# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf.
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

Read("tropical_algebra.g");

# Returns minimum of a matrix A and the set of corresponding indexes.
GetMinimumOfMatrix := function(A)
  local i, j, best;
  best := rec(val := A[1][1], inds := []);
  for i in [1..Length(A)] do
    for j in [1..Length(A[i])] do
      if A[i][j] < best.val then
        best := rec(val := A[i][j], inds := [[i, j]]);
      elif A[i][j] = best.val then
        AddSet(best.inds, [i, j]);
      fi;
    od;
  od;
  return best;
end;


# Retruns the simpex-table constructed by a set of covers and a fixed cover.
MakeSimplexMatrix := function(F, D, h)
  local A, i, j, S;
  A := NullMat((D + 1)^2 + 1, 2 * (D + 1) + (D + 1)^2 + 1);
  for i in [0..D] do
    for j in [0..D] do
      A[i * (D + 1) + j + 1][i + 1] := 1;
      A[i * (D + 1) + j + 1][(D + 1) + j + 1] := 1;
    od;
  od;
  for S in F do
    A[S.ijminval[1].i * (D + 1) + S.ijminval[1].j + 1][2 * (D + 1) + (D + 1)^2 + 1] := -S.ijminval[1].val;
  od;
  for i in [1..(D + 1)^2] do
    A[i][2 * (D + 1) + i] := -1;
  od;
  for S in h do
    A[S[1] * (D + 1) + S[2] + 1][2 * (D + 1) + S[1] * (D + 1) + S[2] + 1] := 0;
  od;
  for i in [1..Length(A[1])] do  
    S := 0;
    for j in [1..Length(A) - 1] do
      S := S + A[j][i];
    od;
    A[(D + 1)^2 + 1][i] := -S;
  od;
  return A;
end;


# Retruns index of pivot column.
FindPivotColumn := function(M)
  local i, best, best_i, t;
  best := 0;
  best_i := fail;
  for i in [1..Length(M[1]) - 1] do
    t := M[Length(M)][i];
    if t < best then
      best := t;
      best_i := i;
    fi;
  od;
  return best_i;
end;


# Retruns index of pivot row.
FindPivotRow := function(M, l)
  local i, a, b, best_i, best;
  best_i := fail;
  best := infinity;
  for i in [1..Length(M) - 1] do  
    a := M[i][l];
    b := M[i][Length(M[i])];
    if a > 0 and b / a < best then
      best_i := i;
      best := b / a;
    fi;
  od;
  return best_i;
end;


# Performs recalculation of a simplex-table. Changes M, Bs and Ns.
Recalc := function(M, k, l, Bs, Ns)
  local t, i, j;
  t := Ns[l];
  Ns[l] := Bs[k];
  Bs[k] := t;

  for i in [1..Length(M)] do
    for j in [1..Length(M[1])] do 
      if i <> k and j <> l then
        M[i][j] := M[i][j] - M[i][l] * M[k][j] / M[k][l];
      fi;
    od;
  od;

  for i in [1..Length(M)] do
    if i <> k then
      M[i][l] := -M[i][l] / M[k][l];
    fi;
  od;

  for i in [1..Length(M[1])] do
    if i <> l then
      M[k][i] := M[k][i] / M[k][l];
    fi;
  od;

  M[k][l] := 1/M[k][l];
end;


# Returns the solution constructed by a simplex-table.
WriteDownSolution := function(M, Bs)
  local i, result;
  result := List([1..Length(Bs)], i -> 0);
  for i in [1..Length(Bs)] do
    result[Bs[i]] := M[i][Length(M[1])];
  od;
  return result;
end; 


# Applies the simplex-method to a matrix M and returns the corresponding solution.
# If there is no solution, then returns fail.
ApplySimplex := function(M)
  local k, l, Bs, Ns;
  Bs := [Length(M[1]) - 1 + 1..Length(M[1]) - 1 + Length(M) - 1];
  Ns := [1..Length(M[1]) - 1];
  while true do
    l := FindPivotColumn(M);
    if l = fail then
      break;
    fi;
    k := FindPivotRow(M, l);
    if k = fail then
      return fail;
    fi;
    Recalc(M, k, l, Bs, Ns);
  od;
  if M[Length(M)][Length(M[1])] <> 0 then
    return fail;
  fi;
  return WriteDownSolution(M, Bs);
end;


# Returns the number of i-th indexes. 
NumberOfIndexes := function(S, i)
  return Length(Set(List(S, c -> c[i])));
end;


# Compresses a set of pair [a1, L1], [a2, L2], ..., [an, Ln] to the set of pair, where all first components are unique.
Rar := function(G)
  local Find, H, i, S;

  Find := function(H, S)
    for i in [1..Length(H)] do
      if S.inds = H[i].inds then
        return i;
      fi;
    od;
    return fail;
  end;

  H := [];
  for S in G do
    i := Find(H, S);
    if i = fail then
      Add(H, S);
    else 
      Append(H[i].ijminval, S.ijminval);
    fi;
  od;
  return H;
end;


# Returns the compressed set of covers. This set contains all the minimal covers.
GetCompressedCovers := function(F)
  local M, N, P, Z;
  if Length(F) = 0 then
    return [[]];
  fi;
  Z := Rar(F);
  M := Filtered(Z, S -> Length(Difference(S.inds, Union(List(Filtered(Z, T -> S <> T), T -> T.inds)))) <> 0);
  N := Union(List(M, S -> S.inds));
  P := Rar(List(Filtered(List(Z, S -> rec(ijminval := S.ijminval, inds := Difference(S.inds, N))), 
      S -> Length(S.inds) <> 0)));
  if Length(P) > 0 then
    Sort(P, function(S, T) return Length(S.inds) > Length(T.inds); end);
    return List(Concatenation(List(GetCompressedCovers(
        Filtered(List(P, S -> rec(ijminval := S.ijminval, inds := Difference(S.inds, P[1].inds))), S -> Length(S.inds) <> 0)),
        S -> Concatenation([P[1]], S)),
        GetCompressedCovers(P{[2..Length(P)]})), S -> Concatenation(M, S));
  fi; 
  return [M];
end;


# Applies our attack.
ApplyAttack := function(A, B, u, D, pm)
  local Repack, F, G, H, S, T;

  Repack := function(ij, min)
    return rec(ijminval := [rec(i := ij[1], j := ij[2], val := min.val)], inds := min.inds);
  end;

  F := Filtered(List(
      Cartesian([0..D], [0..D]), 
      ij -> Repack(ij, GetMinimumOfMatrix(MinusMatrixFromMatrix(
              ProductOfTwoMatricesMinPlus(PowerOfMatrixMinPlus(A, ij[1]), PowerOfMatrixMinPlus(B, ij[2])), 
              ProductOfScalarAndMatrixMinPlus(-2 * pm, u))))), S -> S.ijminval[1].val <= 0);
  G := GetCompressedCovers(F);
  H := Union(List(G, S -> Cartesian(List(S, T -> List(T.ijminval, c -> [c.i, c.j])))));
  Sort(H, function(a, b) 
      return Length(a) < Length(b) or (Length(a) = Length(b) and 
          NumberOfIndexes(a, 1) * NumberOfIndexes(a, 2) < NumberOfIndexes(b, 1) * NumberOfIndexes(b, 2)); end);

  for S in H do
    T := ApplySimplex(MakeSimplexMatrix(F, D, S));
    if T <> fail then
      return [List([0..D], i -> [i, T[i + 1] + pm]), List([0..D], i -> [i, T[D + 1 + i + 1] + pm])];
    fi;
  od;
  return fail;
end;
