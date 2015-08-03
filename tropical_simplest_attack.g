# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# [1] Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

# Generates a random matrix A in Mat(ZZ, n), a_ij in [mm, mM].
GenerateRandomMatrix := function(n, mm, mM)
  local i, j, result;
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      Add(result[i],  Random(mm, mM));
    od;
  od;
  return result;
end;


# Generates a random polynomial p in ZZ[x] of degree d, d in [1, D], p_i in [pm, pM].
GenerateRandomPolynomial := function(D, pm, pM)
  local i, d, result;
  d := Random(1, D);
  result := [];
  for i in [0..d] do
    Add(result, Random(pm, pM));
  od;
  return result;
end;


# Returns a \otimes b.
ProductOfTwoScalarMinPlus := function(a, b)
  if IsInfinity(a) or IsInfinity(b) then
    return infinity;
  else 
    return a + b;
  fi;
end;


# Retruns A \otimes b.
ProductOfTwoMatricesMinPlus := function(A, B)
  local i, j, n, result; 
  n := Length(A);
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      Add(result[i], Minimum(List([1..n], k -> ProductOfTwoScalarMinPlus(A[i][k], B[k][j]))));
    od;
  od;
  return result;
end;


# Returns zero matrix of size nxn over min-plus algebra.
ZeroMatrixMinPlus := function(n)
  local i, j, result;
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      Add(result[i], infinity);
    od;
  od;
  return result;
end;


# Returns ident matrix of size nxn over min-plus algebra.
IdentityMatrixMinPlus := function(n)
  local i, j, result;
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      if i = j then 
        Add(result[i], 0);
      else
        Add(result[i], infinity);
      fi;
    od;
  od;
  return result;
end;


# Returns A^n.
PowerOfMatrixMinPlus := function(A, n)
  if n = 0 then
    return IdentityMatrixMinPlus(Length(A));
  elif n = 1 then
    return A;
  else
    return ProductOfTwoMatricesMinPlus(A, PowerOfMatrixMinPlus(A, n - 1));
  fi;
end;


# Returns A + B.
SumOfTwoMatricesMaxPlus := function(A, B)
  local i, j, n, result;
  n := Length(A);
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      Add(result[i], Minimum(A[i][j], B[i][j]));
    od;
  od;
  return result;
end;


# Returns s \otimes A.
ProductOfScalarAndMatrixMinPlus := function(s, A)
  local i, j, n, result;
  n := Length(A);
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      Add(result[i], ProductOfTwoScalarMinPlus(s, A[i][j]));
    od;
  od;
  return result;
end;


# Retruns p(A).
ApplyPolynomialMinPlus := function(p, A)
  local i, result, P;
  result := ZeroMatrixMinPlus(Length(A));
  P := IdentityMatrixMinPlus(Length(A));
  for i in [1..Length(p)] do
    result := SumOfTwoMatricesMaxPlus(result, ProductOfScalarAndMatrixMinPlus(p[i], P));
    P := ProductOfTwoMatricesMinPlus(P, A);
  od;
  return result; 
end;


MinusMatrixFromMatrix := function(A, B)
  local i, j, n, result;
  n := Length(A);
  result := [];
  for i in [1..n] do
    Add(result, []);
    for j in [1..n] do
      if B[i][j] = infinity then
        return fail;
      fi;
      if A[i][j] = infinity then
        Add(result[i], infinity);
      else 
        Add(result[i], A[i][j] - B[i][j]);
      fi;
    od;
  od;
  return result;
end;


AreAllElementsTheSame := function(A)
  local i, j;
  for i in [1..Length(A)] do
    for j in [1..Length(A[i])] do
      if A[i][j] <> A[1][1] then
        return false;
      fi;
    od;
  od;
  return true;
end;


# Applies our attack.
ApplyAttack := function(A, B, u, D)
  local i, j, T;
  for i in [0..D] do
    for j in [0..D] do
      T := MinusMatrixFromMatrix(ProductOfTwoMatricesMinPlus(PowerOfMatrixMinPlus(A, i), PowerOfMatrixMinPlus(B, j)), u);
      Print(T, "\n");
      if AreAllElementsTheSame(T) then
        return [T[1][1], i, j];
      fi;
    od;
  od;
  return fail;
end;


TestAttack := function(n, mm, mM, D, pm, pM)
  local A, B, p1, p2, q1, q2, u, v, KA, KB, KC, attack_result;
  A := GenerateRandomMatrix(n, mm, mM);
  B := GenerateRandomMatrix(n, mm, mM);
  p1 := GenerateRandomPolynomial(D, pm, pM);
  p2 := GenerateRandomPolynomial(D, pm, pM);
  q1 := GenerateRandomPolynomial(D, pm, pM);
  q2 := GenerateRandomPolynomial(D, pm, pM);

  u := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(p1, A), ApplyPolynomialMinPlus(p2, B));
  v := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(q1, A), ApplyPolynomialMinPlus(q2, B));

  KA := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(p1, A), ProductOfTwoMatricesMinPlus(v, ApplyPolynomialMinPlus(p2, B)));
  KB := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(q1, A), ProductOfTwoMatricesMinPlus(u, ApplyPolynomialMinPlus(q2, B)));

  if KA <> KB then
    return fail;
  fi;

  attack_result := ApplyAttack(A, B, u, D);
  if attack_result = fail then
    return false;
  fi;
  KC := ProductOfTwoMatricesMinPlus(ProductOfScalarAndMatrixMinPlus(attack_result[1], PowerOfMatrixMinPlus(A, attack_result[2])), 
      ProductOfTwoMatricesMinPlus(v, PowerOfMatrixMinPlus(B, attack_result[3])));
  if KA <> KB then
    return false;
  fi;
  return true;
end;


TestSuite := function(numberOfTests)
  local st, et, mm, mM, D, pm, pM, n, i, ok, fl;
  mm := -10^10;
  mM := 10^10;
  D := 10;
  pm := -1000;
  pM := 1000;
  n := 10;
  st := Runtime();
  ok := 0;
  fl := 0;
  for i in [1..numberOfTests] do
    if TestAttack(n, mm, mM, D, pm, pM) then
      Print("OK\n");
      ok := ok + 1;
    else
      Print("FAIL\n");
      fl := fl + 1;
    fi;
  od;
  et := Runtime();
  Print(et - st, "\n");
  Print("OK: ", ok, "\n");
  Print("FAIL: ", fl, "\n");
end;
