# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf.
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

Read("tropical_algebra.g");

# Returns true if A = (c).
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


# Applies our simplest attack.
ApplyAttack := function(A, B, u, D, pm)
  local i, j, T;
  for i in [0..D] do
    for j in [0..D] do
      T := MinusMatrixFromMatrix(ProductOfTwoMatricesMinPlus(PowerOfMatrixMinPlus(A, i), PowerOfMatrixMinPlus(B, j)), u);
      if AreAllElementsTheSame(T) then
        return [[[i, -T[1][1]]], [[j, 0]]];
      fi;
    od;
  od;
  return fail;
end;
