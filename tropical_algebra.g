# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf.
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

# Generates a random matrix A in Mat(ZZ, n), a_ij in [mm, mM].
GenerateRandomMatrix := function(n, mm, mM)
  return List([1..n], i -> List([1..n], j -> Random(mm, mM)));
end;


# Generates a random polynomial p in ZZ[x] of degree d, d in [1, D], p_i in [pm, pM].
GenerateRandomPolynomial := function(D, pm, pM)
  return List([0..Random(1, D)], i -> [i, Random(pm, pM)]);
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
  return List([1..n], i -> List([1..n], j -> infinity));
end;


# Returns ident matrix of size nxn over min-plus algebra.
IdentityMatrixMinPlus := function(n)
  return List([1..n], i -> List([1..n], function(j) 
      if i = j then 
        return 0; 
      else 
        return infinity; 
      fi;
    end));
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
  return ListN(A, B, function(a, b) return ListN(a, b, function(x, y) return Minimum(x, y); end); end);
end;


# Returns s \otimes A.
ProductOfScalarAndMatrixMinPlus := function(s, A)
  return List(A, a -> List(a, x -> ProductOfTwoScalarMinPlus(s, x)));
end;


# Retruns p(A).
ApplyPolynomialMinPlus := function(p, A)
  if Length(p) = 0 then
    return ZeroMatrixMinPlus(Length(A));
  fi;
  return Iterated(List(p, c -> ProductOfScalarAndMatrixMinPlus(c[2], PowerOfMatrixMinPlus(A, c[1]))), SumOfTwoMatricesMaxPlus);
end;


# Returns A - B. Some elements of the matrices can be infinity.
MinusMatrixFromMatrix := function(A, B)
  return ListN(A, B, function(a, b) return ListN(a, b, function (x, y)
      if y = infinity then
        return fail;
      elif x = infinity then
        return infinity;
      else  
        return x - y;
      fi;
  end); end);
end;
