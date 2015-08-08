# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf.
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

Read("tropical_algebra.g");

# Runs our attack.
TestAttack := function(n, mm, mM, D, pm, pM, ApplyAttack)
  local A, B, p1, p2, q1, q2, u, v, KA, KB, KC, attack_result;
  A := GenerateRandomMatrix(n, mm, mM);
  B := GenerateRandomMatrix(n, mm, mM);
  p1 := GenerateRandomPolynomial(D, pm, pM);
  p2 := GenerateRandomPolynomial(D, pm, pM);
  u := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(p1, A), ApplyPolynomialMinPlus(p2, B));
  q1 := GenerateRandomPolynomial(D, pm, pM);
  q2 := GenerateRandomPolynomial(D, pm, pM);
  v := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(q1, A), ApplyPolynomialMinPlus(q2, B));
  KA := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(p1, A), ProductOfTwoMatricesMinPlus(v, ApplyPolynomialMinPlus(p2, B)));
  KB := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(q1, A), ProductOfTwoMatricesMinPlus(u, ApplyPolynomialMinPlus(q2, B)));
  if KA <> KB then
    return false;
  fi;

  attack_result := ApplyAttack(A, B, u, D, pm);
  if attack_result = fail then
    return false;
  fi;
  KC := ProductOfTwoMatricesMinPlus(ApplyPolynomialMinPlus(attack_result[1], A), 
      ProductOfTwoMatricesMinPlus(v, ApplyPolynomialMinPlus(attack_result[2], B)));
  if KA <> KC then
    return false;
  fi;
  return true;
end;


# Runs a set of tests.
TestSuite := function(n, mm, mM, D, pm, pM, ApplyAttack, numberOfTests)
  local st, et, i, ok, fl, maxCovers;
  st := Runtime();
  ok := 0;
  fl := 0;
  for i in [1..numberOfTests] do
    if TestAttack(n, mm, mM, D, pm, pM, ApplyAttack) then
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
