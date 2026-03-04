#!/usr/bin/env wolframscript

(* Test script for symbolic dimension support in IntU *)
(* Run with: wolframscript -file test_symbolic_dim.wls *)
(* Or from Mathematica: << "test_symbolic_dim.wls" *)

Print["Loading IntU package..."];
Get[FileNameJoin[{DirectoryName[$InputFileName], "IntU.m"}]];

passed = 0;
failed = 0;

TestEqual[name_, actual_, expected_] := (
    result = FullSimplify[actual - expected];
    If[result === 0,
        Print["  PASS: ", name];
        passed++,
    (*else*)
        Print["  FAIL: ", name];
        Print["    Expected: ", expected];
        Print["    Got:      ", actual];
        Print["    Diff:     ", result];
        failed++
    ]
);


(* ===== Test 1: SchurPolynomialAt1 consistency ===== *)
Print["\n=== SchurPolynomialAt1 Tests ==="];

(* Verify for concrete dimensions that hook-content formula matches *)
TestEqual["SchurPoly {2,1} at d=3",
    SchurPolynomialAt1[{2, 1}, 3], 8];
TestEqual["SchurPoly {1} at d=5",
    SchurPolynomialAt1[{1}, 5], 5];
TestEqual["SchurPoly {2} at d=4",
    SchurPolynomialAt1[{2}, 4], 10];
TestEqual["SchurPoly {1,1} at d=4",
    SchurPolynomialAt1[{1, 1}, 4], 6];

(* Symbolic dimension *)
TestEqual["SchurPoly {1} at symbolic d",
    SchurPolynomialAt1[{1}, d], d];
TestEqual["SchurPoly {2} at symbolic d",
    SchurPolynomialAt1[{2}, d], d (d + 1) / 2];
TestEqual["SchurPoly {1,1} at symbolic d",
    SchurPolynomialAt1[{1, 1}, d], d (d - 1) / 2];


(* ===== Test 2: Symbolic Weingarten function ===== *)
Print["\n=== Weingarten Tests ==="];

(* Wg({1}, d) = 1/d *)
TestEqual["Wg[{1}, d] = 1/d",
    Weingarten[{1}, d], 1/d];

(* Wg({1,1}, d) = 1/(d^2 - 1) *)
TestEqual["Wg[{1,1}, d] = 1/(d^2-1)",
    Weingarten[{1, 1}, d], 1/(d^2 - 1)];

(* Wg({2}, d) = -1/(d(d^2-1)) *)
TestEqual["Wg[{2}, d] = -1/(d(d^2-1))",
    Weingarten[{2}, d], -1/(d (d^2 - 1))];

(* Verify symbolic matches numeric at specific d *)
TestEqual["Wg[{2,1}, d] at d=3 matches Wg[{2,1}, 3]",
    FullSimplify[Weingarten[{2, 1}, d] /. d -> 3],
    Weingarten[{2, 1}, 3]];

TestEqual["Wg[{1,1,1}, d] at d=4 matches Wg[{1,1,1}, 4]",
    FullSimplify[Weingarten[{1, 1, 1}, d] /. d -> 4],
    Weingarten[{1, 1, 1}, 4]];

(* Integer-only Weingarten still works *)
TestEqual["Wg[{1}, 3] = 1/3 (integer path)",
    Weingarten[{1}, 3], 1/3];
TestEqual["Wg[{1,1}, 2] (integer path)",
    Weingarten[{1, 1}, 2], 1/3];


(* ===== Test 3: Full symbolic integration ===== *)
Print["\n=== Full Integration Tests ==="];

(* int |U_11|^2 dU = 1/d *)
result1 = IntegrateUnitaryHaar[
    Subscript[u, 1, 1] Conjugate[Subscript[u, 1, 1]],
    {u, d}
];
TestEqual["int |U_11|^2 dU = 1/d",
    result1, 1/d];

(* int |U_11|^2 |U_12|^2 dU *)
(* Known result: -1/(d^2(d^2-1)) + 1/(d(d^2-1)) = 1/(d^2(d+1)) ?? *)
(* Actually for n=2: sum of delta*Wg terms *)
(* We just verify it gives a rational function of d *)
result2 = IntegrateUnitaryHaar[
    Subscript[u, 1, 1] Conjugate[Subscript[u, 1, 1]] *
    Subscript[u, 1, 2] Conjugate[Subscript[u, 1, 2]],
    {u, d}
];
TestEqual["int |U_11|^2 |U_12|^2 dU at d=3",
    FullSimplify[result2 /. d -> 3],
    IntegrateUnitaryHaar[
        Subscript[v, 1, 1] Conjugate[Subscript[v, 1, 1]] *
        Subscript[v, 1, 2] Conjugate[Subscript[v, 1, 2]],
        {v, 3}
    ]
];


(* ===== Test 4: Numeric regression ===== *)
Print["\n=== Numeric Regression Tests ==="];

TestEqual["int |U_11|^2 dU(3) = 1/3",
    IntegrateUnitaryHaar[
        Subscript[u, 1, 1] Conjugate[Subscript[u, 1, 1]],
        {u, 3}],
    1/3];

TestEqual["int |U_11|^2 dU(5) = 1/5",
    IntegrateUnitaryHaar[
        Subscript[u, 1, 1] Conjugate[Subscript[u, 1, 1]],
        {u, 5}],
    1/5];

TestEqual["int |U_11|^2 |U_22|^2 dU(2)",
    IntegrateUnitaryHaar[
        Subscript[u, 1, 1] Conjugate[Subscript[u, 1, 1]] *
        Subscript[u, 2, 2] Conjugate[Subscript[u, 2, 2]],
        {u, 2}],
    1/3];


(* ===== Summary ===== *)
Print["\n=== Results ==="];
Print["Passed: ", passed];
Print["Failed: ", failed];
If[failed > 0,
    Print["SOME TESTS FAILED!"];
    Exit[1],
(*else*)
    Print["ALL TESTS PASSED!"];
    Exit[0]
];
