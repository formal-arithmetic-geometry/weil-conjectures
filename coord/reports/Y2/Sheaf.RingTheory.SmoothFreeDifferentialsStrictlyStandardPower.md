## What changed

`Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower` now compiles with a complete
proof from two separate preparation statements and existing library lemmas. The proof
explicitly constructs the stable trivialization of the localized conormal module from
`Algebra.Presentation.localized_conormal_equiv` and the given differential trivialization.
It then obtains a presentation with an initial conormal basis and its localized
Jacobian left inverse. All subsequent denominator clearing is proved here: common
entry denominators, killing the matrix error by a uniform power, the finite maximum of
relation exponents, independence of the polynomial lift, Cauchy–Binet coefficients via
`Matrix.scalar_left_inverse_maximal_minors`, transposed determinants, and the final bounds.

The original `hstable` was parsed incorrectly. Parentheses now make the whole product
of the differential module and the free summand the source of the linear equivalence.
This restores the existing mathematical node and Stacks 07EZ(e). The change record is
`coord/changes/smooth-free-differentials-stable-product.md`. No target statement,
definition, or downstream module changes. Direct importers do not yet call this theorem;
there is consequently no forced adaptation.

Added proof imports: `Sheaf.RingTheory.PresentationLocalizedConormalSplit`,
`Sheaf.RingTheory.SmoothStableConormalBasis`, and
`Sheaf.RingTheory.LocalizedConormalBasisJacobian`. All imports supplying statement
notions stay public; these proof imports are ordinary imports.

## Proved and sorry left

The corrected `Algebra.smooth_free_differentials_strictly_standard_power` has no direct
sorry. This is a decomposition, not a sorry-free proof or a proof of the old misparsed
statement. One direct hole is removed from the corrected item and two lower holes are
added (net -1 before pruning). The private `Algebra.common_denominator` and
`Algebra.clear_matrix_left_inverse` are fully proved, with no additional axioms.

The new remaining holes are exactly:

- `Algebra.exists_presentation_localized_conormal_basis`, in
  `Sheaf.RingTheory.SmoothStableConormalBasis`, node
  `lem-weil-pbc-smooth-stable-conormal-basis`. Its input is an already stably free
  localized conormal module of a given presentation, not the target's differential
  hypothesis. Its output is a basis-bearing presentation; it asserts no power bound,
  Jacobian minor formula, or strictly standard element.
- `Algebra.Presentation.localized_conormal_basis_jacobian`, in
  `Sheaf.RingTheory.LocalizedConormalBasisJacobian`, node
  `lem-weil-pbc-localized-conormal-basis-jacobian`. For any supplied basis-bearing
  presentation it gives localized ideal membership and a localized Jacobian inverse;
  it asserts neither an exponent nor strict standardness. The item supplies those
  missing steps with a real Lean proof.

There are no other sorries in delivered modules. Existing imported holes, including
`Algebra.smooth_localization_conormal_split` and
`Matrix.scalar_left_inverse_maximal_minors`, are not modified.

## No longer needed

The item's direct import `Sheaf.RingTheory.SmoothLocalizationConormalSplit` is removed
and replaced by the tensor-product preparation interfaces. That module and its node
remain needed transitively by the new preparation lemmas; it is not claimed as pruned.
The existing matrix-minors node stays needed and is explicitly applied. The old direct `proof_deps` entries
`def-weil-pbc-mv-polynomial-ring` and `def-weil-pbc-kahler-differentials` are also
removed from the item route: their notions remain in the statement or preparations,
but neither is an independently applied proof lemma. No entire module or node is pruned. All original mathematical preparation steps remain; the
new node files make the two unformalized portions explicit. No UNIT statement or
realized proof step is bypassed (checked `dag/units/sk-thm-p1.json`).

## Where the brief, the DAG or earlier work was wrong

The stage-2 signature's missing parentheses made `hstable` a nonempty product of a
single differential element and an equivalence between two free modules. A compiler
experiment supplies this hypothesis with `s=t=0` for arbitrary algebras. Thus the
original signature does not encode stable freeness and cannot support the Stacks
argument. The mathematical DAG statement was correct and stays unchanged; only its
Lean record changes. The proof now uses the existing presentation-level conormal
complement lemma, which also handles independent universes of R and A, instead of
requiring direct manipulation of the quotient-only split-conormal interface.

The listed local Stacks `.tex` is not present in this read-only clone. I read the official
source at https://stacks.math.columbia.edu/tag/07EZ, particularly the proof of (e), and
compared its stabilization, initial-basis, relation, and left-inverse steps with the DAG.
LeanSearch returned an Internal Server Error; searches are honestly recorded as
unavailable. LeanFinder and Mathlib grep ran successfully. The existing Huber result
`Algebra.Generators.exists_presentation_of_basis_cotangent` concerns a globally free
conormal module and does not give a presentation of A from one free only after
localizing; hence it does not subsume the new stabilization lemma.

Edge cases checked: zero localization uses the empty basis, independently of the rank
q in a supplied stable equivalence; nonzero localization gives c<=n by a residue-field
rank argument. The localized consequence allows c=0 and the empty identity matrix.
The compiled denominator helpers work with empty index sets and zero rings. There is
no cancellation of a, no domain assumption, and localization torsion is killed by an
extra power. For e beyond a bound, only ideal stability and nonnegative subtraction are
used. Changing the chosen lift is handled by an actual kernel-square calculation.

## New nodes

`lem-weil-pbc-smooth-stable-conormal-basis` formalizes just stabilization by zero
variables, lifting a localized conormal basis, and appending relation generators. Its
complete proof and zero-localization/rank treatment are in its docstring and node.
The actual stable conormal equivalence is constructed in the item, rather than left
in this new hole. Its source is the preparation paragraph of Stacks 07EZ(e).

`lem-weil-pbc-localized-conormal-basis-jacobian` formalizes the consequences of that
specified basis: relation membership in the polynomial localization and a Jacobian
matrix left inverse over A_a. Its source is the spanning and split-injection sentences
of Stacks 07EZ(e). It does not package the item or its power conclusion. The existing
split-conormal node is its proof dependency. Both nodes have three kinds of recorded
searches; unavailable LeanSearch is marked unavailable, with successful LeanFinder
and grep alternatives. Blueprint searches for conormal basis, stably free, and split
injection found no matching blueprint nodes. Change record:
`coord/changes/smooth-free-differentials-stable-product.md`.


## Second reading by Y2

1. Compared the entire item module and existing node against the read-only repository.
   The only existing signature edit is the declared parenthesization of `hstable`,
   covered by `coord/changes/smooth-free-differentials-stable-product.md`.
   This corrects a false encoding: the old type admits the zero differential paired
   with the identity equivalence at `s=t=0`. The new type expresses the unchanged DAG
   statement and Stacks 07EZ(e). No target, definition, or other existing declaration
   changes. Re-ran `tools/downstream.py --uses`: 193 import descendants, no external
   use of the declaration. Expanded the change record to list every descendant and
   its local-snapshot holder. Verdict: declared correction, no accidental change.
2. Compiled all three modules in import order using `lcompile.py --all`: no errors or
   warnings. Read every proof and checked the denominator supremum, localization
   torsion, kernel-square lift correction, ordered minors and exponent bounds.
   Explicit `#print axioms` probes check the main theorem and both private helpers,
   and the two new theorems. Only the three permitted axioms and imported `sorryAx`
   occur; the private helpers use no `sorryAx`. The only direct sorries are the two
   reported named public theorems. No forbidden declarations or hollow definitions.
   Existential witnesses are destructed locally inside a theorem proof; no definition
   chooses arbitrary data from an unproved mere-existence theorem. Verdict: valid
   reduction with two named holes, not a complete axiom-free proof.
3. Read both new statements, docstring proofs, and complete nodes. Checked empty
   relation/variable index sets, `c=0`, zero rings/localizations, and the nonzero-ring
   rank bound using a split injection after residue-field base change. The basis
   theorem only prepares a presentation from an already stably free conormal module;
   the Jacobian theorem only extracts two localized consequences from a supplied
   basis. Neither restates the power theorem. Independent LeanFinder query on
   adjoining zero variables and cotangent bases, Loogle query on Extension.Cotangent,
   Mathlib grep for base-changed cotangent injections and left inverses, and searches
   through both library roots found components but no exact replacement. Read
   Mathlib's `exists_presentation_of_basis_cotangent`: it requires a basis globally,
   so it cannot replace preparation from a localized basis. Neither remaining hole
   closes by a short application of the available statements. Verdict: true,
   necessary, strictly smaller, documented split statements.
4. Read the proof from the conclusion downward and independently compared the source
   at https://stacks.math.columbia.edu/tag/07EZ, part (e). The item constructs the
   conormal stable equivalence and actually proves all subsequent denominator, ideal
   and minor calculations. Every proof import has a specific role; public imports
   provide statement notions. The open preparation modules retain their planned
   split-conormal dependency. Checked `dag/units/sk-thm-p1.json` realized statement
   and steps: no realized unit node is bypassed. Expanded No longer needed to name
   all removed direct proof-dependency entries, distinguishing direct pruning from
   modules still needed transitively. Verdict: route retained; no whole-module prune.
5. Checked new-node required fields, source places, search records, blueprint ancestry,
   chapter/unit, signatures, and union of step uses against each `proof_deps`.
   The existing item's six recorded steps agree with the written Lean reduction and
   its corrected `lean.statement`; mathematical statement fields remain unchanged.
   Verdict: DAG agrees with Lean.

Second reading changed the completeness of the change record's Users table and the
report's removed-dependency accounting, and added this independent review. No Lean
proof or statement needed a further repair. One corrected upper hole is decomposed
into two lower holes (net minus one hole closed before pruning); the old malformed
statement is not claimed proved.
