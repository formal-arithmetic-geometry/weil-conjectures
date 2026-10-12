## What changed

Proved `AlgebraicGeometry.isIso_rightDerivedFunctor_lowerTruncation_step` in
`Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization`, with its signature unchanged.
Added the proved private helper `AlgebraicGeometry.isZero_rightDerived_shifted_single`, which
transports ordinary derived-functor vanishing through the single-object, RF shift, and homology
shift comparisons. The main proof applies the lower-truncation triangle, proves both endpoint
vanishings, and uses Mathlib's homology-sequence criteria for monicity and epicity.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`, and
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
Updated the item's node proof, proof dependencies, and proof origin to match the actual route.
The unit record has no realized statement or steps that this route bypasses.

## Proved and sorry left

Proved the item's only sorry:
`AlgebraicGeometry.isIso_rightDerivedFunctor_lowerTruncation_step`
(node `lem-pc-derived-functor-truncation-stabilization`).
The private helper is also fully proved. No sorry remains in this module, and none is added.
The imported `DerivedCategory.exists_lowerTruncationStepTriangle`
(node `lem-pc-derived-lower-truncation-step-triangle`) still has its existing sorry;
this delivery reduces the item to that planned dependency.

Local compilation passed without warnings. The argument includes the boundary `n=N-i`,
`N=0`, and negative integer n: both derived indices are nonnegative because n+j>=N,
and the toNat casts are justified explicitly. The prescribed dry run provides local and
server compilation, axiom probing, and delivery preflight; its result is reported at handoff.

## No longer needed

Removed the direct proof imports
`Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
The former's node `lem-sp-shift-identification` and its three sorry-bearing declarations
are not needed by this proof. The latter remains a transitive, already-proved ingredient of
PlusCompatibility, but its bounded-below triangulated instances are not used here.

Removed `lem-weil-pbc-derived-direct-image-triangulated` from this item's proof dependencies:
the proof uses `lem-pc-right-derived-functor-triangulated` instead, so there is no need to
lift the triangle into the bounded-below category. Retained the lower-truncation triangle
and long exact cohomology dependencies. Used the existing closed single identification
and Mathlib cohomology shift nodes directly. No global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned import `ShiftIdentification` states its comparisons with an extra
`PreservesFiniteLimits F` hypothesis; the item and Stacks Tag 08D4 require only additive F.
The source library's `homologyRightDerivedFunctorObjSingleFunctorIso` and the unbounded
RF triangulated instances require only additivity and the resolution assumptions already
present here, so they supply the needed comparisons without changing the statement.
`HasInjectiveResolutions C` is not automatically an `EnoughInjectives C` instance:
the private helper installs the source library's proved
`enoughInjectives_of_hasInjectiveResolutions` locally.

The cited Stacks .tex file is absent on this machine; the source argument was checked at
https://stacks.math.columbia.edu/tag/08D4, proof of (2). Its product-commutation hypothesis is
used for the inverse-limit argument, which is outside this stabilization lemma.

## Second reading by G1

1. PASS: compared the sole delivered Lean module with the repository version, including
   the existing declaration's signature byte for byte. The signature and all public
   imports are unchanged; there is no definition change and no change record is needed.
   The node differs only in `proof`, `proof_deps`, and `proof_origin`.
2. PASS: compiled the complete module locally with no errors or warnings. Inspected all
   bodies: no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   is introduced. A scratch copy with explicit `#print axioms` shows only propext,
   Classical.choice, and Quot.sound for the private helper. The main theorem also uses
   sorryAx through the existing, explicitly reported lower-truncation triangle. Thus
   this closes one local hole, rather than certifying the theorem's entire dependency
   closure as axiom-free.
3. PASS: no statement is split off and no new hole or DAG node is added. The private
   proved helper is a genuine comparison of shifted single-object cohomology with
   ordinary right derived functors. Read PlusCompatibility, the triangulated instances,
   and the Mathlib homology-sequence criteria. Checked n+i=N, N=0, and negative n:
   n+i and n+i+1 remain nonnegative, so toNat loses no information. The mono criterion
   uses the zero source in degree i; the epi criterion uses the zero target in degree
   i+1. Checked the source argument at https://stacks.math.columbia.edu/tag/08D4.
4. PASS: searched the library and Mathlib with truncGE/isIso and rightDerived/shift/trunc
   queries; found no shorter applicable stabilization declaration. The existing shift
   identification requires an unavailable finite-limits hypothesis. Each proof-only
   import supplies a needed declaration or instance; public imports support the unchanged
   signature. No longer needed lists both removed old proof dependencies and imports.
   The unit sk-thm-picard-duality has empty realized statement and step arrays, so this
   reduction bypasses no recorded realized step. The planned triangle and exact-sequence
   argument are retained.
5. PASS: read each dependency's Lean or Mathlib record and checked that the node's proof
   steps and their dependency union match the actual proof. The comparison uses the
   recorded PlusSingle result through the proved PlusCompatibility comparison. The
   proof origin remains the Stacks argument, with the actual formal route described.

Second reading changed no Lean proof or node: both passed review. Added this review and
clarified here the conditional axiom status and the count: one hole closed, zero holes
added, zero split off; the existing lower-truncation triangle remains open.
