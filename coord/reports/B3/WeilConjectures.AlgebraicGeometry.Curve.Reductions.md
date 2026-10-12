## What changed

Replaced the normalization theorem's `sorry` by a compiled reduction through two named intermediate theorems. The first records finite direct-image transfer; the second records descent across a finite-support cokernel. Added proof-only imports for these modules and the existing finite pushforward constructibility result.

## Proved and sorry left

Closed 1 of 1 holes of the item (a decomposition, not a net proof). The declaration `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite` is now proved from the normalization monomorphism, finite pushforward transfer, and finite-support descent. The new intermediate declarations `AlgebraicGeometry.IsCurve.Assertions.of_finite_pushforward_module` and `AlgebraicGeometry.IsCurve.Assertions.of_finite_support_mono` remain `sorry` (nodes b3-finite-pushforward-module-assertions and b3-finite-support-mono-assertions respectively). There are no sorries left in the item; two are added in new modules, giving net -1. Each is strictly a component of the target argument and has its own DAG node.

## No longer needed

No existing imports of Reductions were removed. In the new helper modules, second reading removed redundant public imports Mathlib.AlgebraicGeometry.Morphisms.Finite and WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs; their signature dependencies are already public through Assertions. The normalization node no longer directly uses lemma-weil-pbc-curve-dense-open-reduction, lemma-weil-pbc-smooth-curve-artin-schreier, or lemma-weil-pbc-smooth-curve-kummer-localization: its source calculation is supplied as the existing hypothesis H. The unit route remains unchanged. No modules are claimed globally pruned. The proof uses `normalization_mono_properties` and the existing finite pushforward constructibility theorem; all other pre-existing imports remain required by the surrounding module declarations.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox helper of_finite_support_mono omitted its prime-annihilation hypothesis, despite relying on it in the proof text. Added hℓ : ℓ • 𝟙 G = 0 and proved it explicitly for the finite direct image in the caller. Empty curves, empty complements and the zero quotient ring require no exceptions.

The available finite_pushforward_assertions uses abelian coefficients converted to ULift ℤ and a CurveCoefficientPair, so its signature does not directly supply the needed arbitrary-Λ implication. The blueprint plan omitted Lean interfaces for the finite pushforward transfer and the dense-open finite-support descent. These are recorded as new split nodes rather than leaving an anonymous partial proof.

## New nodes

`b3-finite-pushforward-module-assertions` is stated in `lean/Sheaf/AlgebraicGeometry/Curve/FinitePushforwardModuleAssertions.lean`.

`b3-finite-support-mono-assertions` is stated in `lean/Sheaf/AlgebraicGeometry/Curve/NormalizationAssertionsTransfer.lean`.


## Second reading by B3

1. **Interfaces: PASS.** Compared Reductions with the repository using diff and the
   delivery declaration parser. All 17 existing declaration signatures, definitions,
   visibility and public imports are unchanged; the diff adds three proof-only imports
   and replaces only the final theorem's proof. No change record is required.
2. **Kernel checks: PASS with the two reported residual holes.** Compiled all three
   modules in import order using lcompile.py. Only the two named helper theorems contain
   sorry, both as whole theorem proofs. No axiom, unsafe, opaque, implemented_by, extern,
   kernel-check bypass or hollow definition is present. A scratch copy with explicit
   #print axioms for the closed theorem and both helpers reports only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected from open dependencies;
   this delivery does not claim an axiom-free normalization theorem.
3. **Residual statements: PASS.** Read both signatures and their mathematical proofs.
   Finite pushforward transfer uses cohomology comparison and finite base change;
   constructibility descends using the epimorphic counit f^* f_* F → F.
   Finite-support descent uses the initial exact sequence and higher isomorphisms;
   the prime-annihilation hypothesis ensures the correct conditional torsion branch.
   Tested empty schemes/fibres/complements, V = X, zero sheaves and Λ/(ℓ) = 0 in the
   arguments; in the last case a prime-annihilated Λ-module is zero. When ℓ equals
   the characteristic but F has invertible torsion, F is zero. If F is p-primary
   with p different from ℓ, F is likewise zero. These are two independent, strictly
   smaller parts of normalization, neither a renamed copy of the item.
   Repeated leanfinder, loogle and grep searches with different queries and searched
   the library and upstream checkout. Existing FinitePushforwardAssertions uses a
   CurveCoefficientPair and ULift Z; DenseOpenPrimeAssertions requires a finite whole
   coefficient ring, reducedness, and the canonical open-extension inclusion.
   UnderlyingAbelianAssertions requires constructibility on both coefficient sides.
   None directly closes the arbitrary-module helper; its coefficient comparison is
   substantial additional work, not a short replacement proof.
   Checked the cited primary sources:
   [0A5D](https://stacks.math.columbia.edu/tag/0A5D),
   [0A3Q](https://stacks.math.columbia.edu/tag/0A3Q), and
   [0GJA](https://stacks.math.columbia.edu/tag/0GJA).
4. **Route and pruning: PASS.** The proof combines the existing normalization
   monomorphism, existing finite-pushforward constructibility, finite transfer and
   finite-support descent. It explicitly proves annihilation by ℓ through the quotient
   and additive functors. The old proof-dependency difference is exactly the three
   nodes listed under No longer needed. No unit statement or realized step in
   dag/units/sk-thm-p1.json is bypassed: smooth calculations are the supplied H.
   Removed two redundant public imports from the new helpers and recompiled the set.
   No existing module is globally pruned. One upper hole closed and two holes added
   remains a decomposition with net -1, not a net proof.
5. **DAG agreement: PASS after repairs.** The normalization proof steps and dependency
   union match the caller. Each residual has its own source, full mathematical proof,
   creation record, blueprint parent, chapter, unit and verbatim Lean signature.
   Expanded their previously underspecified natural-language statements to include
   all hypotheses and cited definition dependencies. Updated normalization's local
   sorry_free field; this records the absence of a local hole, not closure of imported
   axioms. Added independent search records to both new nodes.

Changes in this reading: removed the two redundant public imports; corrected the finite
pushforward docstring's counit notation and separated torsion from constructibility;
made the finite-support low-degree kernel/cokernel argument and the C6 torsion branch
explicit; synchronized both node proof texts; completed node statements and statement
dependencies, added second-reader searches, and updated local sorry-free metadata.
No existing signature or definition changed, and no further hole was closed or added.
