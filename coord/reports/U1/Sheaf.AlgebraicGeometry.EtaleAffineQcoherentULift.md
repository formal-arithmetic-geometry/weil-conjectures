## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etale_affine_qcoherent_ulift` by a
complete Lean proof from the Čech criterion. The affine covering collection is
explicit: affine base, finite index, affine members, and covering sieve.
`EtaleFiniteAffineCechBasis` proves both fibre-product stability and cofinality
from Mathlib. `EtaleAffineTensorCechVanishing` states only the remaining
Čech/Amitsur calculation. The final step uses the already proved general
Ext/right-derived terminal-evaluation comparison, so no K-injective bridge is needed.
All three modules compile cleanly through lcompile.py. No statement or definition
of an existing declaration changed. The blueprint unit has no realized node for
this auxiliary theorem; the existing three-step affine proof is retained.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.Etale.etale_affine_qcoherent_ulift`
(node `lem-sc-etale-affine-qcoherent`). Also proved
`AlgebraicGeometry.Scheme.finiteAffineEtaleCechCover_basis`
(node `new-etale-finite-affine-cech-basis`).

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech`
(node `new-etale-affine-tensor-cech-vanishing`). This is the positive Čech
calculation for finite affine covers of arbitrary affine objects, not the
original sheaf-cohomology conclusion. The main theorem combines it with the
proved cover basis, Čech criterion, and cohomology/evaluation comparison.
The new statement includes empty schemes and empty covers and excludes degree
zero deliberately, since degree-zero sections need not vanish.

## No longer needed

Removed from the item's proof imports:
`Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`,
`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`,
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`,
`Sheaf.AlgebraicGeometry.TensorPullback`,
`Sheaf.Paper.EtaleStandardCoverCech`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.RingTheory.FaithfullyFlat.Amitsur`, and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
The section, pullback, standard-cover and Amitsur dependencies remain needed
by the new Čech calculation and have moved to its module/node; descent is
already publicly imported by the tensor-section sheaf definition.

Actually pruned from this argument:
`prop-weil-pbc-kinjective-resolutions-exist` / `KInjectiveResolutionsExist`;
`def-weil-pbc-etale-cohomology` / `Derived.LowerShriek`;
and the explicit use of `def-weil-pbc-global-sections-functor`.
The proved `new-sheaf-cohomology-derived-evaluation` handles Mathlib's `Sheaf.H`
directly. No claim that these modules become globally unreachable is made.
The affine fibre-product and refinement project lemmas are replaced by Mathlib
in the proved basis node. The fibre-product lemma is still a dependency of the
remaining Čech calculation; the refinement project lemma is pruned.

Additional pruning audit of the original `proof_deps`:
`lem-weil-pbc-etale-covering-affine-refinement` is no longer used, since the basis
proof uses Mathlib `QuasiCompactCover.exists_hom` directly.
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-quasi-coherent`, `lem-sc-etale-qcoherent-descent`,
`def-weil-pbc-etale-site`, `lem-sc-etale-standard-cover-cech`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-pc-module-pullback-identity-composition`, `def-sc-etale-qcoherent-module` and
`lem-pc-cech-exact` remain in statements or the split Čech calculation.
`lem-weil-pbc-cech-vanishing-criterion` is used directly.

## Where the brief, the DAG or earlier work was wrong

The original final step was formulated for K-injective/derived-category
cohomology, but the Lean conclusion is Mathlib's Ext-based `Sheaf.H`. The
proved generic comparison supplies exactly the required bridge. No false
statement or target change was found.

Searches: LeanFinder for affine quasi-coherent acyclicity found only unrelated
cotangent cohomology. Loogle `AddCommGrpCat.uliftFunctor` found preservation of
limits and colimits, but no cohomology transport theorem. For the basis,
Loogle located `QuasiCompactCover.exists_hom`; local source searches located
`Scheme.isAffine_of_isLimit`, which was used to prove intersection affineness.
For the Čech calculation, LeanFinder found general exactness and Mayer–Vietoris
lemmas, but no tensor-section comparison; the library has the intended Amitsur
exactness theorem. LeanSearch was attempted for both new nodes and returned
Internal Server Error. Those failures are recorded without an absence verdict.

## New nodes

`new-etale-finite-affine-cech-basis` packages the first geometric step of the
existing proof. Its theorem is fully proved from Mathlib, including the
finite-cover refinement and the over-category product/limit argument.

`new-etale-affine-tensor-cech-vanishing` packages the second step of the existing
proof. It retains the standard-cover, pullback-section, pullback-coherence and
Amitsur dependencies, with a complete proof in words including the lift.
It is strictly the Čech part of the argument and has no derived-cohomology
conclusion. No change records are necessary.

## Second reading by U1

1. Compared every delivered module with the read-only repository. The sole existing
   module differs only in proof imports and the theorem body: the original declaration
   signature and docstring are byte-for-byte unchanged. The two other modules are new.
   The existing DAG node changes only proof, proof_deps and proof_origin. No statement
   or definition change record is required. Verdict: pass.
2. Compiled all three modules in import order through lcompile.py, without errors or
   warnings. Searched the delivered sources: exactly one sorry, in the reported named
   Čech theorem; no forbidden declaration or hollow definition. Scratch-copy
   #print axioms checks show only propext, Classical.choice and Quot.sound for the
   cover definition and basis theorem; the Čech theorem and main theorem additionally
   use sorryAx from open dependencies. This closes the original theorem body, not its
   entire axiom closure. Verdict: pass for a partial stage-3 delivery.
3. Read the split Čech statement, its full docstring and node, and the standard-cover,
   affine-section and Amitsur declarations. It is true for arbitrary X: the calculation
   takes place over affine U with the quasi-coherent pullback of F. Checked degree one,
   the zero module, the empty affine scheme and empty cover, and a singleton identity
   cover; positive-degree restriction is necessary. The Čech statement is strictly one
   step of the argument, with no sheaf-cohomology conclusion. Independent searches
   used LeanFinder (Cech cohomology faithfully flat affine scheme module tensor exact),
   Loogle (cechComplexFunctor) and grep (Amitsur/tensor/Cech variants), plus local rg.
   They find exactness tools but no existing tensor-section/Mathlib-Čech comparison.
   Closing this calculation requires substantial comparison constructions, rather
   than a short application of an existing theorem. Verdict: retain one named split.
4. Read the main proof top downward: the affine basis, Čech criterion and proved
   Ext/right-derived comparison form the stated three-step reduction. Read
   dag/units/sk-prop-h2.json: realized.statement is empty and realized.steps is [[]];
   no realized unit node is bypassed. Audited all original proof_deps in the pruning
   section. Existing public imports are unchanged; new public imports are required
   by the new signatures (removing the homology import produces Lean's public-visibility
   error, so it was restored). Proof dependencies use plain imports. Verdict: pass.
5. Checked new-node metadata, verbatim Lean signatures and equality of proof_deps
   with the union of uses. Corrected the basis node: its two project-lemma dependencies
   were not used by Lean; the proof is directly from Mathlib, so both uses and
   proof_deps are now empty and proof_origin names the actual Mathlib lemmas. The
   fibre-product project lemma remains in the split calculation; the refinement
   project lemma is pruned. Verdict: pass after repair.

Changes by this reader: repaired the basis DAG dependencies and origin, completed
the original-dependency pruning audit, and expanded the new Čech docstring/node
proof with finite-index reindexing, the over-site equivalence and comparison of
chosen product cones. No Lean proof body or statement changed.
