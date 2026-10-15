## What changed

`exists_constructible_finiteCoefficient_model` now unpacks its constructibility witness and
combines two actual parts of its original proof: finite coefficient descent on each locally
finitely presented stratum, followed by assembly of the supplied stratum models. Every existing
signature and definition is unchanged, byte for byte. The new statements have separate modules,
`Sheaf.Paper.CondensedLfpCoefficientModel` and `Sheaf.Paper.CondensedStratumModelAssembly`, each
with its own DAG node, source, and complete natural-language proof. Their inputs use the actual
inverse-image coefficient rings and the image of the coefficient inclusion, so the target proof
needs no unproved coefficient-identification cast.

Removed the undelivered `exists_constructible_finiteCoefficient_model_of_nonzero`, its node,
and its change record. Its extra nonzero hypothesis removed only the trivial case while leaving
the whole seven-step proof, so it was not a substantive reduction. The valid zero-model proof
was redundant for the uniform stratification reduction and was removed with that case split.

The target's unused public `MorphismDefs` import is removed. Its three statement imports remain
public; the two helpers and the helpers' planned proof inputs are plain imports. The change record
is `coord/changes/condensedFiniteCoefficientDescentReduction.md`.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.ProEtale.exists_constructible_finiteCoefficient_model`.

Added exactly two public named theorem holes:

- `AlgebraicGeometry.ProEtale.exists_lfp_finiteCoefficient_model_on_immersion`
  (`lem-weil-pbc-condensed-lfp-coefficient-model`): the locally finitely presented case,
  corresponding to source-plan steps 1--3, with no stratified extension-class argument.
- `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_model_of_stratum_models`
  (`lem-weil-pbc-condensed-stratum-model-assembly`): assembly supplied with actual finite-field
  models on all strata, corresponding to steps 4--7; it does not descend presentation matrices.

This is a **decomposition**, not a completed proof of finite coefficient descent. The delivery
closes one baseline hole and adds two: net holes closed minus added is **-1**. The submitted
nonzero restatement was not on the repository baseline and is not counted as another hole closed.
There are no hollow definitions, definitions choosing arbitrary witnesses from unproved existence
theorems, or other added holes. No target is claimed axiom-complete: the target still uses
`sorryAx` through the two explicitly named obligations.

## No longer needed

No module is claimed pruned from the targets' import closure. The following old imports are no
longer direct imports of the target; the relevant proof inputs are relocated to the two helper
modules (some are available transitively):

- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
- `Sheaf.Paper.CondensedSheafExtContinuity`
- `Sheaf.Paper.ProfinitePointPullback`

The unused public import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` is also removed.

Every former direct `proof_deps` edge is replaced by the two intermediate nodes. Here is the complete disposition of the old edges:

- `def-constructible-stratification`: retained by assembly node.
- `def-weil-closed-immersion`: retained by local-model node and assembly node.
- `def-weil-finite-subextension-directed-set`: retained by local-model node and assembly node.
- `def-weil-pbc-condensed-e-module-category`: retained by local-model node and assembly node.
- `def-weil-pbc-proetale-covering`: retained by local-model node and assembly node.
- `def-weil-pbc-scheme-conventions`: retained by local-model node.
- `def-weil-proetale-inverse-image`: retained by assembly node.
- `lem-pur-sheaf-hom-cover-gluing`: retained by local-model node.
- `lem-sc-noetherian-finite-irreducible-components`: retained by assembly node.
- `lem-weil-pbc-closed-subset-closed-subscheme`: retained by assembly node.
- `lem-weil-pbc-condensed-constructible-serre`: retained by assembly node.
- `lem-weil-pbc-condensed-flat-coefficient-calculus`: replaced by earlier Compatibility.lean exactness/colimit declarations and generic derived-adjunction inputs; the present flat-calculus module would create an import cycle.
- `lem-weil-pbc-condensed-sheaf-ext-continuity`: retained by assembly node.
- `lem-weil-pbc-ext-one-extension-classification`: retained by assembly node.
- `lem-weil-pbc-proetale-qcqs-fp-section-calculus`: retained by local-model node.
- `lem-weil-pbc-proetale-ringed-open-closed`: retained by assembly node.
- `lem-weil-pbc-profinite-point-pullback`: retained by local-model node and assembly node.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`: retained by local-model node.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`: retained by local-model node.
- `lem-weil-pbc-site-module-sheaf-gluing`: retained by local-model node.
- `lem-weil-proetale-weakly-etale-localization`: retained by local-model node.

## Where the brief, the DAG or earlier work was wrong

The first report overstated the significance of its nonzero split and described removed direct
imports as if obligations had been pruned. The nonzero hole retained the entire hard argument.
The replacement gives the original seven steps two distinct interfaces and keeps the dependency
plans beneath them. No mathematical statement in the repository was corrected or weakened.

The old plan's `CondensedFlatCoefficientCalculus` dependency cannot be imported here: it imports
`CondensedCoefficientComparisons`, which imports `TwoColimit`, which imports this item. The new
assembly plan instead uses the earlier `Compatibility.lean` exactness instances and coefficient
colimit, `Mod.extendRestrictAdjunction`, and generic exact-functor derived-adjunction results.
Those earlier exactness declarations still contain upstream sorries; this delivery claims no
independent proof of flatness. The archive path named by the old source record is not present on
this machine; the seven-step proof in the repository's original module and its DAG node, together
with the mirrored upstream `TwoColimit.lean` module docstring, were the source material read.

The unchanged direct downstream module `TwoColimit` timed out at 60 seconds both against the
baseline and against the sandbox overlay, without a Lean error. No downstream adaptation was
made. This does not affect the clean single-file compiles of the three delivered modules.

## New nodes

`lem-weil-pbc-condensed-lfp-coefficient-model` isolates the finite-matrix, transition-map,
and ringed-site gluing argument on one immersed stratum. An immersion into a topologically
noetherian scheme has noetherian underlying space; no noetherian-ring hypothesis or noetherianity
of a covering object is imposed. The model is locally finitely presented and no constructible
extension gluing is hidden in this conclusion.

`lem-weil-pbc-condensed-stratum-model-assembly` takes finite coefficient models on each stratum
as hypotheses, allowing different fields and a larger final field for extension classes. It
contains only the support induction and open-closed extension descent. The proof explicitly
handles a surjective closed immersion onto the selected open, without assuming that the open
factors through the original stratum. It does not cite the local-model lemma or the parent
statement, preventing a circular reduction.

Fresh LeanFinder, Loogle, and Mathlib grep searches found no matching descent/assembly theorem.
Loogle's `SheafOfModules.IsFinitePresentation` hits provide the local presentation predicate,
not coefficient descent. LeanSearch returned Internal Server Error on both fresh queries and
is recorded as unavailable, with no verdict invented. Searches of `lean/Sheaf`, the current
upstream roots, and the read-only slopmaster2 source found no duplicate. The current `TwoColimit`
object-surjectivity proof calls this item and hence cannot be used to prove it.

## Second reading by B3

1. **Visible statements:** compared the full sandbox diff with the read-only repository. The
   sole existing declaration's signature and its source/proof docstring are unchanged byte for
   byte. No existing definition is touched. The only existing public-interface change is removal
   of the unused `MorphismDefs` re-export; its downstream users and the two new declarations are
   recorded in `coord/changes/condensedFiniteCoefficientDescentReduction.md`. No module held by
   another group is edited.
2. **Proof and axioms:** compiled each of the three modules in import order using `lcompile.py`.
   The target proof supplies `hS a` to the local-model theorem and supplies exactly those resulting
   existential models to the assembly theorem. The only `sorry` tokens in delivered Lean are the
   whole proofs of the two listed public theorems. Inspected all source for forbidden declarations
   and hollow data. Scratch `#print axioms` checks and the delivery probe verify that only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` occur.
3. **Split statements:** rejected the nonzero restatement. The two replacements are distinct
   parts of the seven-step source argument; neither alone restates the parent. Checked zero
   modules, rank-zero presentations, empty strata, and an empty stratification (which forces the
   base to be empty), and checked the one-stratum identity case. Local descent permits torsion
   and arbitrary locally finitely presented modules. Assembly assumes actual locally finitely
   presented models, allows varying fields, and allows a further finite field for the extension
   classes. Neither statement asserts that arbitrary extension classes already descend to the
   original stratum fields. The nonreduced-stratum case uses the empty-complement equivalence,
   not an invalid scheme factorization. Both nodes have complete proofs and fresh search records.
4. **Top-down route and imports:** the revised target combines local descent with assembly
   rather than forwarding the difficult branch unchanged. Every old dependency is accounted for
   above; no closure pruning is claimed. Planned proof dependencies of the two remaining holes
   are retained as plain imports where needed. `dag/units/sk-thm-properbasechange.json` was read:
   its realized statement and three steps are not bypassed, and no realized unit node is removed.
5. **DAG agreement:** the parent now has exactly the two intermediate proof dependencies used
   by its Lean proof. Each new node has verbatim Lean statement, source, stepwise uses with their
   exact union in `proof_deps`, searches, provenance, origin, and the parent's chapter and unit.
   The local node realizes old steps 1--3; assembly realizes steps 4--7 using existing earlier
   flatness/colimit infrastructure instead of a circular imported dependency.

Second-reading changes: replaced the nonzero restatement and zero/nonzero wrapper with the
stratification reduction and its two substantive obligations; removed an unused public import;
replaced circular flat-calculus dependency planning; corrected both DAG metadata and the report's
progress/pruning claims. No remaining obligation could be closed by a short application of an
existing declaration: local descent requires the covering and matrix constructions, while
assembly requires noetherian induction and extension-class descent.
