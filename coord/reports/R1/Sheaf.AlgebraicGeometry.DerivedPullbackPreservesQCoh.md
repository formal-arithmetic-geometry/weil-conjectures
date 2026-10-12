## What changed

Completed `AlgebraicGeometry.derivedPullback_cohomology_over_affine` without changing its
signature. The proof restricts E to V, obtains a K-flat affine module model for the
restricted morphism, uses the existing core affine derived equivalence to establish
quasi-coherence of the output tilde complex, commutes exact restriction with homology,
and transports the result through the derived open-restriction comparison and the
over equivalence. All new proof imports in the item's module are ordinary imports.
Its original public import is unchanged.

Added three modules and matching nodes. `DerivedOpenRestrictionQCoh` is fully proved,
including both directions of quasi-coherence transport through `overEquiv`, and an
explicit five-isomorphism homology comparison for exact derived restriction. The other
two modules isolate the affine K-flat input/output model and the restriction comparison
with independent localization universes. Each remaining proof is exactly `by sorry`.
The affine model specifies a K-flat complex P representing E and computes the output
by extension of scalars along the actual ring map f.appTop; it is not the original
quasi-coherence conclusion under a different name.

Updated the original node's proof, proof_deps and proof_origin to follow the Lean.
Read the unit record `sk-thm-picard-f-representable`; its realized statement and step
lists are empty, and no unit or chapter route was changed.

Local file compilation passed for the four-module reduction. The delivery tool also
passed local axiom probes and server compilation; its initial preflight identified
file-level proof settings as an interface change. These settings were moved into the
proof body and the item recompiled; no existing public commands were changed. Searches were made with
the launcher search tool and direct source rg; LeanSearch returned HTTP 500 and is
recorded as unavailable. The mathematical sources read were Stacks Tags 08DW and 06Z0,
including their proofs. Empty opens/zero rings, zero complexes, arbitrary integer
cohomology degrees, unbounded complexes and nonflat ring maps are allowed by the new
statements. The affine model uses no flatness assumption on the ring map: K-flatness
belongs to the input complex.

## Proved and sorry left

Accounting: one existing hole is closed syntactically, and two new named holes are
added. This is a decomposition, not an unconditional proof of the item's theorem.
The new exact-restriction criterion and its private helpers are fully proved. The
item still depends on `sorryAx` through its open dependencies. The authoritative
net progress after import pruning is the maintainer's pinned-baseline sorry ledger;
the count of declarations closed here is not that progress figure.

Proved in the item:
- `AlgebraicGeometry.derivedPullback_cohomology_over_affine`
  (node `lem-pc-derived-pullback-qcoh-component`), from the explicitly named dependencies.

Also proved:
- `AlgebraicGeometry.schemeDerivedQCoh_openRestriction_iff`
  (node `lem-pc-derived-open-restriction-qcoh-iff`), with no new sorry dependencies.
- Its two private helpers `overEquiv_functor_qcoh` and `overEquiv_inverse_qcoh`.

Every sorry left in this delivery:
- `AlgebraicGeometry.exists_affine_derivedPullback_module_model`
  (node `lem-pc-affine-derived-pullback-module-model`). The remaining work is the
  canonical affine-coordinate transport, choice of a K-flat module representative,
  and use of the existing spectrum pullback computation. The complete input/output
  statement and proof in words are in its module and node.
- `AlgebraicGeometry.derivedPullback_openRestriction_iso_universes`
  (node `lem-pc-derived-pullback-open-restriction-universes`). The remaining work is
  transport of the existing same-universe restriction comparison through canonical
  equivalences of localizations and uniqueness of left-derived functors.

There are no sorries left in the item's module. Existing imported declarations, notably
the core affine derived equivalence, remain separate project items.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
The former's affine pullback formula remains required by the affine module-model node.
For the latter, the proof now imports and applies only
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` and
`AlgebraicGeometry.exists_affineQCohDerivedEquivalence_core`.
The stronger full equivalence theorem's normalization on shifted copies of the unit is
not used. Thus this proof does not need node
`new-affine-qcoh-derived-equivalence-shift` or module
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift`, nor the full-interface
module `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
The full theorem's extra direct proof imports `SchemeDerivedDirectImage`,
`UnboundedDerivedFunctorCohomologicalBound` and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech` are also not needed by this
argument; other paths/users may still require them. `QuasicoherentKernel` remains
required for exact restriction along the canonical affine presentation.

The affine model's dependency was narrowed to the existing core equivalence node.
No unit statement or realized unit step is bypassed. The original affine computation
node is still needed by the remaining comparison/model construction; its unused
normalization or tensor clauses are not being deleted from that shared node. These
are pruning claims for this proof's imports and statements, not assertions that other
project targets have no independent uses of these modules.

The affine module model does not require the tensor-product comparisons or their
naturality statements from `AffineDerivedPullbackTensorTilde`; only its affine
pullback comparison is needed. No separate module or node for those tensor clauses
can be removed because they share that existing multi-declaration module/node and
may have other users.

The full import-closure comparison against the original item's module removes the
following 73 project-root modules from this proof's imports. A node label after a module
identifies its existing DAG record, not a proposed deletion. The affine computation
node remains a mathematical dependency of the remaining affine-model/comparison tasks;
its tensor-only clauses and their imports are not used by the present proof. Other
listed modules may likewise remain necessary for independent users or future proofs.

- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` (nodes: `def-pc-base-derived-tensor-cohomology-model`)
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` (nodes: `lem-pc-affine-derived-pullback-tensor-tilde`)
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` (nodes: `lem-pc-affine-qcoh-derived-equivalence`)
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift` (nodes: `new-affine-qcoh-derived-equivalence-shift`)
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure` (nodes: `def-pc-scheme-derived-tensor-structure`)
- `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor` (nodes: `lem-weil-pbc-affine-tilde-tensor`)
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde` (nodes: `lem-pc-affine-tilde-kflat`)
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` (nodes: `def-pc-derived-direct-image`)
- `Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso` (nodes: `lem-pc-scheme-module-free-yoneda-iso`)
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` (nodes: `lem-pc-module-pullback-adjunction`)
- `Sheaf.AlgebraicGeometry.TensorPullbackTilde` (nodes: `lem-weil-pbc-tilde-pullback-base-change`)
- `WeilConjectures.Algebra.Homology.BifunctorLinear`
- `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided`
- `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom`
- `WeilConjectures.Algebra.Homology.InternalHom`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (nodes: `def-sc-invertible-module`, `lem-weil-pbc-invertible-pullback-invertible`)
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` (nodes: `lem-weil-pbc-pushforward-spec-global-sections`)
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` (nodes: `lem-weil-pbc-sheaf-flat-separator`)
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` (nodes: `lem-weil-pbc-sheaf-tensor-closed`)
- `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive`
- `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlus`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`
- `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield`
- `WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive`
- `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.Localization`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus`
- `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration`
- `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Associator`

## Where the brief, the DAG or earlier work was wrong

The original node's single prose step concealed several Lean interfaces. Exact
restriction/cohomology and quasi-coherence transport in the over equivalence are
now proved in the generic restriction module. The existing affine formula is written
only on spectra; using it for arbitrary affine schemes requires the canonical spectrum
presentations and compatibility of derived pullback with those isomorphisms, isolated
in the affine module model.

The existing `derivedPullback_openRestriction_iso` forces the localization universes
of X, Y, U and V to agree. The item's hypotheses supply a possibly arbitrary wD only
on X and Y. `HasDerivedCategory.standard` on U and V supplies the standard universe,
which need not equal wD. The new comparison explicitly permits independent ambient
and open-subscheme universes; the original theorem and its users were not changed.

The supplied local literature paths are absent on this machine, so the proofs of
Tags 08DW and 06Z0 were read from the Stacks website. No new mathematical route was
invented; this is the same affine-local argument as the original node. The category
instances on `Scheme.Modules` and the shared `SheafOfModules` carrier also require
explicit exactness-instance conversion for restriction along the affine presentation.

## New nodes

`lem-pc-derived-open-restriction-qcoh-iff`: fully proved exact-restriction criterion,
in `lean/Sheaf/AlgebraicGeometry/DerivedOpenRestrictionQCoh.lean`. It applies to every
open and every derived object, with independent localization universes. It implements
the original node's passage between cohomology on U and cohomology over U.

`lem-pc-affine-derived-pullback-module-model`: K-flat representative on the canonical
source spectrum and explicit extension-of-scalars output on the canonical target
spectrum, in `lean/Sheaf/AlgebraicGeometry/AffineDerivedPullbackModuleModel.lean`.
Its proof uses the original affine computation and affine derived equivalence, together
with K-flat resolution. It asserts actual representative isomorphisms and K-flatness,
not quasi-coherence of the desired output.

`lem-pc-derived-pullback-open-restriction-universes`: natural restriction comparison
with independent localization universes, in
`lean/Sheaf/AlgebraicGeometry/DerivedPullbackOpenRestrictionUniverses.lean`. This is
needed to use standard derived categories on opens without specializing the item's
ambient universe binder. It is independent of affineness, quasi-coherence and degree.

No change records: no existing definition or statement was changed.

## Second reading by R1

1. Compared every delivered module with the read-only repository. Only
   `DerivedPullbackPreservesQCoh` existed there; the other three are new modules.
   The existing theorem's entire signature is byte-for-byte unchanged, including
   `uX`, arbitrary ambient `wD`, both derived-category instances, `hE`, both
   affine-open hypotheses, `hUV`, and the over-object conclusion in every integer
   degree. The original public import is unchanged. No existing definition or
   statement is changed, and no change record is needed. Verdict: pass.

2. Compiled all four modules in import order through `lcompile.py`, without errors
   or warnings (12.4, 13.8, 5.0 and 25.0 seconds). Read the proof from the restriction
   of `hE` through the affine model, tilde comparison, exact-restriction homology
   isomorphisms and the inverse open comparison. All isomorphisms have the required
   direction. Scratch-copy `#print axioms` checks show only `propext`,
   `Classical.choice` and `Quot.sound` for the exact-restriction criterion and both
   private helpers. The item and each of the two split statements additionally
   show `sorryAx`, as expected; the item is conditional on those open dependencies.
   Exactly the two reported public theorems contain `sorry`, each as its whole
   proof; no definition contains one and no forbidden declaration or attribute is
   present. Verdict: pass as a decomposition, not as an axiom-free finished item.

3. Read Stacks Tags [08DW](https://stacks.math.columbia.edu/tag/08DW),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
   [08DV](https://stacks.math.columbia.edu/tag/08DV), including their proofs.
   The affine module-model statement is the explicit affine computation: its ring
   map is `f.appTop`, its input is a K-flat module complex, and its output is tilde
   of extension of scalars followed by restriction along the canonical spectrum
   presentation. It does not assert quasi-coherence of the desired cohomology.
   The other hole is the restriction comparison for arbitrary schemes and opens,
   with separate ambient/open localization universes; it has no affine or
   quasi-coherence assumption. These are genuine parts of the affine-local
   argument, not renamed copies of the item. Empty opens/zero rings, zero complexes,
   identity maps, arbitrary integer degrees, unbounded objects, and nonflat ring
   maps cause no omitted hypothesis: K-flatness is on the representative, not the
   map. Checked the docstring proofs and corresponding node statements. Repeated
   LeanFinder searches using “left derived inverse image localization equivalence
   independence of chosen derived category” and “complex of modules on affine
   scheme pullback represented by tensor with global sections ring”, plus direct
   `rg` in the project. They found general derived-functor uniqueness ingredients
   and underived pullback, not replacements for either hole. Loogle did not know
   `Functor.mapDerivedCategory`; this failed query was not treated as evidence of
   absence. The existing `derivedPullback_openRestriction_iso` forces all four
   localization universes to agree and therefore is not a direct specialization
   for the item's arbitrary `wD`. Neither hole can be closed by the located
   ingredients in a short proof. Verdict: true, sourced, proper intermediate tasks.

4. Checked the original proof dependencies and the new Lean route. The stronger
   full affine equivalence is replaced by its core theorem; the old affine
   computation remains a mathematical dependency of the new model/comparison
   tasks. New public imports provide names or instances occurring in signatures;
   proof-only imports in the existing item are ordinary imports. Independently
   computed both project import closures: exactly 73 modules are removed, and the
   report's module list agrees exactly (none missing or spuriously listed).
   The report also names both removed original direct dependencies and explains
   which components remain needed. Read unit `sk-thm-picard-f-representable`:
   its `realized.statement` and sole `realized.steps` entry are empty. The argument
   retains the original restriction/affine-computation route and changes no unit
   or chapter. Verdict: pass; pruning is for this proof's closure, not a claim
   that the old modules have no other users.

5. Checked all four node files against the declarations. Their stored Lean
   signatures match the files modulo whitespace, every `proof_deps` is exactly
   the union of its proof steps' `uses`, and the steps describe the actual proof
   or the remaining named task. The existing node changes only `proof`,
   `proof_deps` and `proof_origin`. Each new node has its own module, source,
   complete proof plan, searches, creation record, blueprint ancestry, chapter,
   unit and Lean record. Verdict: pass.

Second-reading changes: corrected the report's accounting to explicitly classify
one hole closed and two holes added as a decomposition and to disclose `sorryAx`
in the item's axiom closure; added this independent reading and verification.
No Lean proof or statement needed repair. Scratch axiom-probe copies were removed.
