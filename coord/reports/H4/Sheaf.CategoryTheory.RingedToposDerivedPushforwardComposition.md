## What changed

Proved `CategoryTheory.ringedToposDerivedPushforwardComposition` by testing the
resolution comparison on K-flat objects in homotopy categories, then using the
existing K-injective right-derivability API. The composite right derived functor
is chosen to be `Rf ⋙ Rg`; its unit is the composite unit, and the comparison is
the identity isomorphism with the required normalization and uniqueness.

Added `Sheaf.CategoryTheory.RingedToposKFlatPullback`, with a fully proved theorem
`CategoryTheory.RingedToposMorphism.exists_kFlatPullback`. It constructs the tensor
pullback adjoint to the exact supplied `modules` functor from its graph equations,
identifies the two flatness predicates using the existing tensor comparison, and applies
the existing K-flat preservation and derived-pullback declarations. The initially isolated obligation was proved
in this session; it leaves no new hole.

Updated the composition node's route and Lean statement spelling, and added the
proved helper's node. The unit route and all target statements are unchanged.
The composition statement only receives explicit inferred universe/site annotations;
see `coord/changes/ringed-topos-derived-pushforward-composition-elaboration.md`.
No other existing module is adapted. Both final delivered modules compile cleanly with
`lcompile.py --all`; the helper reuses the existing tensor comparison after the build refresh.
Import-direction checks pass. The final delivery dry run performs the required
preflight and axiom checks; neither delivered file contains `sorry`.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.ringedToposDerivedPushforwardComposition`.

Added and proved:
`CategoryTheory.RingedToposMorphism.exists_kFlatPullback`
(node `lem-weil-pbc-supplied-ringed-topos-kflat-pullback`).

Original holes closed: 1 of 1. New holes added: 0. Residual split-offs: 0.
No `sorry` remains in any delivered declaration. This is a proof from existing
project declarations, some of which are still admitted in their own modules;
it is not a claim that the entire target closure is already axiom-clean.
All private helpers have complete proofs, and all definitions are constructions.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullback`

The tensor-pullback helper still uses `ModulePullbackPushforwardAdjunction`,
`Paper.KFlatRingedToposPullback` and `Paper.RingedTopoiDerivedPullback`. These three
are moved below the proved helper, not claimed to be pruned from the whole closure.
The refreshed `RingedTopoiDerivedPullback` proof itself uses the live K-flat resolution,
so `KFlatResolutionIndependentCoefficients` now disappears from this item's full closure. The main argument itself uses the already proved live
resolution `CochainComplex.exists_isKFlatResolution` from `KFlatResolution`.

These eleven modules disappear from this item's full import closure (other parents
may still need them). Corresponding recorded nodes are listed beside each module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the unused independent-coefficient module attached to `lem-pc-kflat-resolution`; that node's live specialization is still used
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`: `lem-weil-pbc-site-derived-tensor-descent`
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`: `def-pc-derived-adjunction-hom-diagram`
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`: `lem-pc-derived-adjunction-source-colimit`
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`: `lem-pc-derived-adjunction-target-colimit`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`: `lem-pc-derived-adjoint-functors`
- `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`: `new-derived-adjunction-compatibility`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`: `def-pc-essentially-constant-ind-diagram`
- `Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors`: `new-everywhere-defined-derived-functors`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`: `lem-weil-pbc-kinjective-total-derived`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`: `lem-pc-pre-derived-adjoint-functors-general`

The old proof's construction and conjugation of three derived adjunctions,
derived pullback composition, and separate cohomology-isomorphism argument are
unnecessary here. The corresponding direct planned dependencies on
`def-weil-pbc-composite-adjunction`, `def-weil-pbc-adjunction-conjugate`,
`lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-unbounded-derived-iso-cohomology`,
`lem-weil-pbc-kinjective-hom-derived`, and
`lem-weil-pbc-kinjective-total-derived` are removed from this node's proof dependencies.
The required localization, K-injective hom comparison, and derivability facts are
used through their existing Mathlib/source-library proofs instead.

The complete set removed from the old node's direct `proof_deps` is:

- `def-weil-abstract-derived-category`
- `def-weil-pbc-adjunction-conjugate`
- `def-weil-pbc-composite-adjunction`
- `lem-pc-derived-adjoint-functors`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-pc-quasi-isomorphisms-multiplicative-system`
- `lem-pc-right-fraction-representation`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`

These are removed as direct planned dependencies; generic derived-category definitions,
fraction calculus, and module-pullback ingredients may remain transitively imported.
The second reading also removed the helper's redundant direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`; it remains transitive.

## Where the brief, the DAG or earlier work was wrong

The existing module adjunction theorem constructs its own module direct image;
it does not directly identify it with `RingedToposMorphism.modules`. The new helper
proves that interface from the supplied generalized-section graph equations,
rather than assuming equality of arbitrary chosen functors.

The K-flat pullback theorem uses `IsFlatOnSite` and the independent-coefficient
K-flat predicate, while this item uses the live `IsFlat` and `IsKFlat` predicates.
The independent K-flat specialization is definitionally the live predicate.
The flatness equivalence needed a proof: the tensor-right functors are naturally
isomorphic through sheafification of the same presheaf tensor products. This is
proved privately in the helper using `SheafOfModules.siteTensorRightIso` from
`RingedTopoiDerivedPullback`, with no signature change elsewhere.

The node's resolution attachment currently names the still-admitted independent
coefficient theorem. The live-universe specialization required here already has a
proof in `Sheaf.Algebra.Homology.KFlatResolution`; the item uses that proof directly.
The original source-level statement also elaborated too slowly without explicit
inferred parameters. The change record preserves both spellings verbatim and
explains why their kernel signatures agree.

No statement was found false. The old conjugation route was longer than needed;
no blueprint unit statement or realized step is bypassed.

## New nodes

`lem-weil-pbc-supplied-ringed-topos-kflat-pullback`, in
`dag/nodes/sec-proper-base-change/`: the fully proved supplied-functor pullback
interface used by the composition proof. Its three mathematical parts are the
module adjunction, preservation of K-flat complexes with flat terms, and inversion
of quasi-isomorphisms on that class. Its proof is complete in this delivery and
needs no follow-up item. Sources: Stacks 03D7, 0G7E and 06YY.

Change record:
`coord/changes/ringed-topos-derived-pushforward-composition-elaboration.md`.

## Second reading by H4

1. **Interfaces.** I diffed the composition module and its node against the repository;
   the helper and its node are new. The only existing signature edits are explicit
   coefficient universes and the site arguments of `RingedToposMorphism`, all declared
   verbatim in the change record. No binder, hypothesis, conclusion, or definition changes.
   I exported the original compiled type as a shared expression graph and had Lean
   kernel-check a declaration of that exact type whose proof is the delivered theorem.
   This passed (`scratchpad/candidate/kernel-probe.log`). Raw expression differences are
   inferred proof terms such as `univLE_of_max UnivLE.self` versus `UnivLE.self`; proof
   irrelevance makes them definitionally equal. The universe parameter list is `[u, w]`
   in both versions. No target statement or other group's module is changed. Verdict: pass.

2. **Proof and data.** I read the fraction argument, the Yoneda test, the K-injective
   derivability criterion, and the normalization and uniqueness equations. The comparison
   is `Iso.refl` for the chosen composite derived functor; naturality at `j` gives the stated
   formula after cancellation of `Qj`. This does not assume direct image preserves
   K-injectives. I also read the helper's ring-operation transport, construction of the
   structural ring morphism, restriction of the adjunction to linear maps, and its two
   preservation clauses. The tensor isomorphisms are constructions, and no data is chosen
   in a definition from an admitted mere-existence theorem. Both modules compile; neither
   has a local `sorry` or a forbidden axiom/implementation escape. Independent
   `#print axioms` probes for both public theorems show exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` from still-open upstream declarations. Verdict: pass.

3. **New statement and searches.** There are no admitted split-offs. The helper treats
   one supplied module direct image, so it is strictly smaller than the composition item.
   Its hypotheses and all three conclusions match its node; I made the node's
   commutativity hypothesis explicit, as already required by `CommRingCat` in Lean. I checked identity morphisms,
   zero rings and zero complexes, and arbitrary nonflat structural maps: the construction
   uses extension of scalars without assuming it is exact. The graph equations are tested
   on generalized elements, so no point or nonempty-site assumption is introduced. I read
   Stacks Tags [03D7](https://stacks.math.columbia.edu/tag/03D7),
   [0G7E](https://stacks.math.columbia.edu/tag/0G7E), and
   [06YY](https://stacks.math.columbia.edu/tag/06YY), and checked the imported Lean statements.
   My additional LeanFinder, Loogle and grep queries are in `searches.jsonl`. They found no
   replacement for the arbitrary supplied-functor interface. The local search did find
   the existing private tensor comparison, which I reused. Verdict: pass.

4. **Route and imports.** The hom-set argument refines right fractions with live K-flat
   resolutions, uses the termwise homotopy adjunction, and tests `Q(g_*j)` by Yoneda before
   constructing the composite derived unit. It uses Mathlib/source-library localization
   and derivability directly. This is below the proper-base-change unit: I checked
   `dag/units/sk-thm-properbasechange.json`, whose three realized steps are unchanged.
   The full list of removed direct DAG dependencies is recorded below. The public import
   `RingedSiteKInjectiveResolutions` is needed to supply the `Abelian` instance in the public
   derived-category signature; making it private fails compilation there. Verdict: pass.

5. **DAG.** The existing node changes only `lean`, `proof`, `proof_deps`, and `proof_origin`.
   Its six proof steps follow the actual argument. The helper node contains its exact Lean
   statement, creation and blueprint records, searches, sources, and the union of its
   proof-step dependencies. I corrected its blueprint ancestor to `def-weil-pbc-four-arrows`
   with the composition node in `via`, as returned by `blueprint_refs.py ancestor`, and
   marked the failed LeanSearch query `unavailable`. I updated its tensor-comparison step to identify the existing
   declaration now used. The live resolution is the proved universe specialization of the
   recorded independent-coefficient resolution statement, explicitly identified in step 2
   and in this report. Verdict: pass.

I removed the duplicate private constructions `presheafTensorIso` and `tensorRightSiteIso`
from the helper and reused `SheafOfModules.siteTensorRightIso`, exposed with a proof-only
`import all Sheaf.Paper.RingedTopoiDerivedPullback`. I removed its now-unneeded direct import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`. I completed the report's full removed-dependency list, recomputed the eleven pruned
project modules against the refreshed sources, and corrected the helper's
blueprint provenance, explicit commutativity hypothesis, and unavailable-search verdict. The public statements and
all existing public imports are unchanged by the second reading. The comparison became
available after the published build refreshed during review; the first probe against the
previous build correctly reported it absent.

The existing composition docstring describes the original planned conjugation proof.
The actual shorter route is recorded in its updated DAG proof and in this report: refine
fractions by K-flat resolutions, use adjunctions and the K-injective hom comparison to show
`g_*j` is a quasi-isomorphism, and construct the composite derived unit. This is the suggested
replacement for the historical proof-plan paragraph when that documentation is updated.
