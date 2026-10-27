## Worker report

The module `Sheaf.CategoryTheory.SystemSingletonScalarExtension` states
`SheafOfModules.singletonScalarExtension`, with its sole postponed proof `sorry`.
The remaining declarations construct the particular comparison and its canonical
maps from the already recorded singleton, sequence-site and scalar models.
Definitions contain real data; no new mathematical notion or dependency interface
is needed. The item's statement, proof and dependency lists are unchanged.

The earlier Q83 attempt confused this stage-2 request with re-splitting. The live
node is already split and stage-1-reviewed PASS for Q67, but has no Lean binding.
This delivery neither re-splits the node nor changes any stage-1 fields. There is
no repair note for this item. The example CompactObject module is now withdrawn;
its node records the upstream `CategoryTheory.IsCompactObject` instead.

Hypotheses and objects:

- The site is `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`,
  with `[EssentiallySmall.{w} C]`. The module universe is `w`, independently
  of `u,v`. The sheaf-composition, sheafification and locally-bijective
  instances are the existing general-site module-category infrastructure;
  they are available for a site small in the module universe. No equality
  between the site-object, site-morphism and coefficient universes is imposed.
- The two inverse coefficient sequences are `B,D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`;
  the name `D` here denotes the node's sequence C, leaving `C` for the site.
  The morphism `a : B ⟶ D` has all its transition-commutation equations as
  naturality. `singletonSequenceRingMap a` assembles those exact components
  on the recorded vertical sequence site.
- Strict systems are the existing `StrictRingSystem B`, realized through the
  existing `strictSystemSequenceEquivalence B` as `systemSequenceModules B`.
  No category of diagrams in level derived categories replaces strict systems.
- The index `n : ℕ` denotes positive level n+1, exactly as in the recorded
  singleton implementation. There is no excluded first level.
- `S : SystemScalarAssignment`, `T : SystemTensorCoherence S`, and
  `A : SystemScalarModel (singletonSequenceRingMap a)` are presentations of
  the already specified universal scalar derived pairs and normalized
  adjunctions. They are arbitrary such presentations, not extra flatness or
  existence assumptions. The imported `nonempty_systemScalarModel` and
  `systemTensorCoherence` supply them for every coefficient map. Every scalar
  model retains its actual sheafified ordinary functor and its universal counit.
- `singletonSequenceOrdinary`, `singletonSequenceDerived`, and their adjunctions
  are the recorded ordinary and derived singleton transported through the
  exact sequence-site equivalence. The comparison is the transported existing
  universal comparison, not an unrelated isomorphism.
- All complexes use `CochainComplex ... ℤ` and all localizations use ordinary
  `DerivedCategory`. No boundedness, normalization of systems, or coefficient
  flatness is assumed. The only K-flat hypothesis is `systemLevelKFlat B n P`
  in the representative clause, precisely K-flat plus flat terms.

Conclusions, in the order of the Lean conjunction:

1. The derived natural isomorphism itself is the actual data declaration
   `singletonScalarDerivedIso S T a A n`. Its type is
   `singletonSequenceDerived S T B n ⋙ A.model.T ≅
   (S (a.app (op n))).model.T ⋙ singletonSequenceDerived S T D n`.
   Lean functor composition reads left to right, so this is exactly the
   node's S_bullet L_n^B -> L_n^C S_n.
   Its definition is `leftAdjointUniq` for the two specified composite
   adjunctions, after `singletonDerivedRestrictionEvaluation` identifies
   their right adjoints. The latter is the canonical localized
   identity-on-sections square `singletonRestrictionEvaluation`.
   The first conjunct states the full equality of the actual Hom transposes
   for every input, output and morphism. Thus identities specialize to the
   unit and counit compatibility; this records their normalization, not just
   existence of naturally isomorphic objects.
2. For every flat-term K-flat input complex, the second conjunct asserts
   whole-sequence-site K-flatness and flatness of every term of the ordinary
   B-singleton, its scalar extension, and the C-singleton of the level
   scalar extension. These use `IsKFlatIndependentCoefficients` and
   `IsFlatOnSite` for `systemSequenceRing B` or `systemSequenceRing D`,
   rather than merely componentwise predicates.
   It asserts both source/target representative comparisons are `IsIso`.
   The displayed equation says d_n followed by the target comparison is
   the source comparison followed by localization of the actual ordinary
   system natural isomorphism. It therefore gives the claimed derived
   representative, with all differentials and transitions retained.
3. The third conjunct is the explicit ordinary comparison on all local pure
   tensors below n. `systemModelTmul` uses the published scalar-first
   convention. The source is c tensor (b tensor x), and the target is
   (a_j(b)*c) tensor (1 tensor x). The coordinate maps are the existing
   `systemSingleLevelBelow ... .inv`; no arbitrary coordinate maps are
   quantified over. It holds for every ordinary module, hence termwise for
   the stated complexes, not only for selected resolutions.
   At j=n the two identity-transition tensors reduce by the existing
   normalized ordinary tensor unit to multiplication on the scalar factor;
   the same all-b,c,x equation specifies that normalization.
4. Above n, the fourth conjunct states both evaluated ordinary objects are
   zero and their evaluated comparison is the zero morphism. Between zero
   objects this is their unique morphism, the identity of zero after the
   canonical zero identifications. No separate levelwise choice is used:
   the arrow being evaluated is the same actual natural system isomorphism.
5. The last conjunct is the lower-singleton square on every derived object
   and every n<=m. `singletonLowerMap` is the transpose of the recorded
   below-level evaluation isomorphism, transported through the sequence-site
   equivalence. `singletonScalarSquare` is built from the existing canonical
   derived scalar composition isomorphisms and `a.naturality`. The two paths
   are d_m after scalar extension of the B-lower map, and d_n followed by
   this scalar associator and the C-lower map. Equality objectwise for the
   natural constructions is equality of the natural transformations.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, with Grothendieck topology
  and sheaves as its recorded convention. The size node is metatheoretic;
  its record explicitly asks consumers to bind universes themselves.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent existing Mathlib
  `SheafOfModules` specialization.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`; `Mathlib.Algebra.Homology.HomologicalComplex`:
  `CochainComplex`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `strictSystemSequenceEquivalence`, `systemSequenceRing`,
  `systemSequenceModules`, `systemSequenceEvaluation`.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `systemLevelLeftExtensionTheory` and its reexported existing basic
  interface, including `systemLevel`, `SystemScalarAssignment`,
  `SystemTensorCoherence`, and `systemLevelKFlat`.
- `Sheaf.CategoryTheory.SystemSingleDerivedExtension`:
  `systemSingleDerivedExtension`, retaining its ordinary adjunction;
  `Sheaf.CategoryTheory.SystemOrdinarySingleExtension`:
  `systemSingleFunctor`, `systemSingleAdjunction`, `systemSingleLevelBelow`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`;
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `sheafRingDerivedCoefficientAdjunction`. Their normalized package is the
  existing `SystemScalarModel` from `SystemScalarModel`.
- `Sheaf.CategoryTheory.SystemEvaluationTopos`: the existing additivity
  instances for the two sequence equivalence functors. The two instance
  aliases in this module expose those existing values for projection types;
  no property is postulated or reproved.
- `SystemSingleDerivedEvaluation`: `systemSingleDerivedBelow`;
  `SystemScalarCoherence`: `systemScalarModelDerivedComposition`;
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Equivalence.mapDerivedCategory`, `Functor.mapDerivedCategoryCompIso`;
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`:
  `Functor.mapDerivedCategorySquareIso`.

Proof-dependency modules are imported for stage 3, including the ordinary
coefficient adjunction, K-flat ringed pullback, tensor colimits, system
coproducts and exact evaluations, K-flat resolutions, tensor complexes and
normalized adjunction composition. The sole sorry's docstring reproduces
all nine node proof steps, including balancing, strict transition coherence,
whole-site K-flatness, the ordinary unit test and lower-singleton square.

Edge cases checked before statement writing: n=0 (positive level 1), j=n,
j>n, n=m, and n<j<=m in the lower square. Zero coefficient rings and zero
modules are allowed. Coefficient maps need not be injective, surjective or
flat; for example Z -> Z/2 is permitted and computes derived tensor rather
than an underived substitute. No nonempty-site assumption is imposed, so
the empty site remains included. The K-flat claim is on the entire vertical
ringed sequence site and not just on individually evaluated complexes.

Searches for reuse:

- msearch LeanFinder, "Derived extension of scalars commutes with singleton
  left extension for inverse systems of sheaves of modules" and "Extension
  of scalars and left adjoint to evaluation of inverse systems of module
  sheaves commute": no matching whole statement was obtained. These
  calls produced no usable results before the provider interruption.
- msearch LeanSearch, "Derived singleton extension for inverse systems of
  module sheaves commutes with scalar extension": eight hits, including
  ModuleCat.ExtendRestrictScalarsAdj.homEquiv_symm_apply and scalar unit
  formulas; none concerns strict systems or this derived comparison.
- msearch Loogle, `SheafOfModules.restrictScalars`: four hits, ordinary
  restriction of scalars, additivity and its underlying object/map equations;
  reused the definition.
- msearch grep, `singleton|singleExtension`, Mathlib CategoryTheory:
  25 unrelated hits, no such theorem. msearch grep,
  `extendScalars_assoc|homEquiv_extendScalarsComp|def restrictScalars`,
  Algebra/Category/ModuleCat: ordinary module scalar restriction and
  associativity only, not this derived singleton theorem.
- rg in the project's WeilConjectures and Sheaf sources for
  `singletonScalar|SingletonScalar|single.*[Ss]calar|[Ss]calar.*[Ss]ingle|singleton.*scalar`
  found degree-zero single complexes and the recorded ordinary/derived
  singleton interfaces, but no whole comparison. Searching the item id
  in WeilConjectures found no declaration. The exact component declarations
  were opened and reused, rather than duplicated.

The Stacks source `sites-cohomology.tex`, label
`lemma-derived-pullback-composition` (0D6D), was opened. Its flat-term K-flat
representative argument is the source of the derived computation. As the
node explicitly records, singleton extension is an agent auxiliary to this
argument and is not presented as a geometric inverse image.

No statement fault, statement correction, or STATEMENT-DISPUTED issue was found.

Validation: scompile.py accepted the complete module against the published live
library. A local wrapper attempt exceeded its file limit, and the prescribed
server confirmation compiled the same source in 35.3 seconds, within the unchanged
60-second limit. The first deliver2.py dry run passed preflight and compilation
(commit eebb8b68903). Removed an unused derived-adjunction import afterward;
the final dry run and delivery recompile the final source. No global build or
direct mutation of the read-only repository was performed.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
