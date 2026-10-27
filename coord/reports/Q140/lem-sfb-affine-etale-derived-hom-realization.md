## Worker report

The main module `Sheaf.AlgebraicGeometry.AffineEtaleDerivedHomRealization` states
`AlgebraicGeometry.Scheme.Modules.affineEtaleDerivedHomRealization`, with `sorry`.
All constructions contain real data. The only other postponed statements are the
underlying-ring sheaf condition, mixed-universe K-injective existence and Hom
quasi-isomorphism invariance and representative comparisons, in their owning dependency modules.

Hypothesis and clause matching:

- Commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
  The affine scheme is literally `Spec (.of A)` throughout.
- The exact associated functor is the dependency's `affineEtaleAssociatedFunctor A c`,
  with `c : ZariskiEtaleModuleContext (Spec (.of A))`. Its context contains continuity
  and right-adjoint-existence proofs, not independently chosen module functors.
- Ordinary unbounded derived categories are `DerivedCategory`, with the target's
  localization-size choice `[HasDerivedCategory.{wE} ...]`. Ordinary module RHom uses
  the existing canonical Grothendieck localization supplied to
  `ordinaryModuleDerivedInternalHom A`; no bounded derived category is substituted.
- Both objects are the factors of `DerivedCategory (ModuleCat A)` opposite times itself.
  `affineEtaleDerivedHomPairProperty A` selects exactly the admissible pairs. Its
  first conjunct is `∀ i, Module.Finite A (H^i E)`; its second is
  `∃ b, ∀ i, b < i → IsZero (H^i E)`; its third is
  `∃ a, ∀ i, i < a → IsZero (H^i F)`. In particular F has no finiteness condition.
- The canonical universe transport is `smallEtaleModuleSectionLift`. It keeps the
  exact `smallEtaleModuleRing`, sends sections to ULift, and conjugates restrictions
  and morphisms by up/down. `smallEtaleModuleSectionLiftEquiv` is the explicit
  linear equivalence with forward map down and inverse up, also in degree zero.
- The existential additive proof permits `mapHomologicalComplex`. The existential
  derived functor `a` is fixed, up to natural isomorphism, by the natural factorization
  `DerivedCategory.Q ⋙ a ≅ (affineEtaleAssociatedFunctor A c ⋙ lift).
  mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q`. It is not an arbitrary functor.
- The final `Nonempty (... ≅ ...)` is an isomorphism of FUNCTORS on the full category
  of admissible pairs. Its left functor is RHom_A followed by a; its right functor
  is `a.op.prod a` followed by ringed-site RHom. It therefore states the displayed
  derived isomorphism and naturality for every morphism of pairs, contravariant in
  E and covariant in F, rather than merely per-object or per-cohomology isomorphisms.
- `smallEtaleCommRingHasDerivedCategory` returns its existing input instance `h`
  under the definitionally equal commutative-ring presentation. This avoids a
  typeclass search mismatch without choosing a different localization.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization`:
  `affineEtaleAssociatedFunctor`, `exists_affineEtaleDerivedModuleRealization`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`;
  `...HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `ordinaryModuleDerivedInternalHom` and the publicly re-exported generic
  `derivedInternalHomOfUniverses`. The latter's full signature was read and is
  preserved through the companion repair.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`; the complete
  generator and resolution signature is preserved and generalized as described below.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; `SheafOfModules.unit` and Mathlib
  `PresheafOfModules.sheafification` supply the prescribed localized-unit generator.
- `WeilConjectures.Algebra.Homology.HomComplex`: `homComplexFunctor`, whose rings and
  module section universes are already independent. Its result section universe
  is the maximum of the site and input module universes.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`, `toKInjectiveResolution`.

The main module imports every currently recorded proof-dependency module, using
plain imports for proof dependencies. `lem-sfb-zariski-etale-pseudocoherent-rhom`
has no Lean record and is only a proof dependency: there is no invented substitute
or import. The theorem docstring carries all five proof steps and their DAG ids.

Edge cases checked: A may be the zero ring, so the empty affine scheme remains
included. Either complex may be zero; the inequalities are strict and bounds
may be any integers, including negative ones and equal bounds. The finite-free
model has only a-n ≤ p ≤ b in degree n, and may have rank zero or an empty
contributing interval. F may have infinitely generated cohomology (e.g. an
infinite direct sum of copies of A in degree zero). E may extend indefinitely
to negative degrees and F indefinitely to positive degrees. The natural-isomorphism
form includes all morphisms of these pairs. No equality between site-object,
site-arrow, coefficient-ring or derived-morphism universes is imposed.

Searches performed before drafting:

- LeanFinder: "Derived Hom of bounded above finite cohomology and bounded below
  complexes commutes with affine etale associated module sheaf": eight hits on
  ordinary sheaf cohomology, scheme modules, and Ext constructions; no comparison.
- Loogle: `"derivedInternalHom", "etale"`: zero hits.
- Mathlib grep: `(RHom|derivedInternalHom).*([Ee]tale)|([Ee]tale).*(RHom|derivedInternalHom)`:
  zero hits.
- LeanSearch: "Affine etale realization commutes with derived internal Hom from
  bounded above coherent complexes to bounded below complexes": eight hits on
  Ext, exact-functor factorization, affine morphisms and etale ring maps; no match.
- Project/source `rg` for `affineEtale.*[Hh]om|[Hh]om.*affineEtale` and the exact node id:
  found the realization prerequisite but no statement of this comparison. The
  generic/ordinary Hom, Hom-complex and K-injective signatures were read in full.
  Additional searches for section lift, ULift, independent coefficient rings,
  `HasSheafCompose`, and free/sheafified localized generators found the existing
  ModuleCat ULift and extension-by-zero constructions used here; no compatible
  public ringed-site derived-Hom interface with smaller coefficient rings.

No mathematical STATEMENT-DISPUTED flag remains. The explicit size presentation
is recorded as a statement correction below, rather than hidden in the Lean.

## Dependency modules

`def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`
publicly imports the complete prior `OrdinaryModuleDerivedInternalHom` module.
The prior generic interface puts both the coefficient rings and module sections
in `max c v r`. It cannot use actual etale structure rings in u when the site
objects live in u+1. The companion keeps rings in r and sections in max c v r.
It uses exactly the existing Hom complex, canonical functorial K-injective
replacement, and `Localization.lift` through `Q.op.prod Q`. The named invariance
statement has `sorry`; its docstring explains the two variable arguments,
naturality, two-out-of-three, K-injective homotopy equivalences and localization.
The companion also states `derivedInternalHomMixedUniverses_comparison` for every
functorial K-injective replacement and `derivedInternalHomMixedUniverses_obj_iso`
for every source representative and K-injective target representative, with the
complete composite-resolution and representative-transport proof docstrings.
The primary definition has no sorry data. The old ordinary/module/ringed APIs
remain re-exported in full. The node changes only in `lean`.

`prop-pur-kinjective-resolutions-exist`:
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses` re-exports
the prior module and states exactly all its clauses with independent smaller
rings: `IsGrothendieckAbelian`, the specified coproduct generator, and a functor I
with natural η whose components are quasi-isomorphisms into K-injective complexes
having injective terms in every degree. The generator is literally the
sheafification of `extensionByZeroPresheaf` applied to the localized unit,
sectionwise lifted by the real `PresheafOfModules.sectionUniverseLift` functor.
This avoids the old `PresheafOfModules.free` API's forced equality of ring and
free-index universes. `hasSheafCompose_commRingToRing` names the proof needed to
regard the original commutative structure sheaf as a ring sheaf on any site;
its proof is postponed and documented, with no ring data postponed. The other
new theorem is the resolution-existence statement itself. This is an interface
repair, not a replacement by an arbitrary generator. The node changes only in
`lean`. It already lies in the transitive dependency closure through the derived
internal-Hom well-definedness nodes; no statement dependency is added.

## Statement corrected

The old statement is preserved verbatim in `statement_change.old_statement`.
It asks for `a_A(RHom_A(E,F)) ≅ RHom(a_A(E),a_A(F))` in the small-etale module
derived category without specifying the section-size presentation. The recorded
affine associated functor has section modules in u, whereas the generic Hom API
on the actual site (objects u+1, arrows u) needs section modules in u+1; its old
coefficient restriction also erroneously forced structure rings into that maximum.

Following spaces-perfect.tex Tag 08JP(1) and perfect.tex Tag 0A6H(3)(a), the corrected
statement makes the canonical sectionwise ULift explicit on both sides, with
original rings, restrictions, site, and linear section identification down/up.
It keeps every original mathematical hypothesis and the natural derived isomorphism,
with the generalized K-injective interface supplied as an inherited dependency repair. The proof
and proof dependencies are unchanged: all their finite-free Hom computations
transport through the explicit section equivalences. The item is not a blueprint
unit's own statement (`blueprint.is = null`).

Citer audit: exactly one node names this item in stmt_deps or proof_deps:
`lem-sfb-space-coherent-derived-internal-hom` (holds: true). Its affine-chart
argument uses the comparison to compute coherent cohomology and the lower bound.
The same finite-free Hom model, with sectionwise down/up identifications, gives
those exact computations; a finite associated sheaf is identified by the same
finite module. Section lifting is exact and fully faithful and reflects these
isomorphisms, so no case is lost. The citer is not edited.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
