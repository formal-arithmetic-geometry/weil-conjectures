## Worker report

The module `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` states
`AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProEtaleAdjunctionTransfer`.
Its one theorem has proof `sorry`. All nine auxiliary declarations have actual data;
they name intersections, full-subcategory restrictions, or inclusions of the published
constructions. The natural-language proof in the theorem docstring follows all five
steps of the node. No node statement or proof plan was changed.

Hypotheses and clauses, matched to Lean:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The arbitrary characteristic-p field is
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`:
  for a field, positive characteristic is prime, and p is its canonical `ringChar k`.
- `X,Y : Scheme.{u}` have `Over (Spec (.of k))` structures. For each structure morphism,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` state exactly separated finite
  type over k. The named morphism f has `IsOver`, `LocallyOfFiniteType`, `QuasiCompact`,
  and `IsSeparated`. The field is not assumed perfect, finite or algebraically closed.
- The coefficient section binds `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  `_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0` states annihilation by a power of ell, including
  exponent zero for the zero ring. No domain, field, nonzero or cyclic-ring assumption.
- `etaleProperty A T` is the recorded `Etale.DerivedCategory.isBoundedConstructible A T`
  intersected with `DerivedCategory.finiteTorAmplitude` on the actual small etale
  module-sheaf category. The latter quantifies over every sheaf in degree zero and
  asks for one finite cohomological interval; it does not merely test constant sheaves.
- `proEtaleProperty A T` uses the essential image of that same finite-value bounded
  constructibility predicate under `comparisonUpperStar.mapDerivedCategory`, exactly
  the finite-coefficient etale-origin convention in def-weil-pbc-proetale-modules,
  intersected with the actual pro-etale finite Tor-amplitude predicate.
- The categories are the `ObjectProperty.FullSubcategory` of these predicates. All
  ambient derived morphisms are retained. Coefficient/module sizes follow the published
  convention: scheme universe u, coefficients and module/sheaf values u+1. No equality
  between the site's object and morphism universes is imposed.
- `hX,hY` express the restriction of the specified termwise comparison to these
  categories. `eX,eY` are the chosen equivalences, including quasi-inverses Q_X,Q_Y,
  units, counits and triangle identities. `heX,heY` identify their forward functors
  with the actual restricted comparison; these are not arbitrary equivalences.
- `(c : Compactification f)` is the fixed compactification. `etaleLowerShriek A c hEt`
  restricts the recorded unbounded etale compactification composite;
  `proEtaleLowerShriek A c hPro` restricts the published ordinary pro-etale composite
  for exactly the same c. The membership witnesses `hEt,hPro` spell out the node's
  phrase that these are functors restricted to Dctf; no functor is replaced by a map
  given as a parameter.
- `cf` has orientation `etaleLowerShriek ⋙ eY.functor ≅ eX.functor ⋙ proEtaleLowerShriek`,
  the Lean composition order of nu_Y^* Rf_!^et ≅ Rf_! nu_X^*. `_hcf` identifies its
  inverse, after the equality identifications heX/heY, with
  `compactSupportSiteComparison A c`. That published comparison is the canonical
  proper direct-image counit mate composed with exact open-extension comparison.
  Thus the specified compact-support comparison is retained, including its normalization.
  `etaleToPlus` reads a lower cohomological bound from the recorded boundedness witness
  and gives the canonical inclusion needed by that bounded-below comparison API.
- `G` and `adjEt : etaleLowerShriek A c hEt ⊣ G` are precisely the assumed etale
  right adjoint and its adjunction, including its given counit.
- The first existential conclusion is an actual adjunction `adjPro`, with right functor
  `eY.inverse ⋙ G ⋙ eX.functor`, exactly nu_X^* G Q_Y.
- The first conjunct specifies its counit at every `eY.functor.obj N`. Its first
  factor is `proEtaleLowerShriek.map (eX.functor.map (G.map (eY.unitIso.inv.app N)))`,
  which identifies G^pro nu_Y^* N with nu_X^* G N through Q_Y nu_Y^* N ≅ N. The next
  factors are `cf.inv.app (G.obj N)` and `eY.functor.map (adjEt.counit.app N)`.
  Removing the displayed identification gives exactly epsilon^pro = nu_Y^*(epsilon^et)
  composed with c_f(GN) inverse. Composition in Lean is written in execution order.
- The last conjunct applies to the Brown adjunction on the localizing closures:
  `hLoc` supplies the restriction of the same ambient compactification composite;
  `J` is its right adjoint and `adjBrown` its adjunction. These are universally
  quantified inside the conclusion, so the assertion applies to the Brown choice of
  sk-prop-sf-existence and every isomorphic adjunction choice. It does not assume
  Brown finite-Tor preservation. It concludes `hJ`, that J preserves Dctf, and an
  `∃! γ` natural isomorphism from the transported G^pro to `brownRestriction A J hJ`.
- The uniqueness property is exactly the ambient counit equation:
  the actual compactification functor maps `γ.hom.app N`, followed by the original
  `adjBrown.counit.app (toLocalizing.obj N)`, to `adjPro.counit.app N`.
  `brownRestriction` retains J's actual ambient objects and maps. The equation uses
  the original Brown counit, not a chosen replacement adjunction on the smaller category.

Coefficient presentation and dependencies:

The ordinary fixed-ring presentation is the one already exported by the recorded
`Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` and the canonical compact-support
comparison. It identifies with the continuous-function section-ring presentation through
`AlgebraicGeometry.ProEtale.finiteCoefficientRealization` and its published equivalence,
from `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`. Its associated bounded-constructible
predicate is the essential image of the same finite-value etale predicate. In the proof,
`Profinite.finiteDiscreteCondensedRing_constant`,
`AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRing_constant`, and
`CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` identify this ordinary
presentation with the internal-module presentation used by Brown existence. An exact
termwise equivalence preserves derived tensor and the defining localizing intersection;
therefore the ordinary closure and compactification functor here are those of the Brown
statement expressed in the identified coefficient categories. No second localizing-closure
construction, alternative coefficient ring or arbitrary realization is introduced.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`,
  module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  standing assumptions are rendered explicitly, and the chosen compactification c is a
  parameter, rather than silently replacing the chosen one by Nagata's default.
- def-weil-pbc-derived-categories: `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  reexported by `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`; cohomology is
  `DerivedCategory.homologyFunctor` and localization is Mathlib's `DerivedCategory`.
- def-weil-pbc-constructible-complexes:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, module
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`. The upstream generic
  finitely-generated-stalk predicate is deliberately not substituted for this one.
- def-weil-pbc-proetale-modules:
  `finiteCoefficientRealization`, `finiteCoefficientDerivedComparison`,
  `isBoundedConstructibleFiniteCoefficient`, and
  `finiteCoefficientRealizationIsEquivalenceRing`, module
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`; read for the equivalent fixed-ring
  convention and its etale-origin predicate, as above.
- sk-def-sfb-constructible: `ConstantModelConstructibleFiniteTor` and
  `constantModelBoundedConstructible`, module `Sheaf.Paper.CondensedConstantConstructibility`;
  read for the internal constant-model convention carried by the finite coefficient
  identification; Tor amplitude is the shared `DerivedCategory.finiteTorAmplitude` from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- def-sf-comparison-derived-pullback: `siteComparisonDerivedPullbackPlus`, module
  `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`; our unbounded forward functor
  is the same `comparisonUpperStar.mapDerivedCategory`, with bounded inputs. The plus
  comparison uses its published compatibility with the unbounded functor.
- def-amb-etale-compact-support:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, module
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, specialized to `ModuleCat A`.
- sk-prop-sf-existence: `CondensedRing.exists_localizingExceptionalAdjoint` and
  `CondensedRing.localizingLowerShriek`, module `Sheaf.Paper.LocalizingExceptionalAdjoint`;
  it is imported and its Brown adjunction is quantified in the identified ordinary
  coefficient presentation in the last conjunct.
- sk-def-localizing-closure: `CategoryTheory.localizingClosure` and
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`, module
  `Sheaf.Paper.LocalizingClosure` reexported by the recorded
  `Sheaf.Paper.LocalizingAdmissibleCoefficients`. The former is directly used to take
  the intersection in the ordinary presentation. It imposes no completeness condition.
- Canonical compact-support comparison:
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`, module
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- Proof-only published dependencies are imported: `CompactSupportComparisonUnit`,
  `FiniteDiscreteCondensedRing`, `FiniteDiscreteSchemeRing`,
  `InternalAbelianSheafModuleEquivalence`; `det-sp-unique-right-adjoint` is the Mathlib
  `CategoryTheory.Adjunction.rightAdjointUniq` and its counit equations in
  `Mathlib.CategoryTheory.Adjunction.Unique`.
- sk-prop-sf-rf-shriek-preservation has no published Lean record in the snapshot, so no
  module can yet be imported for this proof-only prerequisite. Its first two clauses
  are explicitly cited in the proof docstring for the Brown restriction step. It is not
  needed to type the statement, and no preservation hypothesis is added in its place.

Edge cases checked before the statement: the identity morphism uses an identity
compactification and the canonical comparison; empty schemes and empty strata give the
zero coefficient-sheaf categories with their full Hom sets; the zero ring is admitted,
including n=0; A=Z/ell^2 has no flatness or field hypothesis imposed on A; the zero complex
has a valid finite interval; equivalence choices need not be strict inverses, which is why
the inverse unit explicitly occurs in the counit formula. The tests for Tor amplitude are
all degree-zero module sheaves, including nonconstructible ones. No statement dispute or
mathematical correction was found.

Searches performed before writing:

- msearch.py leanfinder, query `transfer an adjunction across equivalences with prescribed
  counit and uniqueness of right adjoint`: eight generic category-theory hits, including
  `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` and
  `Adjunction.rightAdjointUniq_hom_app_counit`; no geometric statement with both the
  specified finite-coefficient comparison and the Brown restriction.
- msearch.py leansearch, query `right adjoint transport along category equivalence counit`:
  eight generic hits including `Adjunction.adjunctionOfEquivRight_counit_app`,
  `Equivalence.counit`, and `Adjunction.mkOfHomEquiv_counit_app`; no exact match.
- msearch.py loogle, query
  `CategoryTheory.Adjunction.ofNatIsoLeft, CategoryTheory.Adjunction.rightAdjointUniq`:
  zero hits. The declarations themselves were inspected directly in Mathlib afterward.
- msearch.py grep, query `adjunction.*(transfer|transport)|rightAdjointUniq` in
  `CategoryTheory`: 21 hits, generic uniqueness/transport; read the actual signatures and
  counit equations in Adjunction/Basic.lean and Adjunction/Unique.lean.
- rg on upstream WeilConjectures and project lean/Sheaf for the node id and names for
  adjunction transfer: one downstream docstring citation in FiniteCoefficientAdjointComparisons,
  no declaration of this statement. Additional rg searches for Dctf, Tor amplitude,
  constructibility, localizingLowerShriek, realization and comparison exposed the interfaces
  listed above. rg on dag/lean_names_upstream.json, Mathlib and both Lean source trees for
  our chosen namespace and declaration names found no collision.

Validation: scompile.py compiled this single delivered module both as a sandbox file and
under its actual library module path, with no errors or warnings. Earlier draft's unused
binder warning was repaired by naming the unused predicate `_P`. No global build or direct
compiler invocation was used. The node copy changes only `lean`. There are no new nodes
and no dependency-module repairs in this delivery. Independent review belongs to the
maintainer under the current direct-worker-delivery instructions.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
