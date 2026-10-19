## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleSupportedReconstruction` states the
normalized reconstruction theorem and supplies the canonical additive ring-object
transport used by the published arbitrary-ring pro-etale module framework.  It defines
`supportedRingAb`, `supportedRingMon`, `supportedRingMonComp`, the closed inverse/direct
image functors, the open inverse image and extension-by-zero functors, and the displayed
maps `supportedLambda` and `supportedTheta`.  The theorem
`AlgebraicGeometry.ProEtale.supported_reconstruction` has one postponed proof.  The
support lemma `supportedLambda_isIso` is the named postponed fact required by the
`supportedTheta` definition; its docstring records the two localization-sequence
arguments and it is listed in the node's `lean.declarations`.

The corrected Lean signature introduces `X Z S B K : Scheme.{u}`, closed immersions
`i : Z ⟶ X` and `e : B ⟶ Z`, complementary open immersions
`k : K ⟶ X` and `u : S ⟶ Z`, quasi-compact instances for `k` and `u`, and the equalities
`hk : Set.range k = (Set.range i)ᶜ` and
`hu : Set.range u = (Set.range e)ᶜ`.  This is the typed form of the source's two
complement statements.  `R` is a sheaf of `CommRingCat.{u+1}` on `X.ProEt`; `A` is a
module object over its additive ring realization and `M` is a module object over the
transported coefficient on `S`.  The isomorphism
`σ : (supportedOpenPullback i u R).obj ((supportedClosedPullback i R).obj A) ≅ M`
renders `σ : u⁻¹ i⁻¹ A ≅ M`.  The two support hypotheses are rendered by
`hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A)` and
`hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
((supportedClosedPullback i R).obj A))`.

The first conclusion is `IsIso (supportedLambda i u R A M σ)`, where
`supportedLambda` is exactly
`(supportedOpenExtension i u R).map σ.inv ≫
(ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app ...`, i.e.
`ε_u ∘ u_!(σ⁻¹)`.  The second is `IsIso` of `supportedTheta`, whose body is
`(ringSheafAdjunction i (supportedRingAb R)).unit.app A ≫
(supportedClosedPushforward i R).map (inv (supportedLambda ...))`, i.e.
`i_*(λ⁻¹) ∘ η_i`.  The restriction clause is the equation
`H.map (F.map θ) ≫ H.map ε_i = σ.hom ≫ η_u`, written with
`(supportedOpenPullback i u R).map` and
`(supportedClosedPullback i R).map`; this is the node's prescribed restriction.
The uniqueness clause quantifies every `h : A ⟶ i_*u_!M` and imposes the same
restriction equation before concluding `h = supportedTheta ...`.  Naturality quantifies
`A'`, `M'`, `σ'`, and explicitly supplies the same two support vanishings for `A'`; its
commuting condition is
`H.map (F.map a) ≫ σ'.hom = σ.hom ≫ b`, and the two conclusions are the naturality
squares for `lambda` and `theta`.

The statement dependencies used are: Mathlib `AlgebraicGeometry.Scheme` for schemes;
Mathlib `AlgebraicGeometry.IsClosedImmersion` and `AlgebraicGeometry.IsOpenImmersion`;
`AlgebraicGeometry.Scheme.ProEt` for the small pro-etale site;
`CategoryTheory.ringedSiteModules`/Mathlib `SheafOfModules` for module sheaves;
`AlgebraicGeometry.Scheme.proEtaleModuleInverseImage` and the published pro-etale
inverse-image/adjunction declarations; and
`AlgebraicGeometry.ProEtale.ringSheafAdjunction` plus
`AlgebraicGeometry.ProEtale.ringSheafOpenAdjunction` for the specified adjunctions.
The three copied dependency records in this delivery repair the stale interfaces for the
pro-etale site, arbitrary-ring inverse image, and arbitrary-ring module adjunction.

Edge cases checked before writing the signature: `K` or `S` empty (then the relevant
`IsZero` hypotheses force the reconstructed object to be zero), `i` or `u` an identity,
clopen complements, the zero ring sheaf, zero modules, and non-reduced closed schemes.
The equations remain well-typed in each case; no nonempty or nonzero assumption is
introduced.  A primed naturality object must satisfy its own support vanishings because
its normalized inverse is used in `theta'`.

Searches made:

- `msearch.py ... leanfinder 'normalized reconstruction of a module sheaf from two successive open closed support conditions with adjunction transpose'`: eight hits, all generic sheafification or Zariski restriction formulas; no complete theorem.
- `msearch.py ... loogle 'SheafOfModules, ringSheafAdjunction, extensionByZero, IsIso'`: zero hits for the combined notion.
- `msearch.py ... grep 'supported.*reconstruction|ringSheafAdjunction|extensionByZero' Mathlib/AlgebraicGeometry`: no Mathlib match.
- `rg` over `WeilConjectures/` and the shared `lean/Sheaf` tree for the item id, support reconstruction, and the ringed operations: only the generic published ringed/open-closed infrastructure was found; no declaration of this two-stage normalized theorem.

## Statement corrected

The original statement omitted the domain scheme of `k : X\\setminus i(Z) ↪ X` and did
not state the complement equality needed by the open-closed theorem.  It also quantified
`A'` in naturality without its two support vanishings, although `theta'` uses the inverse
of its normalized lambda.  The node now introduces `K`, records `hk` and `hu`, and adds
`hK'` and `hB'` to the naturality clause.  The sole citer is
`lem-sfb-locally-closed-extension-coherence`; it constructs `K = X\\setminus Z` and
applies the lemma to objects satisfying both vanishings, so its use still holds.

## Dependency modules

- `def-weil-pbc-proetale-site`: the prior derived-category abbreviation was unusable for
  the site's notion.  Its copied lean record now binds Mathlib's
  `AlgebraicGeometry.Scheme.ProEt` and records the repair note.
- `def-weil-proetale-inverse-image`: the prior finite-coefficient realization was
  unusable for arbitrary ring sheaves.  Its copied lean record now binds
  `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage` and the corresponding sheaf
  inverse-image/adjunction declarations.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: the prior completed-pullback
  specialization was unusable.  Its copied lean record now binds the published
  `AlgebraicGeometry.ProEtale.ringSheafAdjunction` and open adjunction.

The prescribed `scompile.py` compile of the delivered module exited 0 with no errors or
warnings.  No Lake build, global build, or direct repository mutation was used.

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
