## Worker report

The module `Sheaf.Paper.OrgogozoGoodModification` states
`AlgebraicGeometry.OrientedNearbyCycles.exists_modification_isPsiGood` with the
expected postponed proof. It adds two canonical implementation helpers belonging
to this statement: `orgogozoConstantScalars` is the sheafification unit, after
forgetting commutativity, and `orgogozoModuleSections` restricts scalars along that
unit and packages the same sections and restriction maps as a ModuleCat presheaf.
Both definitions contain actual data; neither invokes a new postponed theorem.
The theorem docstring carries all fourteen DAG proof steps with their references.
The already stated proof dependencies are imported non-publicly.

Hypotheses and clauses, in the order of the node:

- The schemes are `{X S : Scheme.{u}}`; `IsIntegral S` is the recorded integral
  scheme predicate. The Noetherian condition is `IsLocallyNoetherian S` together
  with `CompactSpace S`, exactly the node's locally-Noetherian and quasi-compact
  convention.
- The named morphism is `(f : X ⟶ S)`; `LocallyOfFiniteType f` and `QuasiCompact f`
  together give finite type. There is no separatedness hypothesis on `f`.
- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. This is the
  recorded constructible-sheaf size convention. The nearby-cycle interface uses
  its existing `Coeff.{u, u + 1} Λ = ULift.{u + 1} Λ`, canonically the same ring;
  the lift has the same finiteness and module theory. A finite ring can always be
  represented in this universe; no cardinality bound on the ring is introduced.
- The positive integer is `(m : ℕ) (hm : 1 ≤ m)`; positive integers and naturals
  greater than or equal to one agree. The annihilation condition is
  `hmΛ : ∀ x : Λ, m • x = 0`. Invertibility on the base is
  `hmS : IsUnit (m : Γ(S, ⊤))`, equivalent to invertibility in every local ring:
  local inverses of this fixed global section glue uniquely.
- `(K : EtaleDerived X Λ)` uses the recorded intrinsic derived category.
  `hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff Λ) K` means bounded
  cohomological amplitude for its standard t-structure, as in `isBounded_iff`.
- `hKc` quantifies over every `q : ℤ` and applies the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` to an ordinary small-etale sheaf `F`.
  Its module-linear natural isomorphism identifies the actual q-th homology
  sheaf's constant-scalar sections with
  `(AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj`.
  This is an exact way to say the intrinsic cohomology sheaf is constructible.
  The site equivalence is the existing `AsSmall` transport, and the scalar map is
  the actual unit into the constant sheaf of rings. The comparison is a linear
  presheaf isomorphism, so it preserves the module structure and all restriction
  maps. No arbitrary nearby-cycle comparison is used. Descent along the site
  equivalence and the constant-ring/module-sheaf correspondence makes this
  equivalent to constructibility of the original cohomology sheaf.
- The existential `∃ (S₁ : Scheme.{u}) (r : S₁ ⟶ S) (U : S.Opens)` gives the
  modifying scheme, its morphism, and the open subscheme `U.toScheme` with
  inclusion `U.ι`; this inclusion already has `IsOpenImmersion`.
- `IsProper r` is precisely properness. `Dense (U : Set S)` is density in `S`.
- `IsIso (pullback.snd r U.ι)` says the canonical map from the scheme-theoretic
  inverse image `S₁ ×[S] U` to `U` is an isomorphism.
- `Dense (r ⁻¹' (U : Set S))` is the separate required density of the inverse
  image in `S₁`. It is not inferred from density in `S`.
- The fibre product `X₁` is `pullback f r`; `r_X` is `pullback.fst f r`; `f₁` is
  `pullback.snd f r`. Their commutativity is built into the fibre product.
- The pullback complex is the specified canonical derived inverse image
  `((etaleModules (pullback.fst f r)).pull (Coeff Λ)).obj K`.
- `IsPsiGood (pullback.snd f r) Λ` of this complex is the recorded predicate.
  Unfolding it gives `IsIso` of the ordinary, counit-defined `baseChange` for
  every scheme `S₂` and every morphism `S₂ ⟶ S₁`. Thus the final explanatory
  sentence of the node is included without a finiteness condition on this
  morphism. No second, arbitrary comparison is quantified over.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (and its quasi-compact import):
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. This uses the
  repaired recorded module, with locally closed constructible strata and finite
  module values, rather than the differently defined upstream duplicate.
- `Sheaf.Paper.OrientedNearbyCycles`:
  `AlgebraicGeometry.OrientedNearbyCycles.EtaleSite`, `etaleTopology`,
  `etaleDatum`, `Coeff`, `EtaleDerived`, `IsBounded`, `etaleModules`, `IsPsiGood`;
  also read `baseChange`, `nearbySquare`, and their counit-mate constructions to
  verify the specified map, not just the objects.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  used by the canonical inclusion `U.ι`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- Canonical packaging helpers from Mathlib:
  `CategoryTheory.toSheafify`, `Functor.whiskerRight`,
  `PresheafOfModules.restrictScalars`, and
  `PresheafOfModules.forgetToPresheafModuleCat`.

Edge cases checked: an empty base is excluded by the intended `IsIntegral`
condition; empty `X`, zero complexes and the zero coefficient ring remain
allowed. The case `m = 1` is allowed and forces the coefficient ring to be zero.
The dense open may be the whole base, and an identity modification is permitted.
No integrality, reducedness or nonemptiness hypothesis is imposed on `S₁` beyond
what the stated conclusion itself implies. Arbitrary non-Noetherian test schemes
and morphisms remain in `IsPsiGood`. No bound on the Krull dimension of `S`, no
finite Tor amplitude of `K`, and no freeness of coefficient modules is imposed.

Source check: Lu--Zheng, *Duality and nearby cycles over general bases*, Theorem
4.27(1), printed page 37, read at
https://archive.ymsc.tsinghua.edu.cn/pacm_download/48/9291-1712.10216v7.pdf.
It provides a modification making a bounded constructible complex Psi-good for
finite-presentation maps and Noetherian torsion coefficients invertible on the
base. A finite ring is Noetherian, an integral base has one irreducible component,
and finite type over a Noetherian base is finite presentation. The node is exactly
this specialization. No statement correction or disputed statement is needed.

Searches for an existing statement:

- `msearch.py Q113 lem-trf-orgogozo-good-modification leanfinder` with query
  "A proper modification of an integral Noetherian scheme makes nearby cycles of
  a bounded constructible complex commute with every base change": eight hits,
  about proper base change and finite-type factorization; no theorem of this
  statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, AlgebraicGeometry.IsIntegral"`:
  one unrelated commutative-monoid-object hit, no good-modification theorem.
- `msearch.py ... grep "Orgogozo|IsPsiGood|nearby.?[Cc]ycle"`: zero Mathlib hits.
- `rg -n "orgogozo|good modification|Psi.good|IsPsiGood|modification"` in the
  upstream `WeilConjectures` and project `lean/Sheaf`: ordinary modifications
  and the recorded `OrientedNearbyCycles.IsPsiGood` definition; no existing
  theorem asserting this modification.
- `grep -rn "lem-trf-orgogozo-good-modification"` in upstream
  `WeilConjectures`: no hits.

The generic `CategoryTheory.constantRingModuleRestrictionPresheaf` in
`Sheaf.CategoryTheory.ConstantRingModuleSheaves` and the ordinary-site
`Scheme.etaleConstantModuleRestriction` in
`Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence` were also read.
They take modules over the RingCat-valued constant sheaf on their original site.
Here the dependency gives modules over the forgotten CommRingCat-valued constant
sheaf on the transported `AsSmall` site. The helpers only supply that specific
canonical interface, using Mathlib's existing restriction and packaging functors;
they do not define a new constructibility or module-sheaf predicate.
The three new names were also searched in `dag/lean_names_upstream.json`, Mathlib,
upstream `WeilConjectures`, and project `lean/Sheaf`: no existing declarations.

Only the item's `lean` record is changed. The helpers implement the scalar and
site presentation already required by the node; no independent new notion or
dependency repair is introduced.

Validation: the prescribed `deliver2.py Q113 lem-trf-orgogozo-good-modification
--no-push` completed successfully: the module compiles and server preflight passes
(dry-run commit `2a93c9b24d`). Only the expected postponed theorem proof remains.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
