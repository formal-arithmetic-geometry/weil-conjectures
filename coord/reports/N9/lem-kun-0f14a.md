## Worker report

Repaired the returned H3 defect in `Sheaf.EtaleCohomology.KunnethOneProper`,
`AlgebraicGeometry.Etale.isIso_kunneth_one_proper`. Its conclusion now reads
`IsIso (AlgebraicGeometry.Etale.kunnethMap …)`, with the canonical pullback
projections, both structure morphisms, the composite structure morphism,
and its two commutativity proofs supplied explicitly. The previous
`Nonempty (_ ≅ _)` conclusion did not specify a morphism and was insufficient.
The earlier second-reading text claiming otherwise has been removed; a fresh
second reader must review this repaired version.

Every hypothesis and clause is rendered as follows:

| Node text | Lean |
|---|---|
| Separably closed field `k` | `(k : Type u) [Field k] [IsSepClosed k]` |
| Schemes over `k` | `(X Y : Scheme.{u})` and `aX : X ⟶ Spec (.of k)`, `aY : Y ⟶ Spec (.of k)` |
| `X` proper over `k` | `[IsProper aX]` |
| `Y` quasi-compact and quasi-separated over `k` | `[QuasiCompact aY] [QuasiSeparated aY]` |
| `E ∈ D⁺(X_et)` and `K ∈ D⁺(Y_et)` with integer coefficients | The two `DerivedCategory.Plus (Sheaf … (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))` binders |
| Torsion cohomology of `E` | `hE : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X (DerivedCategory.Plus.ι.obj E)` |
| Product `X ×_k Y` | `pullback aX aY` |
| First and second projections | `pullback.fst aX aY`, `pullback.snd aX aY` |
| Square and composite `c` | `c := pullback.fst aX aY ≫ aX`, the proof `rfl`, and `(pullback.condition (f := aX) (g := aY)).symm` |
| Canonical Künneth morphism of `def-kun-kunneth-map` | `kunnethMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) … (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K)` |
| That very map is an isomorphism | `IsIso` applied to that fully specified morphism |

Integer coefficients are encoded by modules over `ULift.{u + 1} ℤ`, the
universe lift of the initial commutative ring. Every abelian group has a
unique such scalar action and every additive map respects it. This exact
equivalence preserves integer tensor products and boundedness, so these
binders include every abelian-sheaf complex in the node. This is also the
encoding of the published integer proper projection formula
(`lem-kun-0f0f`). It is necessary here because the existing canonical-map
construction has `UpperStarPreservesFlat` available for module coefficients;
there is no extra flatness hypothesis in the theorem. The `torsionCohomology`
predicate is the recorded definition: for each `n : ℤ`, forget the module
action on `Hⁿ(E)` and require `CategoryTheory.Sheaf.IsTorsion`. Thus no uniform
torsion order is assumed, and there is no torsion hypothesis on `K`.

The conclusion uses the canonical map in `D((Spec k)_et, ℤ)`, precisely the
category in which `def-kun-kunneth-map` defines it. This is equivalent to the
displayed global-sections assertion, including the specified map: the
constant-sheaf/sections equivalence over a separably closed point is exact
and tensor compatible. Its derived equivalence preserves and reflects
`IsIso`. Under its tensor identification and the canonical Leray isomorphisms
`RΓ(Spec k, RaX_* E) ≅ RΓ(X,E)`, `RΓ(Spec k, RaY_* K) ≅ RΓ(Y,K)`, and
`RΓ(Spec k, Rc_* T) ≅ RΓ(X ×_k Y,T)`, the image of this adjoint-of-counits
map is the node's `κ`. Its source is therefore
`RΓ(X,E) ⊗ᴸ_ℤ RΓ(Y,K)` and its target is
`RΓ(X ×_k Y, pr₁⁻¹E ⊗ᴸ_ℤ pr₂⁻¹K)`. No endpoint isomorphism is chosen in
place of the map. The framework spells out these identifications in
`Ordinary.lean` (`constantSheafEquivalenceOfIsSepClosed`,
`rightDerivedGlobalSectionsIsoOfIsSepClosed`, and the tensor comparison)
and `GlobalSections.lean`
(`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`).

Dependency declarations and modules read and used:

- `def-kun-kunneth-map`: `AlgebraicGeometry.Etale.kunnethMap` in
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`. Its body takes
  the adjoint of the pulled-back counits, with canonical composition and
  monoidality comparisons. This dependency is now already recorded by Q31
  on the shared DAG, so the obsolete sandbox dependency-record repair was
  removed. No dependency record is redelivered.
- `def-kun-separably-closed`: `IsSepClosed` from
  `Mathlib.FieldTheory.IsSepClosed`; the node also records `IsSepClosure`,
  which this theorem does not need.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-pbc-derived-categories`: `DerivedCategory`,
  `DerivedCategory.Plus`, `DerivedCategory.homologyFunctor`, and
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` through
  `Sheaf.AlgebraicGeometry.DerivedCategories`.
- `def-weil-pbc-torsion-etale-sheaf`: the defining module
  `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf` is imported; its
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf` is the colimit of positive
  integer kernels. The recorded `torsionCohomology` definition uses the
  equivalent standard local-torsion predicate `CategoryTheory.Sheaf.IsTorsion`.
- `def-kun-rgamma-unbounded`: `AlgebraicGeometry.Etale.rightDerivedGlobalSections`
  in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, reached through
  `Ordinary`; this is the total right derived global-sections functor.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor` in
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, reached through
  `Ordinary`; it is the K-flat total derived tensor used by `kunnethMap`.
- `def-weil-pbc-derived-inverse-image`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  reached through the framework. The unbounded derived inverse images
  inside `kunnethMap` restrict to this bounded-below inverse image.
- `def-weil-pbc-scheme-conventions` is metatheoretic and records no new
  declaration; the scheme/morphism binders implement it.

The module includes the modules of all currently recorded proof dependencies
as non-public imports. `lem-kun-kunneth-map-agrees` has no recorded Lean
module, so it cannot yet be imported; its compatibility equation and role
are included in step 7 of the proof docstring. No statement dependency is
missing. The docstring now carries all seven natural-language proof steps,
including the point equivalence, boundedness/torsion checks, proper base
change, projection formulas, Leray, symmetry, and identification of the map.
The sole postponed theorem is `isIso_kunneth_one_proper`, matched to the item
node; no helper definition or theorem has been added.

Edge cases checked: zero complexes and the empty scheme remain allowed;
if either input is zero then the canonical map is the map between zero
objects. The empty product is not excluded. When `X = Spec k`, the assertion
reduces to the constant-complex formula on qcqs `Y`, retaining the torsion
hypothesis on `E`. The homology quantification includes degree zero and all
negative degrees. Orders divisible by `char k` remain allowed: there is no
invertibility or finite-coefficient assumption. The field and schemes use
one universe `u`, while coefficients have the full site-required universe
`u + 1`; the lift of the integer ring restricts no abelian groups.

Searches made for this repair:

- `msearch.py` LeanFinder: “Canonical Kunneth map for bounded below integer
  etale cohomology, one proper factor over a separably closed field, torsion
  cohomology”. Eight hits about cotangent complexes and group cohomology;
  none states the theorem.
- `msearch.py` Loogle: `"kunneth"`. Zero hits.
- `msearch.py` grep: `kunneth|Kunneth` in Mathlib `AlgebraicGeometry`.
  Zero hits.
- `rg` across the upstream project, shared `lean/WeilConjectures`, and
  `lean/Sheaf`, for `kunnethMap`, `kunneth`, `Kunneth`, and
  `isIso_kunneth_one_proper`; also searched the item id. The canonical map
  exists in `Ordinary.lean`, but the existing proper-factor theorem uses
  finite coefficients, finite-type `Y`, and only endpoint isomorphisms;
  the other `isIso_kunnethMap_of_isSepClosed` theorem requires both factors
  finite type and invertible finite coefficients. Neither is this statement.
- Read the current source with `scompile.py --source
  WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` and checked
  the full canonical-map signature/body and point comparisons.
- Opened [Stacks 0F14](https://stacks.math.columbia.edu/tag/0F14), part (1),
  and [Stacks 0F1E](https://stacks.math.columbia.edu/tag/0F1E), the canonical
  adjoint-of-counits construction. They support exactly these hypotheses
  and this canonical morphism.

The item's natural-language statement, statement dependencies, proof and
proof dependencies are unchanged. This repairs the Lean rendering of H3,
so it requires no `statement_change` record. There is no statement dispute.

Validation: `scompile.py` compiled the delivered module cleanly under the
prescribed 60-second limit. `deliver2.py N9 lem-kun-0f14a --no-push` printed
`OK (dry run)` for commit `508ad374ac`: compilation and preflight passed
except for the independent second reading, which the second reader writes.
Nothing was pushed.

## Second reading by N9

I independently read the sandbox node and Lean module, the nine statement-dependency
records and the declarations they name. I read the Stacks TeX at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/etale-cohomology.tex`,
`lemma-kunneth-one-proper`, part (1), with its surrounding section and
`remark-define-kunneth-map` (Tags 0F14 and 0F1E). The source assumes precisely
a separably closed field, a proper first factor and a qcqs second factor;
part (2)'s finite-type and finite-coefficient assumptions do not apply to
part (1). The node specifies the canonical map, so an existence assertion
about an isomorphism between its endpoints would not suffice.

My object/hypothesis/conclusion checklist, matched item by item:

| Node object or clause | Lean rendering and verdict |
|---|---|
| A separably closed field `k` | `(k : Type u) [Field k] [IsSepClosed k]`. Exact: Mathlib's `IsSepClosed` says every separable polynomial splits; it does not demand algebraic closure or a characteristic. |
| Two schemes over that field | `(X Y : Scheme.{u})`, `(aX : X ⟶ Spec (.of k))`, `(aY : Y ⟶ Spec (.of k))`. Exact: these are the specified structure maps, used consistently in the product and map. |
| `X` proper over `k` | `[IsProper aX]`. Exact: the Mathlib class is separated, universally closed and locally of finite type, with quasi-compactness supplied by universal closedness, hence the node's properness. |
| `Y` quasi-compact and quasi-separated over `k` | `[QuasiCompact aY] [QuasiSeparated aY]`. Exact: preimages of compact opens are compact, and the diagonal is quasi-compact. No finite-type, separatedness, Noetherian or properness assumption on `Y` is added. |
| Integer-coefficient `E ∈ D⁺(X_et)` | `E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))`. Exact integer-coefficient encoding, justified below; `Plus` bounds cohomology below, not the terms of an arbitrarily chosen representative. |
| Every cohomology sheaf of `E` is torsion | `hE : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X (DerivedCategory.Plus.ι.obj E)`. Exact: the existing definition quantifies over all `r : ℤ`, takes the homology sheaf, forgets scalars, and requires local torsion. It does not demand one annihilator or that every section group be torsion. |
| Integer-coefficient `K ∈ D⁺(Y_et)` | The analogous `K` binder on `Y`. Exact: its lower bound is independent of `E`'s, and there is no torsion condition on `K`. The placement of `hE` before `K` imposes no further dependency. |
| Product and its two canonical projections | `pullback aX aY`, `pullback.fst aX aY`, `pullback.snd aX aY`. Exact: these use the same two structure maps and the categorical fibre product of schemes. |
| Composite structure map and commutative square | `((pullback.fst aX aY) ≫ aX)`, `rfl`, `(pullback.condition (f := aX) (g := aY)).symm`. Exact: the symmetry has the direction required for `q ≫ aY = c`. These are arguments defining the map, not extra hypotheses or asserted conjuncts. |
| Source `RΓ(X,E) ⊗ᴸ_ℤ RΓ(Y,K)` | The canonical map's source is `RaX_* E ⊗ᴸ RaY_* K` on `Spec k`. Exact under the tensor-compatible point-topos equivalence and the canonical Leray identifications, as checked below. |
| Target `RΓ(X ×_k Y, pr₁⁻¹E ⊗ᴸ_ℤ pr₂⁻¹K)` | The canonical map's target is `Rc_* (Lpr₁^* E ⊗ᴸ Lpr₂^* K)`. Exact under the same equivalence: constant-coefficient étale inverse image is exact, so its derived functor is its termwise descent and gives the node's inverse images. |
| This specified Künneth map is an isomorphism | `IsIso (kunnethMap … (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K))`. Exact: the recorded `def-kun-kunneth-map` supplies this map; no arbitrary map or endpoint isomorphism replaces it. |

For the coefficient check I opened Mathlib's `Grp/ZModuleEquivalence.lean`
(`forget₂AddCommGroupIsEquivalence`), `ModuleCat/ChangeOfRings.lean`
(the equivalence induced by a ring equivalence), and `Ring/ULift.lean`
(`ULift.ringEquiv`). A module over the lift of `ℤ` is exactly an abelian
group with its unique integer action. This equivalence is exact and preserves
the integer tensor product, and its sheaf and complex versions preserve
cohomology and the bounded-below condition. The lift changes size of the
coefficient ring, not coefficients or allowable torsion. This agrees with
the encodings explicitly recorded by `def-kun-derived-tensor` and
`def-weil-pbc-derived-categories`.

For the map check I opened the full signature and body of `kunnethMap` in
the shared `Ordinary.lean` and independently confirmed its current server
source with `scompile.py --source`. The definition is the adjoint of the
composition and tensor comparison followed by the two pulled-back counits,
as in Tag 0F1E and the dependency node. Its section assumptions on the
coefficient category specialize to global instances for `ModuleCat (ULift ℤ)`;
in particular `upperStarPreservesFlat_moduleCat` has no geometric hypothesis.
They do not become extra hypotheses on this theorem. I also opened
`constantSheafEquivalenceOfIsSepClosed`,
`rightDerivedGlobalSectionsIsoOfIsSepClosed`, the tensor comparison in
`Ordinary.lean`, and
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` in
`GlobalSections.lean`. Exact evaluation on the point induces a derived
equivalence, hence preserves and reflects `IsIso`. Under its canonical
tensor and Leray comparisons the image of this very adjoint-of-counits map
is the displayed global-sections morphism. Thus formulating `IsIso` on the
point has neither weakened the conclusion nor lost its specified map.

For the remaining dependency checks, `rightDerivedGlobalSections` in
`LowerShriek.lean` is the total right derived global-sections functor;
`derivedTensor` in `Tensor.lean` is the K-flat derived monoidal tensor;
`mapDerivedCategoryPlus` in `ExactFunctor.lean` is the restriction of the
termwise exact-functor descent, with its inclusion compatibility. I read
`DerivedCategories.lean`'s actual `torsionCohomology` body and
`TorsionEtaleSheaf.lean`'s colimit-of-kernels definition, as well as the
upstream local/stalkwise torsion bridge. Their torsion conditions agree.
The conventions node introduces no separate declaration. All nine
statement dependencies are usable; there is no missing construction,
private replacement, new node, or dependency module in this delivery.

Edge cases: no nonempty scheme or nonzero object is required. Empty `X` or
`Y` gives the empty product and remains covered; zero input complexes are
allowed. Both input bounds may be negative; the torsion quantifier includes
degree zero and all negative degrees. No integer `n` is a parameter, so
`n = 0` is not an omitted case and no uniform positive annihilator is
required. Torsion at the characteristic is allowed in positive
characteristic, as are characteristic zero and nonperfect separably closed
fields. There is no index-set parameter to restrict. `u` is bound and
arbitrary, the schemes and field share the ambient scheme universe, and
the coefficient groups occupy the site-required `u + 1`; smaller objects
can be placed in that common ambient universe. No equality of independently
specified site or coefficient universes is imposed.

Independent H4 searches used wording different from the worker's:

- LeanFinder via `msearch.py`: “Derived etale external cup product over a
  separably closed point with a proper factor and integral torsion bounded
  below complexes”. Eight hits, all about formally étale ring maps or
  cotangent modules; no match.
- Loogle via `msearch.py`: `"kunneth"`. Zero hits.
- LeanSearch via `msearch.py`: “Integral etale Kunneth isomorphism with one
  proper factor and bounded below torsion cohomology”. The service returned
  Internal Server Error, recorded as unavailable; no mathematical verdict
  was inferred from it.
- Grep via `msearch.py`: `external.product|cup.product.*tensor|kunneth`.
  Eleven unrelated simplicial or diagram external-product hits.
- Direct `rg` on Mathlib's algebraic geometry, all upstream
  `WeilConjectures`, the shared `lean/Sheaf`, and the shared canonical-map
  module, using `kunneth`, `künneth`, `external.product`, and theorem-name
  patterns. I opened upstream `Finiteness/Kunneth.lean`'s
  `nonempty_iso_kunneth` and the current `Ordinary.lean`'s
  `isIso_kunnethMap_of_isSepClosed`: their finite coefficient ring,
  invertible exponent and finite-type hypotheses do not cover the present
  integral qcqs assertion. The other hits are tensor Künneth statements
  for complexes, quasi-coherent cohomology, or different six-functor maps.
  There is no exact existing statement to substitute.

I found no remaining mismatch and changed no Lean declaration or node field.
The worker's repair of the earlier arbitrary-endpoint-isomorphism defect is
correct. The module has one theorem, whose entire proof is `sorry`, and no
new definition. Its source/blueprint docstrings carry the seven proof steps:
exact torsion-preserving pullback and properness, point equivalence,
boundedness and proper exchange, proper projection formula, Leray,
constant-complex formula with symmetry, then identification of the
canonical map by the compatibility equation. Every currently recorded
proof-dependency module is imported; the unrecorded compatibility lemma
has its role explained in step 7. No variable or universe is unbound, no
line exceeds 100 characters, and the node's `lean.statement` is verbatim
the theorem signature. The item's other fields agree with the shared node,
so no statement correction or citer audit is needed.

Second-reader validation: `scompile.py N9 lem-kun-0f14a` compiled both the
sandbox check and the delivered module without errors or warnings (24.6 s
and 24.1 s). The prescribed `deliver2.py N9 lem-kun-0f14a --no-push`
printed `OK (dry run)` at `caf91df288`: preflight and compilation passed.
