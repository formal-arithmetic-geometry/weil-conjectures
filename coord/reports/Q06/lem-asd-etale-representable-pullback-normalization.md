## Worker report

Item: `lem-asd-etale-representable-pullback-normalization`.
Module: `Sheaf.AlgebraicGeometry.EtaleRepresentablePullbackNormalization`.
The only postponed theorem is
`AlgebraicGeometry.etaleRepresentablePullbackNormalization`. Its proof is `sorry`.
Three helpers in this owning node's module construct the maps and equivalence named
in the statement, using existing Mathlib constructions; no helper contains postponed
proofs or arbitrary choices of a comparison. No node statement or dependency was changed.

Read the complete node, all six statement dependencies and all proof dependencies,
their recorded interfaces, and Stacks `etale-cohomology.tex`,
`lemma-stalk-pullback` (Tag 03Q1), especially (4) and its displayed proof, and
`sites.tex`, `lemma-pullback-representable-sheaf` (Tag 04D3).
Missing local upstream sources were read with `scompile.py --source` from the
published library: `SmallEtaleRepresentablePresheafSheaf`,
`EtaleInverseImageAlgebraicStructures`, and `EtaleSheaves`.

Hypotheses and clauses, individually:

- Arbitrary schemes and morphism `f : X → Y`: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no separatedness, finiteness, flatness, surjectivity or nonemptiness assumption.
- An object `P → Y` of the small étale site: `(P : Y.Etale)`. Its structure morphism
  and étaleness are the data/property of this existing category.
- `P'` and its canonical action on arrows: `(MorphismProperty.Over.pullback @Etale ⊤ f).obj P`
  and the same functor's `.map`. This is the recorded base-change functor, not a new one.
  The Mathlib choice is `pullback P.hom f`, with projection `pullback.snd` to `X`.
  Thus its order is `P ×_Y X`; it is the fibre product `X ×_Y P` in the node via
  the canonical projection-compatible symmetry. This is exactly the convention noted
  in the base-change dependency's `mathlib_match`.
- `h_P` and `h_{P'}`: the existing `smallEtaleTopology.uliftYoneda.{u + 1}.obj`
  on the respective sites. At `W` its sections are `ULift (W ⟶ P)` in the small-site
  category, i.e. scheme morphisms over the base. Mathlib's lifted Yoneda embedding
  includes these presheaves as sheaves, using the existing subcanonical instance.
  `ULift` only embeds the same set into the coefficient universe required by the
  recorded inverse image, `Type (u + 1)`; every arrow, including identities, is retained.
- The inverse/direct-image adjunction: the recorded `Scheme.etaleSetPullback f`
  and `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` on the base-change
  functor. Its right adjoint is `.sheafPushforwardContinuous`; its presheaf is
  literally precomposition by base change, so `(f_*H)(W) = H(b_f(W))`.
  The small topology is written as `smallGrothendieckTopology @Etale` in the adjunction
  arguments, exactly as in the recorded dependency and inverse-image definition;
  `smallEtaleTopology` is its definitional synonym, with no extra continuity hypothesis.
- The specified `beta`: `etaleRepresentableBaseChangeMap f P` is
  `ObjectProperty.homMk (uliftYonedaMap.{u + 1} b_f P)`. Its component maps
  `ULift.up a` to `ULift.up (b_f.map a)`, literally base change of the arrow.
  The full sheaf category wrapper adds no mathematical data.
- The specified adjunct `c`: `etaleRepresentablePullbackComparison f P` is the
  inverse of the existing adjunction's `homEquiv` applied to that exact `beta`.
- `c` is an isomorphism: the first conjunct is
  `IsIso (etaleRepresentablePullbackComparison f P)`.
- The Hom-bijection `Phi_H`: `etaleRepresentablePullbackHomEquiv f P H` is a genuine
  `Equiv`, constructed as adjunction `homEquiv`, then the existing sheaf
  `uliftYonedaEquiv` on `Y`, then the inverse of that equivalence on `X`.
  Those latter maps evaluate at `ULift.up (𝟙 P)` and invert evaluation at
  `ULift.up (𝟙 P')`, respectively, precisely the specified chain.
- Naturality of that bijection in `H`: the second conjunct quantifies over
  `H H'`, `a : f⁻¹h_P ⟶ H`, and `g : H ⟶ H'`, and asserts
  `Phi_H' (a ≫ g) = Phi_H a ≫ g`. Bijectivity is already in the helper's `Equiv` type.
- Identity normalization `Phi_{h_{P'}}(c) = id`: the third conjunct is that equality
  for the same concrete comparison and Hom-equivalence.
- Equivalent unique characterization: the fourth conjunct quantifies over every
  `d : f⁻¹h_P ⟶ h_{P'}` and asserts that its adjunct, evaluated at
  `ULift.up (𝟙 P)`, equals `ULift.up (𝟙 P')` if and only if
  `d = etaleRepresentablePullbackComparison f P`. This includes that `c` itself
  satisfies the identity-section condition as well as its uniqueness.
- Naturality in representing objects: the last conjunct quantifies over every
  `Q : Y.Etale` and `t : P ⟶ Q`, and states
  `f⁻¹(h_t) ≫ c_Q = c_P ≫ h_{b_f(t)}` using the existing lifted Yoneda maps.

Dependency interfaces used or imported for their planned proof:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, underlying the existing base-change functor.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, its full-subcategory
  inclusion and morphisms; no replacement sheaf category was introduced.
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`:
  `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf`, imported as the recorded
  general representability dependency. Since the representing schemes here are objects
  of the site itself, their sheaf objects use Mathlib's existing subcanonical Yoneda
  embedding; it has the same underlying representable presheaves, identified through
  `Scheme.Etale.forgetFullyFaithful`. No new sheaf-condition proof is postponed.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`:
  `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`; its clause (1) uses
  `Scheme.etaleSetPullback` (defined in `WeilConjectures.AlgebraicGeometry.EtaleSheaves`)
  and the concrete constructed set adjunction, used verbatim here.
- `Mathlib.CategoryTheory.Yoneda`: `yonedaEquiv`, `uliftYonedaEquiv`, their naturality,
  and `Coyoneda.fullyFaithful`, the recorded Yoneda and co-Yoneda proof leaves.
- `Mathlib.CategoryTheory.Limits.MorphismProperty`:
  `MorphismProperty.Over.instPreservesFiniteLimitsTopPullback`, the base-change
  finite-limits proof dependency. This proof-only module is imported without `public`.
- `Mathlib.CategoryTheory.Sites.Subcanonical`: `GrothendieckTopology.uliftYonedaEquiv`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `Scheme.subcanonical_smallEtaleTopology`, the existing instance used by the sheaf
  Yoneda embedding. This merely supplies the already-established representable sheaves.

Edge cases checked before writing: `f` may be an identity or any morphism; `P` may be
the identity object or the empty étale scheme; `X` and/or `Y` may be empty. None of these
are excluded by a binder or instance assumption. In particular evaluation at `id_P`
exists even for an empty representing scheme. `H` is an arbitrary sheaf, not assumed
constant, finite or locally constant. The universe lift uses the bijection
`ULift.up/down`, so it neither drops arrows nor forces the site's object and morphism
universes to agree. Base-change symmetry does not change its `X`-scheme structure.

Searches for an existing statement (all 2026-10-17):

- `msearch.py leanfinder`, query "Inverse image of a representable sheaf on the small
  etale site is the representable of its base change; adjoint sends identity to identity":
  eight hits, including `Scheme.Etale.forgetFullyFaithful`, `overMapPullbackId`,
  module pullback unit maps/adjunctions, and `sheafPullbackIso`. None states all the
  normalized representable-comparison clauses for the recorded set inverse image.
- `msearch.py loogle`, query `"sheafPullback", "yoneda"`: zero hits.
- `msearch.py grep`, query
  `sheafPullback.*yoneda|yoneda.*sheafPullback|pullback.*representable|representable.*pullback`
  in `Mathlib/CategoryTheory/Sites`: zero hits.
- `rg` in `WeilConjectures` and `lean/Sheaf` for representable/pullback variants:
  results concerned Picard representation, finite evaluation, free abelian sheaves,
  descent or general infinity-category representables, not this statement.
  `grep -rn` for the exact node id in upstream `WeilConjectures` had no hits.
- `rg` for all four proposed full declaration names in Mathlib, upstream, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no collisions.
- Direct signature/docstring reads in Mathlib's Yoneda, Subcanonical, Pullback,
  Continuous, Scheme, Etale and OverAdjunction modules found the reusable maps
  `uliftYonedaMap`, the sheaf Yoneda evaluation equivalence and the constructed adjunction.
  Those are used directly rather than redefined.

Validation: compiled each delivered file with `scompile.py` only, using the private overlay.
An initial small/unlifted representable mismatch was repaired using Mathlib's existing
`uliftYoneda.{u + 1}`, retaining `Scheme.etaleSetPullback` and all cases.
The final module uses `set_option autoImplicit false` and explicitly binds its universe
and every mathematical variable. The theorem docstring carries all five natural-language
proof steps with their DAG citations. No statement dispute or source defect was found.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
