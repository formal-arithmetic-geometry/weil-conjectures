## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ClosedPointAffineLocalModel` states
`AlgebraicGeometry.IsIntegralCurve.closed_point_affine_local_model`, with its whole
proof postponed by `sorry`. It introduces no definitions and changes only `lean`
in the item's node. The node and source are consistent; no correction or disputed
statement is needed.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the scheme and its named structure map are
  `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. `[IsIntegralCurve f]` is the recorded
  dependency predicate: it extends integral variety (separated, locally finite
  type and quasi-compact) and says `topologicalKrullDim X = 1`. This agrees with
  dimension via local rings by the recorded `Scheme.dim_eq_topologicalKrullDim`.
- The point is `(x : X)` and its closedness is `hx : x ∈ closedPoints X`, which
  unfolds to closedness of its singleton.
- Existence of an affine neighbourhood is the first conjunct
  `∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U`.
- The second conjunct quantifies over *every* `U`, `hU : IsAffineOpen U`, and
  `hxU : x ∈ U`, not only a chosen affine chart. Its section ring is literally
  Mathlib's `Γ(X, U)`. Its structural map from k is
  `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
  X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom`.
  This is pullback of global constants followed by restriction to U.
- `RingHom.FiniteType` on this map and `IsNoetherianRing Γ(X, U)` are the first
  two clauses for every affine neighbourhood.
- `hU.fromSpec` is the canonical immersion from `Spec Γ(X,U)` onto U.
  The clause `∀ q, hU.fromSpec q = x ↔ q = hU.primeIdealOf ⟨x, hxU⟩`
  states both existence (take the displayed canonical prime) and uniqueness of
  the prime over x. The next conjunct says its ideal `IsMaximal`.
- The localization is exactly `Localization.AtPrime` of that prime ideal.
  `IsNoetherianRing`, `IsLocalRing`, `IsDomain`, and `ringKrullDim ... = 1`
  state its four required properties. The next four conjuncts state the same
  properties for `X.presheaf.stalk x`. The already available local-ring
  instances are conclusions explicitly requested by the node, not hypotheses.
- The existential `e : Localization.AtPrime ... ≃+* X.presheaf.stalk x`
  is characterized by `e.toRingHom.comp (algebraMap Γ(X,U) ...) =
  (X.presheaf.germ U x hxU).hom`. Thus the map is the one induced by germs,
  not an arbitrary ring isomorphism. On a fraction r/s its value times the
  germ of s is the germ of r. Since s is outside the corresponding prime,
  its germ is a unit, and this is exactly r_x s_x^{-1}. This characterizing
  equation is equivalent to the displayed fraction formula in the node.
- The next clause, `∀ c : k, ...`, says e carries the image of the restricted
  structural section c in the localization to the structural germ at x.
  These are precisely the two structural k-algebra maps. A ring isomorphism
  between local rings is automatically local, so this states an isomorphism
  of local k-algebras without choosing a second Algebra instance.
- Mathlib's `IsLocalRing.ResidueField.mapEquiv e` is literally the residue
  isomorphism induced by e, with domain definitionally the prime's
  `Ideal.ResidueField` and codomain `X.residueField x`. The last ring-map
  equality says its composite with the structural k-to-residue map is
  `f.residueFieldAlgebraMap x`. Thus it is an isomorphism of field extensions
  of k, not merely of abstract residue fields.
- There is no normality, smoothness, perfectness, or separability hypothesis.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs).
- `AlgebraicGeometry.IsVariety`, `AlgebraicGeometry.IsIntegralCurve`
  (WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective).
- `AlgebraicGeometry.Spec`, `Spec.map` (Mathlib.AlgebraicGeometry.Scheme).
- `AlgebraicGeometry.IsOpenImmersion` (Mathlib.AlgebraicGeometry.OpenImmersion),
  used through the canonical Mathlib affine immersion `IsAffineOpen.fromSpec`.
- `RingHom.FiniteType` (Mathlib.RingTheory.FiniteType), the recorded ring-map
  version of `Algebra.FiniteType`.
- `IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs).
- `Localization.AtPrime` (Mathlib.RingTheory.Localization.AtPrime.Basic) and
  `Ideal.ResidueField` (Mathlib.RingTheory.LocalRing.ResidueField.Ideal).
- `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`
  (Mathlib.AlgebraicGeometry.ResidueField); the structural coefficient map is
  the existing `Scheme.Hom.residueFieldAlgebraMap` (WeilConjectures.ZetaSeries).
- `ringKrullDim` (Mathlib.RingTheory.KrullDimension.Basic).
- `closedPoints` (Mathlib.Topology.JacobsonSpace).
- `PresheafOfModules.moduleStalkFunctor`
  (WeilConjectures.Topology.PresheafModuleStalkFunctor) is the recorded
  general module-stalk dependency, imported directly. Its underlying ring
  stalk and germs here are Mathlib's `TopCat.Presheaf.stalk` and `germ`;
  no second module-stalk construction is introduced.

The module also imports all recorded proof dependencies with available modules,
using plain imports for those used only in the proof plan. In particular these
include `dimension_locally_algebraic`, `Scheme.dim_eq_topologicalKrullDim`, and
`finiteType_domain_ringKrullDim_eq_trdeg` from their recorded WeilConjectures
modules. Mathlib proof leaves are imported from AffineScheme, Properties,
Morphisms.FiniteType, OpenImmersion, RingTheory.FiniteType,
Spectrum.Prime.Topology, Geometry.RingedSpace.LocallyRingedSpace, and
Topology.KrullDimension. The declaration docstring reproduces all seven proof
steps, including the dimension convention bridge and scalar compatibility.

Edge cases checked mathematically before drafting:

- The empty scheme cannot satisfy integral-curve dimension one or supply x;
  the empty affine open cannot satisfy hxU. No separate nonemptiness assumption
  was added.
- The generic point of an integral one-dimensional curve is not closed and is
  correctly excluded: its stalk would have dimension zero.
- The cusp at its singular closed point has a nonregular/non-normal local
  domain of dimension one and is included, as required.
- Arbitrary imperfect fields and inseparable closed residue extensions are
  included; none of the ring-isomorphism or dimension conclusions requires
  separability. Nonrational closed points are also included.
- Every universe is explicitly bound. The common universe for k and X follows
  the recorded IsIntegralCurve interface; arbitrary universe levels are allowed.

Searches made for an existing full statement:

- `msearch.py ... leanfinder`: "A closed point of an integral curve over a field
  has an affine neighborhood whose localization is a one dimensional Noetherian
  local domain isomorphic to the scheme stalk". Eight results: domain/fraction
  ring stalk instances and individual stalk lemmas; no combined statement.
- `msearch.py ... loogle`: `"stalk", "ringKrullDim"`. One result,
  `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, not this statement.
- `msearch.py ... grep` in AlgebraicGeometry:
  `stalk.*(AlgEquiv|RingEquiv)|localization.*stalk|ringKrullDim.*stalk`.
  Twenty-five results, including `IsAffineOpen.isLocalization_stalk` and
  `Spec.stalkIso`, but no full local model with coefficient compatibility.
- `rg` in both lean/WeilConjectures and lean/Sheaf for the item id and for
  closed-point affine/local-model and stalk/localization patterns found
  related pieces. `closed_point_affine_dimension_data` chooses one chart and
  includes function-field data; `separable_curve_geometric_local_data` assumes
  finite separable residue fields and a geometric base change. Neither states
  the present result for every chart and without separability. The upstream
  item-id search had no match. No notion was duplicated.

Validation: `scompile.py Q18 lem-sfb-curve-closed-point-affine-local-model` checked
both sandbox and final library module modes successfully (2.3 s and 2.2 s), with
no errors or warnings. All theorem proofs are `sorry`; no definitions are added.

## Second reading by Q18

I reread the node and final file after compilation. This is a self-check by the
single dispatched worker; the maintainer supplies the independent review.
The check matched the named structure morphism and recorded integral-curve
predicate, closed point, affine existence, universal quantifier over affine
neighbourhoods, canonical structural ring map, finite type and Noetherianity,
unique maximal prime, germ-characterized localization isomorphism, its scalar
map, its induced residue isomorphism and scalar map, and all four properties
of both local rings. No mismatch or additional hypothesis was found. In
particular the residue equivalence is `mapEquiv e`, not an unrelated witness,
and the prime equivalence supplies existence as well as uniqueness. No changes
were needed after this reading. The general module-stalk dependency and all
available proof dependencies are imported rather than restated.
