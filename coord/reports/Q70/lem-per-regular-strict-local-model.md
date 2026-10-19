## Worker report

The module `Sheaf.AlgebraicGeometry.RegularStrictLocalModel` states
`AlgebraicGeometry.regular_strict_local_model`, with `sorry` as its only proof.
No definition, auxiliary theorem, new node or dependency replacement is introduced.
The natural statement, proof and proof dependencies remain unchanged. The two already
landed definition nodes for the strict-henselization structural map and point evaluation
are added to statement dependencies because the signature uses their canonical maps.

Hypothesis and conclusion correspondence:

- Schemes `X,Y` are `Scheme.{u}`, with `[IsNoetherian X]` and `[IsNoetherian Y]`.
  Excellence is `∀ U : X.affineOpens, IsExcellent Γ(X,U)` and the corresponding
  condition on `Y`. This uses the recorded excellent-ring predicate directly.
- The given regular morphism is `h : Y ⟶ X`, `[Flat h]`, and `hreg`.
  The latter quantifies over every point `x`, every field `L`, every residue-field
  algebra structure and `[Module.Finite (X.residueField x) L]`, and requires
  `IsRegularScheme` of the base change of `h.fiberToSpecResidueField x` along
  `Spec.map (algebraMap ... L)`. This is precisely regularity of the fibre after
  every finite residue-field extension; there is no finite-type hypothesis on `h`.
- The geometric points are the algebraically closed fields `ΩX,ΩY` and morphisms
  `barX : Spec (.of ΩX) ⟶ X`, `barY : Spec (.of ΩY) ⟶ Y`.
  Their specified map is `e : ΩX →+* ΩY`; `hbar` says
  `barY ≫ h = Spec.map e ≫ barX`. No equality of the two fields is assumed.
- The induced map is the unique `H : strictHenselizationScheme barY ⟶
  strictHenselizationScheme barX` satisfying the displayed properties.
  Its structural square is `H ≫ jX = jY ≫ h`; the next equation retains the
  specified geometric-point map via the canonical point-evaluation maps.
  `IsLocalHom H.appTop.hom` is the local condition on its map of coordinate rings.
  These conditions characterize the induced pointed local map, rather than
  permitting an unrelated morphism between the two strict local schemes.
- Regularity of `H` is `Flat H` together with the same universal finite-field
  fibre-base-change test as `hreg`, now at every point of the base strict localization.
- The next four conjuncts state Noetherianity of both strict local schemes and
  excellence of all their affine coordinate rings.
- The dimension assertion quantifies over **every** `v` of the source strict
  localization. Its left side is
  `ringKrullDim ((H.fiber (H v)).presheaf.stalk (H.asFiber v))`.
  On the right the image `y` is `strictHenselizationStructuralMap barY v`, the
  image `x` is `h y`, and the expression is the stalk of `h.fiber (h y)` at
  `h.asFiber y`. Thus these are the two specified local fibre rings, not the
  dimensions of their entire fibres, or of their ambient local schemes.
- For every scheme `C` and `[IsClosedImmersion i]` with target the base strict
  localization, `pullback.snd H i` is required to be flat and to pass the same
  finite-field regular-fibre test. `pullback H i` and `C` are explicitly both
  Noetherian and excellent. There is no reducedness, nonemptiness or regularity
  assumption on `C`.
- Ordinary localizations are the spectra of the stalks at `y₀` and `h y₀`, with
  their canonical map `Spec.map (h.stalkMap y₀)`. The final conjunct quantifies over
  every `y₀ : Y` and states the analogous regularity, both Noetherianities,
  both excellences, and the equality of local fibre dimensions at every point `v`
  of `Spec (Y.presheaf.stalk y₀)`. The original image is `Y.fromSpecStalk y₀ v`.
  A compatible pair of ordinary points is determined by `y₀`, since its base
  point must be `h y₀`.

Recorded dependency declarations used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (whose definition is
  `IsQuasiExcellent R ∧ IsUniversallyCatenary R`). Excellence is applied to affine
  coordinate rings; no new scheme-excellence predicate is defined.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  defined as local Noetherianity and the upstream stalkwise `IsRegular` condition.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`,
  `fiberToSpecResidueField`, and `asFiber`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and
  `Mathlib.AlgebraicGeometry.ResidueField`: geometric points are the recorded
  inline field/morphism encoding, with `IsAlgClosed`.
- `Sheaf.AlgebraicGeometry.StrictHenselization` (reached through the canonical-map
  imports): `Scheme.strictHenselizationRing` and `strictHenselizationScheme`, the
  existing small pointed-etale colimit and its spectrum. No private construction.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`; and
  `Sheaf.Paper.StrictHenselizationPointEvaluation`:
  `Scheme.strictHenselizationPointEvaluation`. These are the existing structure map
  and colimit evaluation. The structural-map wrapper reuses the published source
  declaration named in the node's current record.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, with values in
  `WithBot ℕ∞`; dimensions are not truncated to natural numbers.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, through
  the existing scheme-stalk localizations. Ordinary scheme localizations are
  `Spec (X.presheaf.stalk x)` and their map is the existing `stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`; the scheme instances are already imported.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` under the recorded
  excellent and regular ring predicates;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` for schemes.

The statement imports expose only its notions. Existing proof dependencies are
imported privately, including the pointed-neighbourhood/triples comparison,
strict-henselization functoriality, Noetherianity, excellence ascent, regular local
maps, smooth filtered colimits, separable fibre decomposition, regular composition
and base change, fibre stalk quotients, tensor maps, flatness, and the height formula.
The docstring follows all ten natural proof steps, including the quotient calculation
for closed base change. Uniqueness is the pointed-etale lifting uniqueness already
used to characterize the induced local map.

Source checks: I read ILO XVII printed pp. 283–285, especially the strict-local
reductions in the project server and the project server, and the regular local strictly henselian setting
of the project server; also Stacks `more-algebra.tex`, definition-regular,
lemma-regular-local (07C0) and lemma-regular-base-change (07C1). The regular-fibre
test is written directly in the scheme formulation used by the node, rather than
assuming an unrecorded equivalence with regularity of stalk ring maps.

Edge cases checked: identity maps and the trivial finite field extension; finite
inseparable extensions are included without a separability assumption. The map
`h` need not be of finite type. Nonclosed `v` are included in both dimension
assertions. Zero-dimensional local fibres have dimension zero in the stated
extended dimension type. Empty closed subschemes are allowed: the pullback is
empty, the universal fibre tests are vacuous and both empty schemes are
Noetherian excellent. Empty original schemes admit no geometric points, so the
strict-local assertion has no instance in that case. The ordinary assertion is
universally quantified over existing compatible points, with no nonempty hypothesis.
All variables and the common scheme/field universe are explicit; finite extensions
are tested in the scheme universe, not in an independently smaller universe.

Searches for an existing statement (the saved search results are in `searches.jsonl`):

- LeanSearch: `regular morphism strict localizations excellent schemes fibre dimension`:
  eight hits about smooth/etale morphisms, none the strict-local regularity and
  dimension statement.
- LeanFinder: `regular morphism induced on compatible strict localizations of excellent
  noetherian schemes preserves fibre local dimensions`: eight localization/smoothness
  and ring-hom-property hits, none the item.
- Loogle: `AlgebraicGeometry.IsRegular, AlgebraicGeometry.Scheme.Hom.fiber`:
  no hits, unknown identifier for the proposed regularity name.
- `msearch.py grep`, `IsRegularMorphism|RegularMorphism|IsExcellentScheme|strictHenselization`
  under Mathlib AlgebraicGeometry: no hits in the recorded search.
- Direct `rg` in pinned Mathlib AlgebraicGeometry for `IsRegularMorphism|RegularMorphism|
  geometrically regular|regular morphism`: no matching regular-morphism API.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` for the node id,
  `regular_strict_local_model` and the regular-morphism names: no declaration of
  this statement. The project contains downstream docstring references in
  RegularDimensionFunctionPullback and RegularSpecializationGeometry, not a
  theorem supplying this local-model assertion. Related divisor-quotient results
  are different statements. Existing definitions of all notions were reused.

No statement correction or disputed assertion is needed. Validation: the final
module is checked by the prescribed single-file `scompile.py` and delivery dry run;
the theorem remains a stage-2 statement with `sorry`.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
