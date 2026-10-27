## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantPencilGraphModel` states
`AlgebraicGeometry.exists_invariant_pencil_graph_model`. Its only postponed proof is
that theorem's whole `sorry`; its docstring gives all seven DAG proof steps and their
citations. Two real-data helpers name the scalar homomorphism into the generic stalk
and the generic projective-space map in the zeroth chart. They belong to this node's
construction and are recorded in `lean.declarations`. No new independent notion,
dependency repair, or statement correction is needed. Only the node's `lean` changes.

Hypotheses and clauses, read against the unchanged node:

- The field is `(k : Type u) [Field k]`. The scheme and E are `(N : Scheme.{u})`
  `[IsIntegral N]` and the existing `N.functionField`. Its scalar inclusion is
  `invariantPencilFieldConstants f`, obtained by evaluating the structure morphism on
  the canonical `Spec k(N)` point and applying `ΓSpecIso`.
- The named structure morphism is `f : N ⟶ Spec (.of k)`. Projectivity is the upstream
  finite-space `IsHProjective f`; geometric integrality is `GeometricallyIntegral f`;
  finite type is `LocallyOfFiniteType f` and `QuasiCompact f`. Normality is `hN`,
  requiring every actual local ring to be an integrally closed domain.
- The finite group has independent universe `v`, `[Group H] [Finite H]`. `rho` is
  a homomorphism into field automorphisms, `act` into scheme automorphisms. `hact`
  expresses equivariance of the structure morphism, with the inverse in `rho h⁻¹`
  accounting for contravariance of Spec. No faithfulness hypothesis occurs.
- `r : ℕ`, `t : Fin r → N.functionField` and `ht` give precisely the finite
  algebraically independent tuple over the specified scalar inclusion. `hfixed`
  requires the canonical generic-stalk pullback of every scheme automorphism to
  fix every `t i`. Requiring pullback invariance is equivalent to invariance under
  the left field action, since the group contains all inverses.
- P is the existing `ℙ(ULift (Fin (r + 1)); Spec (.of k))`. The ULift merely places
  its finite coordinate type in universe u. `actP` is constrained elementwise to
  `ProjectiveSpace.map` of the scalar automorphism. Thus it fixes the homogeneous
  coordinates and is not an arbitrary action.
- `V : N.Opens`, `Dense (V : Set N)` and the preimage equality for every h express
  the dense invariant open. `actV` restricts `act` via the equality after `V.ι`.
  `v` is equivariant and over k. `etaV ≫ V.ι = N.fromSpecFunctionField` fixes its
  generic point; `etaV ≫ v = invariantPencilGenericMap f t` specifies the original
  rational map. The preimage of the zeroth standard chart is top, so all t_i are
  regular on this V and v is [1:t_1:...:t_r], not just a projective rational map
  with occasional points outside that chart.
- `j` has first component `V.ι` and second component v in the actual fibre product.
  These equations uniquely specify the graph map. Z is exactly `j.image`, the
  recorded scheme-theoretic closure, not an arbitrary closed model.
- The existential integral instance asserts that Z is integral. `p` is constrained
  to `j.imageι ≫ pullback.fst`; `IsIso (p ∣_ V)` is the isomorphism over V. `hp`
  gives the generic-point equality and `eZ.hom = p.functionFieldMap hp` states that
  the actual projection pullback identifies k(Z) with E, not merely that the fields
  happen to be isomorphic.
- X' is exactly `j.image.normalization` and its morphism is the existing
  `j.image.fromNormalization`. Under eZ this is normalization in E. The equations
  for a and b fix the two actual projections through this normalization.
- The local-stalk clause asserts normality of X'. `IsHProjective (a ≫ f)`,
  `GeometricallyIntegral (a ≫ f)`, `LocallyOfFiniteType (a ≫ f)` and
  `QuasiCompact (a ≫ f)` give precisely its remaining scheme properties. Its
  integral instance is explicitly retained in the last existential block.
- `actZ` commutes with both graph-closure projections, hence extends the diagonal
  action on the graph. `actX` commutes with the normalization map and has the
  explicitly stated scalar semilinearity. Both a and b are equivariant.
- `IsHProjective a`, `IsHProjective b` give finite-space relative projectivity.
  `IsProper a`, `Surjective a`, and `IsIso (a ∣_ V)` give the stated geometric
  properties of a. Its birational assertion uses the same dense V and `ha`, `eX`,
  `eX.hom = a.functionFieldMap ha`, so the function-field identification is actual.
- `IsDominant b` and `IsProper b` are literal. The projective-space integral
  instance and `hb` allow its canonical function-field pullback. The equation
  `CommRingCat.ofHom beta = b.functionFieldMap hb ≫ eX.inv` transports exactly
  that map back to E. Its Spec equation is exactly the original generic pencil,
  fixing the coordinate and coefficient maps. Finally `Set.range beta` equals
  `IntermediateField.adjoin k (Set.range t)` with the specified scalar structure.
  As beta is a homomorphism of fields, this identifies k(P) with precisely the
  subfield k(t_1,...,t_r), with its specified inclusion into E.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs); `IsIntegral` (Mathlib.AlgebraicGeometry.Properties).
- `LocallyOfFiniteType` (Mathlib.AlgebraicGeometry.Morphisms.FiniteType), `QuasiCompact`
  (Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact), `IsProper`
  (Mathlib.AlgebraicGeometry.Morphisms.Proper).
- `IsHProjective` (WeilConjectures.AlgebraicGeometry.Morphisms.Projective), the recorded
  upstream finite-coordinate embedding definition; no Sheaf duplicate imported.
- `Scheme.functionField` (Mathlib.AlgebraicGeometry.FunctionField), the arbitrary
  integral-scheme clause of def-sc-function-field, imported also through the recorded
  WeilConjectures.AlgebraicGeometry.FunctionField. Its component product is not the
  function field needed for an arbitrary integral N.
- `Scheme.normalization`, `Scheme.fromNormalization`
  (WeilConjectures.Mathlib.AlgebraicGeometry.Normalization), with real relative-normalization data.
- `GeometricallyIntegral` (Mathlib.AlgebraicGeometry.Geometrically.Integral).
- `Scheme.Hom.image`, `Scheme.Hom.imageι` (Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme).
- `pullback`, `pullback.fst`, `pullback.snd`
  (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback).
- `AlgebraicIndependent` and `IsTranscendenceBasis`
  (Mathlib.RingTheory.AlgebraicIndependent.Defs), and `Algebra.trdeg`
  (Mathlib.RingTheory.AlgebraicIndependent.Basic). The item needs independence, not
  maximality or a transcendence basis; it uses the exact recorded basic definition.
- `Scheme.Hom.dominantFunctionFieldAlgebra` (Sheaf.TraceFormula.LocalDimensionFormula),
  and its underlying `Scheme.Hom.functionFieldMap`
  (WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback).
- The chart construction additionally uses the existing `ProjectiveSpace.standardOpenIso`,
  `AffineSpace.homOfVector`, `ProjectiveSpace.map`, `Scheme.fromSpecFunctionField`,
  `Scheme.ΓSpecIso`, and `IntermediateField.adjoin`. These are existing constructions,
  not newly copied definitions. The theorem's proof imports include the recorded
  statement-bearing proof modules and Mathlib leaves. The two presently unstated
  proof tools lem-sfb-equivariant-normal-projective-model and
  lem-sfb-projective-fibre-product-closed-model are not statement prerequisites and
  have no module to import yet.

Edge cases checked: r=0 uses one homogeneous coordinate and an empty family of affine
coordinates; its subfield is the image of k. Nonfaithful and trivial actions are allowed.
The inverse convention works for nontrivial scalar actions. No perfection, characteristic,
separability, transcendence-basis maximality, or dimension hypothesis was introduced.
The empty N is excluded by the given integral/geometrically integral hypotheses; V is
forced nonempty by density in N. Normalization of a geometrically integral finite-type
scheme remains geometrically integral here: its function field is the same regular
extension of k, geometric reducedness follows from the separably generated function
field and the scheme being integral, and geometric irreducibility from the same field.
The scheme and coefficient universe u and independent group universe v retain all cases.

Searches for an existing full statement:

- msearch.py leanfinder: "Invariant rational functions give an equivariant map to
  projective space resolved by normalization of its graph": 8 hits, starting with
  Projectivization.lift and RatFunc.liftOn'; these concern projective points or rational
  function quotients and do not give the scheme construction.
- msearch.py loogle: "AlgebraicGeometry.Scheme.RationalMap, AlgebraicGeometry.ProjectiveSpace":
  tool returned zero hits and unknown identifier AlgebraicGeometry.ProjectiveSpace;
  this invalid query was not treated as evidence of absence. Source searches supply
  the projective-space API above.
- msearch.py grep: `(graph|Graph).*(normaliz|equivariant)|invariant.*[Rr]ational`,
  AlgebraicGeometry: zero hits.
- msearch.py leansearch: "An equivariant rational map to projective space extends on
  the normalization of its graph": 8 hits for RationalMap, toNormalization and related
  constituent results; no full normalized equivariant graph theorem.
- rg across lean/WeilConjectures and lean/Sheaf for the node id, invariant-pencil,
  invariantPencil and semilinear actions found InvariantLocalCurvePencils and
  SemilinearEquivariantChowModification. Their statements are different: the former
  regularizes constants and local pencils; the latter supplies an unspecified Chow
  modification, not the normalized graph with the specified coordinate-field map.
- rg across Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json found none
  of this delivery's three fully qualified declaration names. Dependency declarations
  were opened at their definitions, not inferred from names alone.

Source check: read the current blueprint direct-image proof at literature/blueprint/latest,
which keeps the alteration route. Read de Jong's publisher PDF, Lemma 5.2 proof at printed
p. 613 (https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf), and the cited Stacks
scheme-image/normalization and projective-chart constructions. The delivered statement
keeps the node's extracted graph-construction assertion unchanged. No STATEMENT-DISPUTED
finding remains.

Validation: scompile.py compiled the file in module mode under both its sandbox probe
name and its actual library path, no errors or warnings. The first two elaboration
iterations repaired only explicit argument order and the nonempty-top germ encoding;
they made no mathematical change. Every theorem proof remains sorry and both helper
definitions contain real data. The node's Lean statement is the verbatim theorem signature.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
