## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveSourceAlterationCriterion` states
`AlgebraicGeometry.projective_source_alteration_criterion`. Its single theorem is
postponed with `sorry`; no definition or auxiliary theorem is introduced. The item
node changes only in `lean`. No statement correction or dependency repair is needed.

Hypothesis and conclusion correspondence:

- A field k is `(k : Type u) [Field k]`. Both schemes are `Scheme.{u}`, with
  `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]` supplying their structure maps.
- Integrality of X and Y is `[IsIntegral X] [IsIntegral Y]`. This includes nonemptiness,
  reducedness and irreducibility, and supplies the generic points and field structures.
- Projectivity of X/k is `[IsHProjective (X ↘ Spec (.of k))]`, the recorded canonical
  upstream finite-projective-space convention. This is not a projective-bundle convention.
- Finite type of each structure morphism is explicitly its `LocallyOfFiniteType` and
  `QuasiCompact` instances. Both parts of both hypotheses remain in the signature,
  including the parts already consequences of projectivity.
- Separatedness of Y/k is `[IsSeparated (Y ↘ Spec (.of k))]`. Its defining field says
  the diagonal is a closed immersion, exactly the specified convention.
- The k-morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`.
- The unconditional conclusions are `IsHProjective f ∧ IsProper f`.
- The conditional portion is `∀ [IsDominant f], ... .Finite → ...`. Dominance is dense
  range of the actual underlying map. The finite ring map is
  `(f.functionFieldMap f.apply_genericPoint_of_isDominant).hom`, the induced generic-stalk
  map k(Y) -> k(X). `RingHom.Finite` is finite-dimensionality for this field extension;
  it neither supplies an arbitrary embedding nor requires separability.
- Surjectivity is `Surjective f`. The dense open is `∃ U : Y.Opens, Dense (U : Set Y) ∧
  IsFinite (f ∣_ U)`. The restriction has exactly source f^{-1}(U) and target U.
- These conclusions, together with the unconditional properness and the two integral
  hypotheses, are exactly the alteration definition spelled out in the node. A duplicate
  alteration predicate is unnecessary.
- Write F for `pullback f (Y.fromSpecStalk (genericPoint Y))` in this report only. The
  source's generic fibre over Spec k(Y) is precisely this pullback: `Y.functionField`
  is definitionally the stalk at the generic point. The theorem contains no local alias
  or `let` binding. The residue-field fibre `f.fiber (genericPoint Y)` is canonically
  isomorphic to F, because the generic stalk is a field. The chosen expression keeps
  the base exactly Spec k(Y) without a second transport definition.
- `IsIntegral F` and `topologicalKrullDim ↥F = 0` render integrality and dimension zero.
  `∃ x : ↥F, (∀ z : ↥F, z = x) ∧ Nonempty (F.residueField x ≃+* X.functionField)` renders
  exactly one point and its residue field k(X). The explicit `↥` coercions ensure that
  dimension and point binders use the underlying type of the scheme pullback.

Recorded statement dependencies read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (class extends CommRing and
  DivisionRing).
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties
  (nonempty and domain section rings on nonempty opens).
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- def-weil-proper-morphism: `IsProper`, `IsSeparated`, `UniversallyClosed`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper, .Separated and .UniversallyClosed.
- def-kun-projective: `IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective, lines 30--41: a closed immersion
  into projective space with a finite coordinate type, followed by the structural map.
- def-weil-closed-immersion: `IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion (closed embedding, surjective stalk maps).
- def-sc-function-field: the arbitrary integral-scheme clause explicitly reuses
  `Scheme.functionField`, Mathlib.AlgebraicGeometry.FunctionField. The node's recorded
  module WeilConjectures.AlgebraicGeometry.FunctionField is imported and its full
  docstring read; `functionFieldOfComponents` is its general component-product clause.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs; here the actual induced
  map is used through RingHom.Finite, which uses its canonical module structure.
- def-weil-finite-integral-morphism: `IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite (affine with finite affine-section maps).
- def-weil-surjective-morphism: `Surjective`,
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.
- def-weil-open-immersion: `IsOpenImmersion`, Mathlib.AlgebraicGeometry.OpenImmersion;
  the open subscheme and restriction notation use this interface.

Additional existing interfaces: `Scheme.Hom.functionFieldMap` in
WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback, lines 60--67, is defined for
arbitrary integral schemes, despite its module path. It is the generic stalk map after
identifying the image generic point. `apply_genericPoint_of_isDominant` in the publicly
imported WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree, lines 687--695, supplies
that equality from dominance without dimension or flatness assumptions.
`Scheme.fromSpecStalk` is Mathlib.AlgebraicGeometry.Stalk; `Scheme.residueField` is
Mathlib.AlgebraicGeometry.ResidueField; `topologicalKrullDim` is
Mathlib.Topology.KrullDimension. All universes and variables are explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are both disabled.

Proof-dependency imports: the module imports the recorded modules for
lem-kun-projective-implies-proper (`hProjective_properness`),
lem-sbc-finite-affine-tensor-base-change (`Scheme.finite_affine_tensor_base_change`),
lem-sbc-affine-fibre-sections-tensor (`affine_fibre_sections_tensor`),
and lem-trf-proper-finite-fibre-finite-near
(`exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, Mathlib's Tag 02UP).
The other Mathlib matches are exposed by the appropriate imports:
`functionField_isFractionRing_of_isAffineOpen`, open-immersion base change,
`IsLocalization.tensor`, localization/domain and spectrum irreducibility,
`FiniteDimensional.exists_mul_eq_one`, `fieldOfFiniteDimensional`, `Scheme.Hom.fiber`,
`Scheme.Hom.fiberHomeo`, and `Spec`. `lem-sfb-finite-constant-projective-graph` has no Lean
record or Mathlib match in the read clone; its future proof-only import is omitted,
as authorized for an unstated proof dependency. It is not needed to type this statement.

Source reading: literature/stacks-project/morphisms.tex, lemma-locally-projective-proper
(Tag 01WC), lines 10579ff; lemma-generically-finite (Tag 02NW), lines 13191ff, including
its extra quasi-compact/quasi-separated hypotheses for conclusion (4). The present proper
map meets those hypotheses. literature/stacks-project/varieties.tex,
item-dimension-irreducible-trdeg (Tag 0B1C), lines 3811ff. The proper finite-fibre
neighbourhood result is also read in Mathlib.AlgebraicGeometry.ZariskisMainTheorem,
lines 404--418, tagged 02UP. The theorem docstring includes all six DAG proof steps and
names their supporting nodes, including the affine localization proof of the singleton
integral generic fibre.

Edge cases checked before writing: integral excludes empty X and Y by definition, as it
should; no dimension-one condition occurs, so Spec of a finite field extension and
arbitrary dimension-zero integral schemes are included. The identity map is included.
Purely inseparable finite extensions give Spec L over Spec K and satisfy the conclusion;
no geometric reducedness or separability is asserted. A nondominant constant map from a
positive-dimensional projective scheme still has the unconditional projectivity and
properness conclusions; its conditional conclusions are not asserted. No characteristic,
perfectness, algebraic closure, smoothness or normality assumption appears. The dense open
cannot be empty since Y is integral and nonempty. Its being the whole target is allowed.

Searches actually run (Q32/item, msearch.py):

1. leanfinder: "A morphism from an integral projective variety to an integral separated
   variety is projective and proper, and a finite extension of function fields makes it
   an alteration with one-point integral zero-dimensional generic fibre". Eight results,
   including IsIntegralHom, normalization integrality, rational-map function-field
   constructions and finite_appTop_of_universallyClosed; none states this conjunction.
2. loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite". Nine results,
   including finite implies proper, proper plus affine/quasifinite criteria and the
   exact finite-fibre neighbourhood lemma. None includes projective source, the induced
   finite function-field hypothesis and all generic-fibre conclusions.
3. grep: "genericallyFinite|[Aa]lteration|functionField.*[Ff]inite|[Ff]inite.*functionField"
   in AlgebraicGeometry. Three hits, all RationalMap function-field constructions.
4. Direct rg in lean/Sheaf and lean/WeilConjectures for
   `functionFieldMap|functionField.*[Ff]inite|[Aa]lteration|projective_source`, and for
   `class IsHProjective|def IsHProjective`; direct rg for this node id in WeilConjectures.
   No copy of this theorem exists. The searches located the canonical projectivity
   predicate and generic-stalk field map, both reused. Nearby alteration existence
   theorems concern different hypotheses and conclusions.

No STATEMENT-DISPUTED flag: the node is coherent and no false edge case was found.
The requested CompactObject example file is now a withdrawn module with no declarations;
the current module/public-import conventions in brief-stage2 are followed directly.

Validation: scompile.py was run on this delivered file. The first compile found ambiguous
coercion of a categorical pullback in point-type positions; explicit underlying-scheme
coercions repaired that issue. Subsequent compile and delivery checks are recorded below.

Final scompile.py result: sandbox and library module both compile cleanly (2.2 s and
2.1 s respectively), with no errors or unexpected warnings.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
