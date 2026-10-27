## Worker report

Delivered one theorem, with `sorry`, in
`Sheaf.AlgebraicGeometry.SmoothCurveEmbeddingExtension`:
`AlgebraicGeometry.Scheme.exists_hom_of_smooth_connected_curve_functionField_embedding`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The repository was read only; the prescribed compiler and delivery wrappers handle bookkeeping.

Hypothesis and clause correspondence, checked against the node and source:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The schemes are `(C Y : Scheme.{u})`, equipped with the given k-structures by
  `[C.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`.
- A smooth connected one-dimensional curve is
  `[IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]`.
  The recorded upstream `IsConnectedCurve` extends `IsCurve`, including separatedness,
  local finite type and quasi-compactness, and has connectedness and dimension exactly one.
- The target is `[IsIntegral Y] [IsProper (Y ↘ Spec (.of k))]`.
- `∃ hC : IsIntegral C` supplies integrality as a conclusion before the dependent
  quantification over embeddings. It adds no hypothesis: this is a proved consequence of
  `lem-sc-smooth-connected-curve-local-rings`. Since `IsIntegral C` is a proposition,
  proof irrelevance makes its choice immaterial to the subsequent generic stalk.
  This avoids an additional integral assumption and avoids `let`/`have` in the signature.
- Both function fields are the existing `Scheme.functionField`, the structure-sheaf
  stalk at `genericPoint`. This is the arbitrary integral-scheme clause expressly
  recorded in `def-sc-function-field`, rather than a second definition.
- Every embedding is `∀ (φ : Y.functionField →+* C.functionField)`.
  A unital ring homomorphism between fields is automatically injective. That it fixes
  k is precisely the subsequent equality
  `Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecFunctionField ≫ (Y ↘ Spec (.of k)) =
  C.fromSpecFunctionField ≫ (C ↘ Spec (.of k))`.
  The maps to Spec k are the canonical ones from the supplied structure morphisms;
  there is no arbitrary field-algebra structure or arbitrary comparison map.
  Contravariance and full faithfulness of Spec identify this equality with commutation
  of φ with the embeddings of k in the two generic stalks.
- Existence of the scheme morphism and the generic-point assertion are
  `∃ (F : C ⟶ Y) (hη : F (genericPoint C) = genericPoint Y)`.
- That F is a k-morphism is `F.IsOver (Spec (.of k))`.
- The induced local-ring map is explicitly
  `Y.presheaf.stalkSpecializes (specializes_of_eq hη) ≫ F.stalkMap (genericPoint C)`.
  The specialization transports the generic target stalk along the equality hη;
  it is the identity under that identification. Equality with `CommRingCat.ofHom φ`
  says the induced map is exactly the prescribed embedding.
- The more precise extension identity is
  `C.fromSpecFunctionField ≫ F =
  Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecFunctionField`.
  The upstream `fromSpecFunctionField` is literally `fromSpecStalk (genericPoint _)`.
- The affine clause quantifies over every `(V : Y.Opens) (hV : IsAffineOpen V)
  (_ : Nonempty V)`. The chosen presentation is the canonical `A = Γ(Y,V)`;
  `Y.germToFunctionField V` is the canonical inclusion A → k(Y).
  `Spec.map (Y.germToFunctionField V ≫ CommRingCat.ofHom φ) ≫ hV.fromSpec =
  C.fromSpecFunctionField ≫ F` specifies the factorization through V.
  `hV.fromSpec` is the canonical affine-open immersion; no arbitrary factor is chosen.
- The last conjunct quantifies over `(a b : Y.functionField)` with `b ≠ 0` and
  evaluates the actual transported stalk map on `a / b`, giving `φ a / φ b`.
  In particular it gives the advertised fraction formula for a,b from any affine A
  after the canonical germ inclusion. Ring-map injectivity makes the image denominator
  nonzero. The formula also holds for a=0.
- There is no assumption that C is proper, or that Y is smooth or of dimension one.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs`;
  `IsAlgClosed` (and the algebraic-closure interface) in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`.
- `AlgebraicGeometry.IsCurve` / `IsConnectedCurve`, from
  `WeilConjectures.AlgebraicGeometry.Curve` (def-sc-curves).
- `Scheme.functionFieldOfComponents`, from
  `WeilConjectures.AlgebraicGeometry.FunctionField`, whose docstring directs the
  integral-scheme clause to `Scheme.functionField` in
  `Mathlib.AlgebraicGeometry.FunctionField` (def-sc-function-field).
- `AlgebraicGeometry.IsIntegral` in `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.IsProper`, in `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Scheme.Over` and `Scheme.Hom.IsOver`, in `Mathlib.AlgebraicGeometry.Over`.
- `Algebra` and `algebraMap`, in `Mathlib.Algebra.Algebra.Defs`;
  the equivalent ring-hom formulation of the field extension is used here.
- `IsGenericPoint`, `genericPoint`, `genericPoint_spec`, in `Mathlib.Topology.Sober`.
- `AlgebraicGeometry.Spec` and `Spec.map`, in `Mathlib.AlgebraicGeometry.Scheme`.
- `Scheme.germToFunctionField` and
  `functionField_isFractionRing_of_isAffineOpen`, in
  `Mathlib.AlgebraicGeometry.FunctionField`.
- `Scheme.fromSpecFunctionField`, in
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`, is the existing abbreviation
  for `Scheme.fromSpecStalk (genericPoint _)` in `Mathlib.AlgebraicGeometry.Stalk`.

The already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
(`Scheme.smooth_connected_curve_local_rings`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap`
(`Scheme.exists_hom_of_valuationRing_stalk`),
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
(`Scheme.fromSpecStalk_affine_description`, `fromSpecStalk_local_properties`), and
`Mathlib.AlgebraicGeometry.AffineScheme`
(`Scheme.localRingHom_comp_stalkIso`, `Spec.algebraMap_stalkIso_inv`).
The fraction-field proof dependency is in the public function-field import.

Sources read: `literature/stacks-project/curves.tex`, Tag 0BY1 third proof paragraph,
Tag 0BXY, and `literature/stacks-project/morphisms.tex`, Tag 0BX7 with its proof.
The current blueprint was read under `literature/blueprint/latest/`, specifically the
proof of `det-thm-sf-ctf-stability-direct-images`. The extracted auxiliary statement
and its source are preserved unchanged; this delivery does not revise the unit route.

Edge cases checked before writing:

- Empty C and C=Spec k are excluded by the node's connected dimension-one condition,
  exactly as `IsConnectedCurve` stipulates; empty Y is excluded by integrality.
- C need not be proper: A¹ and the embedding t↦1/t into the function field of P¹
  give the intended extension to P¹. An affine nonproper target would fail, so
  properness is retained on Y.
- Y=Spec k is allowed, with its unique k-embedding; F is the structural morphism.
- No characteristic assumption or separability requirement appears. Frobenius
  t↦t^p over an algebraically closed field, fixing coefficients, is allowed.
- Identity embeddings and affine opens V=Y when Y is affine are included.
- Empty opens are intentionally omitted exactly by `Nonempty V`; every nonempty
  affine open is quantified. No choice of affine presentation restricts this clause.
- Both the zero numerator and every nonzero denominator occur in the fraction formula.
- Arbitrary universe u is bound explicitly. Schemes and the field lie in the usual
  common scheme universe, with no size-sensitive test-object quantification.

Searches made before writing (msearch.py NY lem-sfb-smooth-curve-embedding-extension):

1. LeanFinder: "Every embedding of function fields from an integral proper scheme
   into a smooth connected curve extends to a morphism of schemes".
   Eight hits, principally `Scheme.RationalMap.ofFunctionField`,
   `fromFunctionField_ofFunctionField`, `PartialMap.fromFunctionField`,
   and valuative squares. They construct rational maps or local lifts, not this
   global morphism with the prescribed generic map and affine and fraction clauses.
2. Loogle: `"functionField", "IsProper"`: zero hits.
3. Mathlib grep (AlgebraicGeometry):
   `exists_hom_of_valuationRing_stalk|fromFunctionField_ofFunctionField|ofFunctionField`:
   five rational-map hits, no exact theorem.
4. LeanSearch: "A field embedding into the function field of a nonsingular curve
   extends to an integral proper scheme": eight hits on function-field definitions,
   fraction rings, rational maps and unrelated field embeddings; no exact theorem.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the curve/integrality,
   function-field-map, generic base-map, and valuation-stalk-extension interfaces.
   It found the existing general valuation-stalk extension, the smooth-curve
   local-ring theorem and the upstream generic-point and germ maps, which are reused.
   `rg` for the item's id in WeilConjectures had no hit. The final declaration name
   was also searched in both source roots and `dag/lean_names_upstream.json`: no hit.

Validation: prescribed scompile.py compiled the sandbox and library forms cleanly
(2.2 s and 2.3 s); no errors or non-sorry warnings. All universes and variables are
explicitly bound, with `set_option autoImplicit false` as an additional check.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NY

This is a second source-to-signature pass by the dispatched worker; no other agent was
started, as the assignment prohibits delegation. The maintainer supplies the independent
review. I reopened the node and delivered module and checked every binder and conjunct.

The main potential mismatch was adding `[IsIntegral C]` as an assumption merely to type
its function field. The delivered signature instead concludes `∃ hC : IsIntegral C`
and quantifies the embeddings in its scope; class evidence is inferred directly without
`letI`. Smooth connected one-dimensional C already has that property by the recorded
local-ring theorem. This preserves every curve covered by the original statement.

The k-embedding condition is a canonical spectrum diagram, not an assumption of any
additional geometric property; it is exactly commutation with k. The local-ring-map
conjunct includes transport from η_Y to F(η_C), so it has the specified domain, rather
than silently using the stalk at a different point. The affine factorization quantifies
over all nonempty affine opens, and the fraction formula is stated for the actual stalk
map. These clauses were included explicitly rather than only mentioned in a docstring.
The target can have any dimension or singularities and the curve need not be proper.
No changes to the natural-language statement, dependencies, or proof were necessary.
