## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricClosedCurveSmoothModel` states
`WeilConjectures.FiniteFieldDatum.exists_smooth_closed_curve_finiteField_model`.
Its only declaration is a theorem with proof `sorry`. No definitions, additional
nodes, dependency repairs, or statement corrections are needed. All fields of
the item other than `lean` are preserved.

Source read: the current blueprint at `literature/blueprint/latest/blueprint/
sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md`, paragraph 2, together with the item's
seven detailed proof steps. The docstring reproduces those steps and their
named inputs. The source's smooth geometrically connected affine finite-field
curve is retained, and the prescribed geometric closed subscheme is not reduced
or replaced.

Hypotheses and conclusions, in the order of the node:

- Fixed k₀, k and k_m: `D : FiniteFieldDatum.{u}` is the recorded global
  datum. Its `k₀` has q elements, `k` is its fixed algebraic closure,
  `D.extensionSubfield m hm` is the unique subfield with q^m elements, and
  `D.extensionEmbedding m hm` is its specified k₀-embedding.
- X₀ over k₀: `X₀ : Over (Spec (CommRingCat.of D.k₀))`.
  Affineness is `[IsAffine X₀.left]`. Finite type is the recorded conjunction,
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.
- X = X₀ × k: `(D.geometricFiber X₀).left`, with structure map
  `(D.geometricFiber X₀).hom` and first projection `pullback.fst`.
- The prescribed immersion is `i : C ⟶ (D.geometricFiber X₀).left`, with
  `[IsClosedImmersion i]`. The k-structure on C is its composite with the
  ambient k-structure; hence this makes i a k-morphism, as in the node.
- C affine, nonempty, smooth, connected, pure dimension one:
  `[IsAffine C]`, `[ConnectedSpace C]` (which includes `Nonempty C`),
  `[Smooth (i ≫ (D.geometricFiber X₀).hom)]`, and `hC : C.IsPureDimension 1`.
- The model is existentially quantified after `m : ℕ` and `hm : 1 ≤ m` as
  `Cₘ : Over (Spec (CommRingCat.of (D.extensionSubfield m hm)))`.
- Its immersion `iₘ` is a morphism over Spec k_m into
  `(Over.pullback (Spec.map (CommRingCat.ofHom
  (D.extensionEmbedding m hm)))).obj X₀`, with `IsClosedImmersion iₘ.left`.
- Affineness and finite type of the model are `IsAffine Cₘ.left`,
  `LocallyOfFiniteType Cₘ.hom`, and `QuasiCompact Cₘ.hom`.
- Smoothness, geometric connectedness and purity are `Smooth Cₘ.hom`,
  `GeometricallyConnected Cₘ.hom`, and `Cₘ.left.IsPureDimension 1`.
- The comparison is `e : Over.mk (i ≫ (D.geometricFiber X₀).hom) ≅
  (Over.pullback (Spec.map (CommRingCat.ofHom
  (D.extensionSubfield m hm).subtype))).obj Cₘ`. This is an isomorphism
  C ≅ (C_m)_k over k; its inverse has the orientation used in the prose.
- Compatibility of the embeddings is the displayed equality of their
  composites to X₀. Their composites to Spec k agree because e is an
  isomorphism in `Over (Spec k)`. Equality of both pullback projections is
  exactly equality of their maps into X = X₀ × k; thus this retains full
  compatibility with the immersion into X, rather than just into X₀.
- A k-point is `c : Over.mk (𝟙 (Spec (CommRingCat.of D.k))) ⟶
  Over.mk (i ≫ (D.geometricFiber X₀).hom)`, using the recorded field-point
  convention. `c.left (IsLocalRing.closedPoint D.k)` is its underlying point.
  The equality hypothesis for `z : Cₘ.left` says that z is its image under
  `e.hom.left ≫ pullback.fst Cₘ.hom (Spec.map ...)`.
- Closedness is `z ∈ closedPoints Cₘ.left`. Finite residue degree over the
  correct embedded base field is `(Cₘ.hom.residueFieldAlgebraMap z).Finite`.
  This RingHom predicate uses the canonical structure morphism, so there is
  no arbitrary algebra structure or additional residue-field assumption.
- All point quantifiers occur after the existential choice of the same m,
  C_m, i_m and e. This states the node's universal assertion, which applies
  to every member of any prescribed finite set without changing the model.
  An additional finite-set conjunct would duplicate this logical consequence.

Dependency interfaces read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `extensionSubfield`, `extensionEmbedding`, `geometricFiber`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its recorded
  scheme base-change convention is precisely `Over.pullback` / `pullback`
  and their projections, used here; this is publicly imported by FiniteFieldFiber.
- `Mathlib.CategoryTheory.Comma.Over.Basic` / `.Pullback`: `Over`, `Over.mk`,
  morphisms and isomorphisms in Over, and `Over.pullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` including nonemptiness.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, namely
  Krull dimension d of each irreducible component with its subspace topology.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` is the geometric-property
  node's recorded public module; `.Geometrically.Connected` supplies the
  needed `AlgebraicGeometry.GeometricallyConnected` class, which tests all
  field extensions. No private substitute is introduced.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`. `WeilConjectures.ZetaSeries` supplies
  `Scheme.Hom.residueFieldAlgebraMap`, the canonical map from the base field.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`, exactly closed singletons.

Plain proof imports retain the existing proof plan:
`Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent`
(`exists_closed_subscheme_finiteField_descent`),
`Sheaf.AlgebraicGeometry.ClosedPointField`
(`closedPoint_iff_residueField_trdeg_zero_and_finite`),
`Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`
(`geometricallyConnected_iff_connectedSpace_of_isAlgClosed`),
`WeilConjectures.RingTheory.DimensionAtPointComponents`
(`dimension_at_point_components`), and Mathlib's `Morphisms.Flat`,
`Morphisms.LocalFlatDescent`, `Pullbacks`, and `PullbackCarrier`.
Finite-type composition/base-change inputs already enter publicly with the
finite-type interface. `lem-trf-field-extension-component-local-dimension`
has no recorded Lean declaration or Mathlib match in the read repository;
there is consequently no module to import for this proof-only dependency.
Its full mathematical input remains in the theorem proof docstring, and its
DAG record is unchanged. It is not a missing notion needed to type the statement.

Edge cases checked before writing: empty C is excluded exactly by connectedness;
empty X₀ admits no such C and is not separately excluded; no reducedness,
smoothness, connectedness, or integrality of X₀ is imposed. Dimension is purity
of all components, not just total dimension or local-ring dimension. m=1 is
allowed. The set of chosen points can be empty, singleton, repeated in a list,
or any finite set. No point is required to be rational over k_m, and residue
degrees are not bounded by m. In particular on the affine line over k_m there
are closed points of arbitrarily large residue degree; the universal point
clause asserts finiteness individually, not simultaneous rationality.
Geometric k-points cannot map to a transcendental generic point because k/k_m
is algebraic. All schemes and fields use the existing datum's universe u;
there are no independent test-object universes and no auto-bound variables.

Searches for an existing statement (all made through the prescribed tools):

- msearch leanfinder: “A smooth connected affine closed curve over the algebraic
  closure of a finite field descends to a smooth geometrically connected affine
  curve over a finite extension, with closed images of all geometric points”.
  Eight hits: Weierstrass curve point/base-change/integral-model results and
  `isField_of_universallyClosed`; none states this prescribed closed-subscheme
  model with its smoothness, purity, and universal point clause.
- msearch loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.GeometricallyConnected`:
  zero hits.
- msearch grep: `finite.field.*curve|curve.*finite.field|geometric.*closed.*curve.*model`:
  zero Mathlib hits.
- msearch leansearch: “A smooth connected affine curve over the algebraic closure
  of a finite field descends to a smooth geometrically connected model over a
  finite extension”: eight hits, including `Algebra.Smooth.exists_finiteType`
  and general smoothness / Weierstrass model lemmas; no exact theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf` with the same curve/model
  expression: curve compactification, Weil-sheaf and purity infrastructure,
  and the two-point consumer; none gives this prescribed immersion's model.
  `grep -rn` for the item id in `lean/WeilConjectures` returned no hits.
- rg for the chosen theorem name in Mathlib, both project roots, and
  `dag/lean_names_upstream.json`: no collision.

Validation: prescribed scompile.py compiled this file in sandbox and library
module modes without errors or non-sorry warnings. `set_option autoImplicit false`
is also explicit in the delivered module. Final dry-run results are recorded below.

No STATEMENT-DISPUTED issue was found.

## Second reading by NU

A separate self-review pass reopened the node and the full theorem signature;
no second agent was started, following the dispatcher instruction. The maintainer's
independent delivery review remains the independent reading. The clause mapping
above was checked against the signature in order: finite-field datum, affine
finite-type ambient scheme, actual closed immersion, smooth connected affine
pure-one source, positive extension degree, affine finite-type smooth geometrically
connected pure-one model, isomorphism over k, immersion compatibility, and
universal closed finite-degree images. In particular, the comparison was checked
on both X₀ and k projections, and the residue map was checked to come from C_m's
structure morphism. No mathematical mismatch or statement change was found.

Final dry run: `deliver2.py NU lem-zl-geometric-closed-curve-smooth-model --no-push`
returned `OK (dry run): commit bf98dbfd671 passes the preflight and compiles;
nothing pushed`. The module with explicit `autoImplicit false` passed both
sandbox and library compilation. The node diff is exactly the addition of
`lean`, and its recorded signature is byte-for-byte the theorem signature
before `:=` in the delivered file; no Lean line exceeds 100 characters.
