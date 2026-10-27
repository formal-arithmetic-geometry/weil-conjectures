## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPointAffineDimensionData` states
`AlgebraicGeometry.closed_point_affine_dimension_data`, with its entire proof
`sorry`. There are no new definitions, helper theorems, new nodes, dependency
repairs, or changes to the natural-language statement, dependency lists or proof.
The node copy changes only `lean`. The declaration's docstring carries all six
steps of the node's proof and their sources.

### Hypotheses and every conclusion

- The arbitrary field K is `{K : Type u} [Field K]`.
- The nonempty integral scheme X is `{X : Scheme.{u}} [IsIntegral X]`.
  Mathlib's IsIntegral includes Nonempty X and domain section rings on nonempty
  opens. Nonemptiness is not silently omitted or strengthened.
- Its structural K-scheme morphism is the explicit `f : X ⟶ Spec (.of K)`;
  local finite type is `[LocallyOfFiniteType f]`. No quasi-compactness or global
  finite-type condition is imposed.
- The closed point is `(x : X) (hx : x ∈ closedPoints X)`, exactly closedness of
  its singleton. There is no rationality, separability or algebraic-closedness
  assumption.
- The generic point eta is Mathlib's `genericPoint X`. Its uniqueness on the
  integral scheme makes this equivalent to the node's generic point. The field
  L is `X.functionField`, definitionally `X.presheaf.stalk (genericPoint X)`;
  its field instance comes from IsIntegral. It is the generic stalk itself.
- The affine neighborhood is `∃ (U : X.Opens) (hU : IsAffineOpen U)
  (hxU : x ∈ U)`. The ring A is the actual `Γ(X, U)`, not an independently
  chosen isomorphic ring. `hU.isoSpec` identifies the open subscheme with
  Spec A. `IsDomain Γ(X, U)` includes nonzeroness. `RingHom.FiniteType` of
  `(f.appLE ⊤ U ...).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom` is finite
  generation for its structural K-algebra map, not an arbitrary map.
- The maximal ideal representing x is
  `(hU.primeIdealOf ⟨x, hxU⟩).asIdeal`, with the explicit `IsMaximal` clause.
  By its definition, primeIdealOf is the image under hU.isoSpec.hom;
  `hU.fromSpec_primeIdealOf` identifies its image in X with x. Thus the ideal
  represents the specified point, rather than some unrelated closed point.
- Generic-point membership is the witness `(hηU : genericPoint X ∈ U)`.
- The map A to L is the actual `X.presheaf.germ U (genericPoint X) hηU`.
  `Function.Injective`, `∀ b, b ≠ 0 → IsUnit ...`, and
  `∀ z : X.functionField, ∃ a b, b ≠ 0 ∧ z = germ a * (germ b)⁻¹`
  give exactly the injectivity, inverted nonzero denominators and quotient
  representation requested. The K-algebra compatibility is the following
  `∀ c : K` equality between the germ of the structural section on U and
  the germ of the structural global section.
- The structural K-map on L used in transcendence degree is explicitly
  `(X.presheaf.germ ⊤ (genericPoint X) ...).hom.comp
  (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)`.
  It does not depend on a chosen affine neighborhood or arbitrary algebra.
  The preceding scalar equality identifies its restriction through A.
- The canonical local-ring isomorphism is the existential CommRingCat
  isomorphism `e : U.toScheme.presheaf.stalk ⟨x, hxU⟩ ≅ X.presheaf.stalk x`
  together with `e = U.stalkIso ⟨x, hxU⟩`. The next scalar equation says
  that e sends the germ of each structural constant for `U.ι ≫ f` to that
  for f. A commutative-ring isomorphism between local rings preserves units
  and the unique maximal ideals, so it is local. The scalar equation makes
  it an isomorphism of local K-algebras, rather than only abstract rings.
- The residue comparison is
  `eκ : U.toScheme.residueField ⟨x, hxU⟩ ≅ X.residueField x`, fixed by
  `eκ.inv = U.ι.residueFieldMap ⟨x, hxU⟩`. Thus it is the inverse of the
  canonical residue restriction. The equality
  `∀ c, eκ.hom ((U.ι ≫ f).residueFieldAlgebraMap ⟨x, hxU⟩ c) =
  f.residueFieldAlgebraMap x c` asserts that it respects K. Mathlib's
  `Scheme.Opens.stalkIso_inv` and `Scheme.residue_residueFieldMap` identify
  this map as the residue comparison induced by e, as the node specifies.
- Finiteness of the actual extension kappa_X(x)/K is the explicit
  `@Module.Finite K (X.residueField x) ...
  (f.residueFieldAlgebraMap x).toAlgebra.toModule`.
- The common finite nonnegative integer is `∃ r : ℕ`. `@Algebra.trdeg`
  with the structural map on L equals `(r : Cardinal)`; `ringKrullDim Γ(X,U)`
  and `ringKrullDim (Localization.AtPrime (hU.primeIdealOf ⟨x,hxU⟩).asIdeal)`
  both equal `(r : WithBot ℕ∞)`. These are the requested two dimensions,
  not only the dimension of the scheme or an inequality. The prime instance
  for localization comes from the actual PrimeSpectrum point.

The isomorphism witnesses are fixed to the canonical maps to retain the
canonical clause. Their scalar equations encode the structural K-algebras
without introducing local notation, file-local instances, let binders or a
second definition. All universes and variables are explicitly bound.

### Dependency declarations read and used

Each statement dependency's node statement, recorded lean/mathlib_match, and
its declaration and source docstring were read. Dependencies with status
mathlib need no additional lean record.

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties. Its fields include nonempty and
  component_integral; its irreducible-space instance supplies genericPoint.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType. This is applied to f only.
  The node's additional QuasiCompact notion is not a hypothesis of this item.
- `def-weil-closed-points`: `closedPoints`, Mathlib.Topology.JacobsonSpace.
- `def-sc-generic-point`: `IsGenericPoint`, `genericPoint`,
  `genericPoint_spec`, Mathlib.Topology.Sober.
- `def-weil-pbc-module-stalk`:
  `PresheafOfModules.moduleStalkFunctor`,
  WeilConjectures.Topology.PresheafModuleStalkFunctor, imported as recorded;
  its underlying ring stalks and germs are Mathlib's
  `TopCat.Presheaf.stalk` and `TopCat.Presheaf.germ` used here. This item
  concerns the structural ring stalk, not an independently chosen module.
- `def-kun-transcendence-degree`: `Algebra.trdeg`,
  Mathlib.RingTheory.AlgebraicIndependent.Basic.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme. Chart identification and its represented
  prime use IsAffineOpen.isoSpec and IsAffineOpen.primeIdealOf in
  Mathlib.AlgebraicGeometry.AffineScheme.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  Mathlib.RingTheory.FiniteType. The recorded bare-ring-map interface is
  used directly with the canonical structural ring homomorphism.
- `def-weil-residue-field`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, Mathlib.AlgebraicGeometry.ResidueField.
  `Scheme.Hom.residueFieldAlgebraMap` from WeilConjectures.ZetaSeries
  supplies its existing canonical structural K-map. It is the composite of
  the base field's canonical residue identification and f.residueFieldMap.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  Mathlib.RingTheory.KrullDimension.Basic.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  Mathlib.RingTheory.Localization.AtPrime.Basic. The node also defines
  Ideal.ResidueField and Ideal.Fiber; neither extra object is asserted here.

The proof dependencies with declarations are imported: the Mathlib
functionField_isFractionRing_of_isAffineOpen and affine stalk-localization
interfaces are in the public FunctionField import closure;
finite_of_finite_type_of_isJacobsonRing is in the plain proof import
Mathlib.RingTheory.Jacobson.Ring; finiteType_domain_ringKrullDim_eq_trdeg
is in the plain proof import
WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg.
The six-step proof docstring describes the fraction-field transport needed to
apply the latter's canonical FractionRing form to the actual generic stalk.

### Sources and edge cases

Read local Stacks morphisms.tex, lemma-alteration-dimension (02JX), including
its closed point on the locally finite-type generic fibre and finite residue
extension; lemma-integral-scheme-rational-functions (01RV); and algebra.tex,
lemma-dimension-prime-polynomial-ring (00P0), including its maximal-localization
clause. These confirm the statement as written, with no source correction.

- For X = Spec F with F/K finite, x is its unique closed and generic point,
  m = 0, and both dimensions and transcendence degree are zero. The formula
  includes this case; no positive-dimension assumption appears.
- For A = K[t] and a non-rational maximal ideal, the residue extension need
  not equal K. It is finite, and both dimensions are one. The signature
  requires finite extension, never equality with K.
- Purely inseparable finite extensions are included. There is no perfectness
  or separability hypothesis.
- Empty schemes cannot have the chosen x and are also excluded by IsIntegral;
  x in U makes the chosen chart nonempty. IsDomain excludes the zero ring.
- Non-quasi-compact integral locally finite-type schemes are included: only
  one affine neighborhood is chosen and no QuasiCompact binder is present.
- A nonclosed generic point of a positive-dimensional scheme cannot satisfy
  hx. No assertion about the dimension of every prime localization is made.
- K and X share the ambient universe required to form their scheme morphism
  into Spec K, as in the dependency interfaces. The universe u is arbitrary.

### Searches for an existing whole statement

All service searches used the prescribed msearch.py wrapper with group Q154
and this item. None of the results states the entire affine-data conjunction.

- LeanFinder query: "An integral scheme locally of finite type over a field
  has an affine neighborhood of a closed point with finite residue extension
  and Krull dimension equal to function field transcendence degree".
  Eight hits, including functionField_isFractionRing_of_isAffineOpen,
  functionField, instFieldCarrierFunctionField, stalkFunctionFieldAlgebra,
  and isClosed_singleton_iff_locallyOfFiniteType. These are ingredients only.
- Loogle query: `"functionField", "IsAffineOpen"`. One hit:
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen. Read its
  full signature and the canonical germ algebra in FunctionField.lean.
- Mathlib grep query:
  `functionField_isFractionRing|height_of_isClosed|ringKrullDim.*trdeg`,
  subdirectory AlgebraicGeometry. Four hits, the function-field lemmas and
  Scheme.height_of_isClosed. The height lemma concerns the specialization
  order on the scheme, not the Krull dimension of the local ring.
- LeanSearch query: "A closed point of an integral scheme locally of finite
  type over a field has finite residue field extension and an affine
  neighborhood whose ring and maximal localization dimension equal the
  function field transcendence degree". Eight hits: residueField,
  isClosed_singleton_iff_locallyOfFiniteType, height_of_isClosed, closedPoint
  and related residue-field ingredients. No whole-item match.
- rg over project Sheaf and WeilConjectures for closed-point/affine terms and
  `finiteType_domain_ringKrullDim_eq_trdeg` found the recorded algebra
  theorem and ClosedIrreducibleDimensionTrdeg as ingredients. The latter
  proves global dimension for an irreducible closed subset; it does not give
  this chart, its maximal ideal, both canonical comparisons and all clauses.
- `grep -rn` of the exact node id in WeilConjectures had no match.
  rg of `closed_point_affine_dimension_data`, `ClosedPointAffineDimensionData`
  and the exact node id over Sheaf, WeilConjectures and
  dag/lean_names_upstream.json had no match.

### Validation and previous attempt

The prescribed scompile.py compiled the delivered file separately in sandbox
and library module modes against the server's published build: both clean,
10.3 s and 9.9 s respectively; no error or unexpected warning. The file begins
with module and uses public imports for statement dependencies, plain imports
for proof-only dependencies, and an exposed public section.

The previous BLOCKED text referred to the completed Q112 stage-1 review. The
node has no lean record or reviewed_lean binding, so that review does not
supply a stage-2 statement. The current packet is a new Lean-only stage-2
realization, not a resplit or change to the reviewed proof. There is no
repair note for this item and no mathematical statement fault was found.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
