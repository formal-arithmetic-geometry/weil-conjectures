## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeFibreTopology` states
`AlgebraicGeometry.AlgebraicSpace.schemeFibre_point_homeomorphism`. Its only proof is
`sorry`. No definition, axiom, extra hypothesis, new DAG node or dependency repair is added.
The item's natural-language statement and dependency lists are unchanged.

Hypothesis and clause correspondence:

- A scheme T: `{T : Scheme.{u}}`, with the universe `u` explicitly declared and
  `set_option autoImplicit false`.
- An algebraic space X over T and its structure morphism: `(X : AlgebraicSpace T)`.
  These are the recorded fppf sheaves on schemes over T. The structure morphism is
  already encoded in this base category, rather than introduced as an unrelated map.
- A point t: `(t : T)`; there is no closedness or local-closedness restriction.
- Spec κ(t) with its canonical morphism to T: `Over.mk (T.fromSpecResidueField t)`.
  The recorded Mathlib definition of `fromSpecResidueField` has domain
  `Spec (T.residueField t)` and is induced by the stalk residue map.
- The sheaf fibre product X_t: `X.obj.obj ⨯ yoneda.obj
  (Over.mk (T.fromSpecResidueField t))`. This is a categorical product of presheaves
  ON SCHEMES OVER T, not an absolute product of spaces. On this category h_T is
  terminal, so the product is precisely X ×_{h_T} h_{Spec κ(t)}. Limits of sheaves
  are computed in presheaves. Thus the displayed presheaf is the underlying presheaf
  of the required sheaf fibre product; no choice of a product model or extra
  representability hypothesis is used. The imported fibre-product closure theorem
  guarantees algebraicity, while `Point` and its topology apply directly to the
  underlying presheaf, as their dependency nodes specify.
- Point spaces with the existing atlas topology: `Point` with
  `pointTopologicalSpace` on both presheaves.
- The inverse image |f|^{-1}({t}): the subtype
  `{x : Point X.obj.obj | ∃ p : PointRepresentative X.obj.obj,
    Quot.mk _ p = x ∧ p.base (IsLocalRing.closedPoint p.K) = t}`.
  Each field spectrum has one point. Passing to a common field preserves its image
  in T, so this membership condition says exactly that the structural image of x
  is t. The existential merely spells out the inverse image on the already defined
  quotient; it does not choose a representative or define another point set.
  The subtype's inferred topology is the subspace topology.
- Homeomorphism onto that inverse image: the existential `e : ... ≃ₜ ...`.
- The homeomorphism is THE PROJECTION: for every field-valued representative p,
  `(e (Quot.mk _ p)).val = Quot.mk _ (p.map (prod.fst ...))`. Since every quotient
  point has a representative, this specifies the first product projection on every
  point. It rules out merely asserting existence of an unrelated homeomorphism.
- Connectedness: the explicit `PreconnectedSpace ... ↔ PreconnectedSpace ...`.
  This expresses connectedness without imposing nonemptiness, so it includes the
  empty-fibre case. Together with the next clause it also gives equivalence of
  Mathlib's `ConnectedSpace`, which includes nonemptiness in its definition.
- Nonemptiness: the explicit `Nonempty ... ↔ Nonempty ...` for the same two spaces.
- Absence of separation, quasi-compactness, finite type and Noetherian assumptions:
  no such predicate occurs among the binders. No atlas or finiteness datum is fixed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` and `Spec.map` (recorded def-pc-scheme and
  def-weil-affine-spectrum). Reexported through the imported dependencies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`, and
  `IsAlgebraicSpace` (def-trf-algebraic-space). Reexported by PointTopology.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` and `Scheme.fromSpecResidueField`
  (def-weil-residue-field). The same module gives the proof input
  `Scheme.SpecToEquivOfField`,
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, and
  `Scheme.fromSpecResidueField_apply`
  (the Mathlib match of lem-weil-pbc-morphism-from-spec-field).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` (lem-trf-space-fibre-products-etale-covers).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`
  (def-a1-space-point-topology).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  `PointRepresentative.Rel`, `Point`, `schemePointMap`
  (def-a1-algebraic-space-point-classes). Publicly reexported by PointTopology.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`:
  `exists_affine_etale_cover_and_point_topology`
  (lem-a1-space-affine-etale-cover), imported as a proof dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`:
  `point_open_calculus` (lem-a1-space-point-open-calculus), imported as a proof
  dependency. Its general `mapPoint` is not copied or redefined: the main
  theorem specifies the projection through the already recorded representative map.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField` and `fiberHomeo` (def-pc-scheme-fibre), imported as
  a proof dependency.
- Mathlib categorical binary products and topological connectedness supply the
  standard product, its first projection, the homeomorphism type and
  `PreconnectedSpace`; no private counterparts are introduced.

Source checked: `literature/stacks-project/decent-spaces.tex`, the entire statement
and proof of `lemma-topology-fibre` (Tag 0AC8). For a scheme target take the identity
atlas of T: the residue-field monomorphism has singleton source and is
quasi-compact; the result has no finiteness or separation hypothesis on X or T.
The theorem docstring retains all four proof steps of the node: base-changed atlas
and scheme-fibre comparison; surjectivity and common-field injectivity;
explicit openness using |p|(O) intersected with the fibre; and consequences.

Edge cases checked before writing:

- Empty fibre: both point spaces are empty; preconnectedness and nonemptiness
  equivalences remain valid and no `Nonempty` assumption is present.
- Empty X: the same argument applies; no atlas index is assumed nonempty.
- Empty T: no t exists, so the quantified theorem is vacuous, as is the node.
- Generic or non-locally-closed t: `fromSpecResidueField` is defined for every
  point and the inverse-image subtype imposes no local-closedness condition.
- Non-quasi-compact, non-separated or non-Noetherian X/T: the binders impose
  none of these conditions; the atlas argument uses open surjections, not compactness.
- Arbitrary scheme universe u: fields, schemes and test schemes retain the
  dependency convention `Type u`, and point quotients are in `Type (u + 1)`.

Searches for an existing statement:

- `msearch.py ... leanfinder "An algebraic space over a scheme has point space of
  its residue field fibre homeomorphic to the inverse image of the base point"`:
  eight hits, all scheme residue-field/fibre results; no algebraic-space result.
- `msearch.py ... loogle '"fiberHomeo"'`: six hits, the three scheme fibreHomeo
  declarations and three unrelated fibre-bundle/covering results.
- `msearch.py ... grep 'fiber.*[Hh]omeo|fibre.*[Hh]omeo' AlgebraicGeometry`:
  eleven hits, all the scheme fibre theorem and its uses.
- `rg -n 'fiberHomeo|fibreHomeo|scheme.fibre.topology|schemeFibre'` on the named
  project source trees: scheme fibreHomeo uses and unrelated profinite fibre
  homeomorphisms; no version of this algebraic-space result.
- `rg -n 'lem-sfb-space-scheme-fibre-topology' lean/WeilConjectures`: no hit.
- Read the point classes, topology, affine atlas, point calculus, fibre-product,
  ProperCurveModuli and atlas comparison source interfaces. None states the
  scheme-target algebraic-space fibre homeomorphism. The generic scheme theorem
  cannot be recorded as an exact match since X need not be a scheme.
- Searched the proposed full declaration name in `dag/lean_names_upstream.json`,
  Mathlib, WeilConjectures and Sheaf: no duplicate.

No statement fault or STATEMENT-DISPUTED flag was found. No new nodes or dependency
modules are needed: the main declaration uses existing constructions directly.

## Second reading by Q50

This is the same worker's final source-to-signature check; the dispatched worker
brief assigns the independent reading to the maintainer, and prohibits starting
other agents. It is not claimed as an independent agent review.

Re-read the node and the full delivered signature. Confirmed the scheme/space/point
binders; terminal-base interpretation of the existing product; the residue-field
morphism; representative description of the full inverse-image subset; subspace
and atlas topologies; the canonical first-projection equation; connectedness
including the empty-space convention; and nonemptiness. No mathematical statement
was changed. During compiler repair the first product projection's object arguments
were changed to the named implicit binders `(X := ...)` and `(Y := ...)`.

Validation: `scompile.py Q50 lem-sfb-space-scheme-fibre-topology <module>`
passed both sandbox and library-mode per-file compilation, with no errors or warnings.
