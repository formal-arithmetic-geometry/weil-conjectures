## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSubschemeFieldStalkTest` states
`AlgebraicGeometry.closed_subscheme_unramified_of_closed_point_field_stalks`.
Its only theorem has proof `by sorry`, with all four DAG proof steps in its docstring.
There are no new definitions, dependency repairs, or statement corrections.
The original statement and all dependency lists are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- Schemes X and Y: `{X Y : Scheme.{u}}`.
- The given morphism X → Spec k: `(f : X ⟶ Spec (.of k))`.
  It is explicit because the canonical recorded residue-field algebra map takes f.
- Locally of finite type: `[LocallyOfFiniteType f]`, without quasi-compactness.
- The closed immersion Y ↪ X: `(i : Y ⟶ X) [IsClosedImmersion i]`.
- The hypothesis only applies to y whose ambient image is closed:
  `h : ∀ y : Y, i y ∈ closedPoints X → ...`.
- The canonical residue quotient is an isomorphism:
  `Function.Bijective (Y.residue y)`. For a morphism of commutative rings,
  bijectivity is precisely being an isomorphism, and this is the actual quotient
  map, not an arbitrary isomorphism between its source and target.
- Its residue field is finite over k:
  `((i ≫ f).residueFieldAlgebraMap y).Finite`. RingHom.Finite means module-finite
  for the algebra structure induced by this homomorphism, hence finite dimensional
  for fields. It does not mean that the residue field is a finite set.
- It is separable algebraic over k:
  `@Algebra.IsSeparable k (Y.residueField y) _ _
    ((i ≫ f).residueFieldAlgebraMap y).toAlgebra`.
  The two anonymous arguments are the inferred commutative-ring structures of those fields,
  not unbound variables. Algebra.IsSeparable includes algebraicity. In particular,
  the algebra structure is explicitly the canonical one from the composite.
- The structure morphism of Y is `i ≫ f`. The conclusion separately includes
  `LocallyOfFiniteType (i ≫ f)` and `IsUnramified (i ≫ f)` as the node requests.
  The latter is the recorded conjunction of local finite type and open diagonal.
- The additional conclusions hold for every point, with no closedness condition:
  `∀ y : Y, i y ∈ closedPoints X ∧ Function.Bijective (Y.residue y) ∧ ...`.
  The final two conjuncts repeat exactly the finiteness and canonical separability
  expressions from h. Thus closedness is asserted in X, not merely in Y.
- Empty Y is allowed: no point, nonemptiness, dimension, separatedness, perfection,
  or quasi-compactness assumptions are present. Every universe and variable is
  explicitly bound; `set_option autoImplicit false` is active.

Dependency declarations read and used:

- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-closed-points`: its Mathlib match is used directly from
  `Mathlib.Topology.JacobsonSpace`, `closedPoints`; membership is IsClosed {x}.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.residue`, and the functorial
  `Scheme.Hom.residueFieldMap`. The already published canonical base-field
  embedding `Scheme.Hom.residueFieldAlgebraMap` is imported from
  `WeilConjectures.ZetaSeries`; it uses the residue-field identification of Spec k
  and that residueFieldMap. No replacement algebra structure or helper is defined.
- `def-weil-pbc-separable-algebraic-extension`:
  `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable`.
- `def-weil-unramified-morphism`:
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`, `AlgebraicGeometry.IsUnramified`.
- Proof dependency `lem-sc-lft-over-field-jacobson-space` is a Mathlib leaf:
  `LocallyOfFiniteType.jacobsonSpace` in the already public FiniteType import,
  with `JacobsonSpace.closure_inter_closedPoints` in JacobsonSpace.
- Proof dependency `lem-weil-pbc-spec-local-ring-canonical-morphism`:
  plain import `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`,
  `AlgebraicGeometry.Scheme.fromSpecStalk_local_properties`, clause (1).
- Proof dependency `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `Spec.map` in Mathlib.AlgebraicGeometry.Scheme, already transitively public.
- Proof dependency `lem-trf-unramified-over-field-local-criterion`:
  plain import `Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion`,
  `AlgebraicGeometry.unramified_over_field_iff_local_criterion`.
  Its exact bijective-residue and canonical extension encoding is used here.

Source check: read varieties.tex lemma-locally-finite-type-Jacobson (0478),
morphisms.tex lemma-unramified-over-field (02G7), and curves.tex
lemma-nodal-lci (0C4E), especially its final paragraph. The closed-specialization
argument agrees with the node: a field local ring admits no proper generalization.

Edge cases checked mathematically before writing:

- Empty Y: the pointwise hypothesis and conclusion are vacuous, and both morphism
  properties hold locally. The statement does not manufacture a point of Y.
- An infinite disjoint union of spectra of finite separable extensions: identity
  closed immersion into itself satisfies the assertion; no finite cover is assumed.
- Dual numbers over k, immersed by the identity: the residue quotient at the
  closed point is not injective, so the hypothesis correctly fails.
- The identity immersion of A¹ over k: the closed-point local rings are not fields,
  so the hypothesis correctly fails; its generic point is not incorrectly included.
- A finite inseparable extension over an imperfect field: the residue map is an
  isomorphism but the separability conjunct fails, as required.
- No separatedness or curve-dimension restriction is needed: the proof is local
  on the ambient affine cover and uses only the closed-immersion image topology.

Searches (2026-10-24; raw launcher search records are in searches.jsonl):

- msearch.py leanfinder query: "A closed subscheme of a scheme locally of finite
  type over a field with finite separable field stalks at ambient closed points
  is unramified and every point maps to a closed point". Eight hits, including
  Algebra.unramifiedLocus, Algebra.isUnramifiedAt_iff_map_eq, and
  AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType. These concern
  algebraic local criteria or a single point; none states this propagation test.
- msearch.py loogle query: `"Unramified", "IsField"`. Two hits:
  Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing and
  Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal. Neither states
  the closed-subscheme result; their hypotheses and conclusions are different.
- msearch.py grep in AlgebraicGeometry:
  `unramified.*(closed|field)|closed.*unramified|isField.*stalk|stalk.*isField`.
  Five hits in Geometrically/Reduced, Properties, and FunctionField. These are
  field-stalk results at generic points, not the requested ambient-closed test.
- msearch.py leansearch query: "A closed subscheme of a scheme locally of finite
  type over a field whose stalks at ambient closed points are finite separable
  fields is unramified". Eight hits on FormallyUnramified, Algebra.Unramified,
  the unramified locus, and the field criterion. None has the requested statement.
- rg searches with the same unramified/closed/field/stalk patterns in
  lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry found
  local criteria and consumers, with no exact match. Exact node-id search in
  lean/WeilConjectures and lean/Sheaf returned no occurrence. Exact proposed
  declaration/module searches in Mathlib, both source roots, and
  dag/lean_names_upstream.json returned no occurrence.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q10

I reread the unchanged node statement against the completed source as a separate
clause-checking pass. This was the same dispatcher worker; no independent worker
was started, as the brief forbids that. The maintainer's independent review remains
separate. The important distinctions checked were: the hypothesis uses closedness
of i(y) in X; the conclusion quantifies over all y; residue is the canonical quotient;
the k-action comes from i ≫ f; finiteness is of the field extension, not the set;
unramifiedness uses the recorded IsUnramified definition; and no quasi-compactness,
dimension, or nonemptiness condition was introduced. The separate locally-finite-type
conclusion is retained even though it is also part of IsUnramified, exactly matching
the two clauses of the node. All four proof steps are present in the docstring and
all stated proof dependencies are available via the imports. No mismatch or change
was found in this rereading.

Validation: scompile.py compiled the module in sandbox mode (4.2 s) and library
mode (1.7 s), with no errors or warnings. Only this node's lean record is changed.
