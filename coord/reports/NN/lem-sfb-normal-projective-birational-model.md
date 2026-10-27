## Worker report

The module `Sheaf.AlgebraicGeometry.NormalProjectiveBirationalModel` states
`AlgebraicGeometry.exists_normal_projective_birational_model`, with its single proof
postponed by `sorry`. It contains no new definition. The node is unchanged except for
its Lean record. No dependency repair or statement correction is needed.

Clause-by-clause correspondence:

- The field is `(e : Type u) [Field e]`; the specified e-scheme S is
  `(S : Scheme.{u}) [S.Over (Spec (.of e))]`. `[IsIntegral S]` includes nonemptiness,
  reducedness and irreducibility. `[IsProper (S ↘ Spec (.of e))]` gives precisely
  properness and the stated finite type: proper includes locally finite type and
  universal closedness, and the latter implies quasi-compactness. No perfection,
  algebraic closure, characteristic, dimension or smoothness hypothesis is imposed.
- `∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (c : Y ⟶ S)` introduces the integral Y and
  the modification c. Its e-structure is `c ≫ S ↘ Spec (.of e)`; in particular c is
  an e-morphism, without any additional unconstrained structure map. The first two
  conjuncts `LocallyOfFiniteType` and `QuasiCompact` are finite type of Y over e.
- `IsProper c ∧ Surjective c` is the proper surjective modification. The existential
  `V : S.Opens` with `(V : Set S).Nonempty ∧ IsIso (c ∣_ V)` is the specified
  nonempty open and the isomorphism of its full inverse image with V. Integrality
  of S makes V dense; integrality of Y and surjectivity make its inverse image
  nonempty and dense. This already renders birationality of c.
- The existential `n : ℕ` and closed immersion i into
  `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of e))` give the finite-dimensional projective
  embedding of Y. The equality for the composite with the structural projection
  makes it an embedding over e. The coordinate type has n+1 elements, as required
  by the recorded convention. ULift only aligns universes.
- N is exactly `Y.normalization` and n_Y is exactly `Y.fromNormalization`, not a
  chosen normal cover or an arbitrary finite map. `IsFinite` and `Surjective`
  apply to this displayed morphism. Its birational clause is a dense target open
  U with dense full inverse image and `IsIso (Y.fromNormalization ∣_ U)`.
- `IsIntegral Y.normalization` includes nonemptiness. For every `x : Y.normalization`,
  the conjunction of `IsDomain (Y.normalization.presheaf.stalk x)` and
  `IsIntegrallyClosed (Y.normalization.presheaf.stalk x)` states normality in
  exactly the node's local-ring sense.
- The existential m and j give the closed projective embedding of this same N;
  the equality with `Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)` makes it over e.
- The two `IsHProjective` conjuncts are H-projectivity of Y and N over e. The two
  `IsProper` conjuncts are their properness. Finite type of Y is explicit near
  the start, and finite type of N is the subsequent `LocallyOfFiniteType` and
  `QuasiCompact` conjunction.
- `IsProper (Y.fromNormalization ≫ c)` and `Surjective` of that same composite
  render properness and surjectivity of c composed with n_Y. Dense opens
  A in N and W in S, with an isomorphism a and
  `a.hom ≫ W.ι = A.ι ≫ Y.fromNormalization ≫ c`, state precisely the dense-open
  definition of birationality for this actual composite.
- The last six conjuncts state that c, n_Y and their composite send the generic
  point of the source to the generic point of the target, and that their
  actual `stalkMap` at that point is an isomorphism. On integral schemes the
  function field is exactly the generic stalk (`Scheme.functionField`), so these
  are the morphism-induced function-field isomorphisms, in the contravariant
  direction. Proof irrelevance identifies the generic-stalk structures for any
  integral-instance witnesses; no independently chosen isomorphism replaces them.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, including its nonempty
  and domain-of-sections fields (def-pc-integral-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed` (def-weil-proper-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`
  (def-weil-surjective-morphism).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the existing
  open subschemes and `morphismRestrict` notation supply the specified opens
  (def-weil-open-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  (def-weil-closed-immersion).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its
  canonical structural morphism (def-nagata-projective-space-base-change).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization` and `Scheme.fromNormalization` (def-sc-normalization).
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded integral-scheme
  clause reuses `Scheme.functionField` from `Mathlib.AlgebraicGeometry.FunctionField`;
  this is the generic stalk, unlike the general component-product definition
  `Scheme.functionFieldOfComponents` (def-sc-function-field).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`
  (def-weil-finite-integral-morphism).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  the dependency explicitly prescribes `IsDomain R ∧ IsIntegrallyClosed R`
  for normal domains (def-weil-pbc-normal-ring).
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`
  (def-kun-projective).

Proof imports include the recorded Chow and finite-over-projective modules, the
upstream normalization module, Mathlib Noetherian and quasi-separated permanence,
and the existing function-field API. The docstring carries all seven DAG proof
steps verbatim, reflowed only, with their node references. It describes the
trivial-group Chow specialization, normalization via the generic-point morphism,
the finite-module denominator calculation, the affine-base projective embedding,
and the induced generic-stalk identifications.

Edge cases checked before writing:

- Empty S is excluded by the node itself and `IsIntegral`, so no empty countercase
  is silently admitted. Y and N are nonempty by their integral clauses.
- S = Spec e is included, with identity modification, its own normalization and
  embeddings into P^0; n=m=0 gives one homogeneous coordinate, not empty projective
  space. The statement does not demand positive dimension.
- An integral singular projective curve is included; normalization is allowed to
  differ from Y. Neither c nor normalization is required globally to be an iso.
- Imperfect fields and every characteristic are included: finite normalization
  over a field uses Nagata finiteness, not geometric normality or perfection.
- Each dense-open requirement is applied in an integral nonempty scheme. For
  normalization, the inverse image is the full inverse image. For the composite
  it is a suitable source open with a commuting isomorphism, exactly as requested.
- Arbitrary universe u is explicit. ULift of Fin preserves every finite projective
  dimension and does not identify unrelated site universes.

Searches (2026-10-24):

- msearch.py leanfinder: "An integral proper scheme over a field has a projective
  birational Chow modification whose normalization is finite normal and projective".
  Eight hits, including `Scheme.Hom.instIsIntegralNormalization`, integralness and
  dominance of relative normalization. None states the combined model theorem.
- msearch.py leansearch: "normal projective birational model of an integral proper
  scheme over a field". Eight hits on relative normalization and proper morphisms,
  none with the claimed simultaneous Chow/normal/projective conclusion.
- msearch.py loogle: "AlgebraicGeometry.Scheme.normalization,
  AlgebraicGeometry.IsHProjective". No hits; service does not know the upstream
  normalization identifier.
- msearch.py grep: "normalization.*[Pp]rojective|[Pp]rojective.*normalization|[Cc]how"
  in AlgebraicGeometry: no hits.
- rg of `normal.projective.*(model|birational)|normal_projective|normalProjective`
  in `lean/WeilConjectures` and `lean/Sheaf`: no exact declaration.
- rg of this item's id in `lean/WeilConjectures`: no match. Broader birational and
  function-field searches find existing normalization and Chow declarations and
  the separate equivariant statement, which is used for the proof instead of
  restated as a definition.

Sources opened locally: coherent.tex lemma-chow-Noetherian and
remark-chow-Noetherian (Tags 0200/0201); varieties.tex
lemma-normalization-locally-algebraic and lemma-normalize-projective (Tags 0BXR/0GK4).
These confirm both the dense-open modification and finite projective normalization
without extra field hypotheses. No statement dispute or node fault was found.

## Second reading by NN

Independent second reading (maintainer review service, 2026-10-24); the earlier
section was a self-check by the author and is replaced by this reading.

Node list and the Lean rendering, each checked:

- Field e: `(e : Type u) [Field e]` (def-weil-field). OK.
- S nonempty integral proper finite-type e-scheme: `[S.Over (Spec (.of e))]`,
  `[IsIntegral S]` (nonempty by `IsIntegral`), `[IsProper (S ↘ Spec (.of e))]`
  (proper contains locally finite type and quasi-compactness). No extra hypothesis
  (no perfection, Noetherian, dimension or char assumption). OK.
- Y integral finite type over e: `∃ Y (_ : IsIntegral Y) (c : Y ⟶ S)`, with
  `LocallyOfFiniteType ∧ QuasiCompact` of `c ≫ S ↘ Spec e` (the recorded finite-type
  convention of def-weil-finite-type-morphism). The e-structure of Y is the composite,
  so c is an e-morphism by construction. OK.
- c proper surjective: `IsProper c ∧ Surjective c`. OK.
- Nonempty open V with c⁻¹V → V iso: `∃ V : S.Opens, (V : Set S).Nonempty ∧ IsIso (c ∣_ V)`
  (`morphismRestrict : c ⁻¹ᵁ V ⟶ V`, the full inverse image). OK.
- Closed immersion Y ↪ P^n_e over e: `i : Y ⟶ ℙ(ULift (Fin (n+1)); Spec e)`,
  `IsClosedImmersion i`, over-e equation. ℙ is the recorded `ProjectiveSpace`
  (def-nagata-projective-space-base-change), n+1 homogeneous coordinates as in
  def-kun-projective. OK.
- n_Y : N = Y^ν → Y normalization in own function field: `Y.normalization`,
  `Y.fromNormalization` are the recorded upstream abbrevs of def-sc-normalization
  (relative normalization in `Y.fromSpecFunctionField`), not a chosen cover. OK.
- n_Y finite, surjective, birational: `IsFinite`, `Surjective`, and a dense U with dense
  full preimage and `IsIso (Y.fromNormalization ∣_ U)`. OK.
- N nonempty integral, normal (local rings integrally closed domains):
  `IsIntegral Y.normalization`, `∀ x, IsDomain (stalk x) ∧ IsIntegrallyClosed (stalk x)`,
  the inline form recorded by def-weil-pbc-normal-ring. OK.
- Closed immersion N ↪ P^m_e over e: second existential with the composite structure
  map. OK.
- Y, N H-projective, proper, finite type over e: two `IsHProjective` (upstream class of
  def-kun-projective, finite coordinate type), two `IsProper`, finite type of N by the
  LocallyOfFiniteType/QuasiCompact pair. OK.
- c∘n_Y proper, surjective, birational: `IsProper`, `Surjective` of
  `Y.fromNormalization ≫ c`, and dense A ⊆ N, W ⊆ S with `a : A ≅ W`,
  `a.hom ≫ W.ι = A.ι ≫ Y.fromNormalization ≫ c` (dense-open birationality, as the
  node defines it). OK.
- Function-field isomorphisms induced by c, n_Y, c∘n_Y: generic point goes to generic
  point and the actual `stalkMap` at the generic point is an iso; for integral schemes
  the generic stalk is Mathlib `Scheme.functionField`, the integral clause of the
  def-sc-function-field record. OK.

Edge cases: S = Spec e (Y = N = S, n = m = 0, P^0 has one coordinate); singular
integral curves (normalization not an iso globally); imperfect e and every
characteristic (normalization finiteness by finite type over a field); empty S
excluded by the node and by `IsIntegral`. Universe u throughout, ULift only on the
finite coordinate type.

Records: the node changes only in its `lean` record; `lean.statement` is verbatim the
signature in the file; module and statement docstrings carry the source place,
`(blueprint: lem-sfb-normal-projective-birational-model)` and the seven proof steps;
no new definition; proof `sorry`. stmt_deps are all definition nodes with landed
declarations that the statement uses.

Searches: rg of `normal_projective_birational|NormalProjectiveBirational` in the live
lean/Sheaf and lean/WeilConjectures trees: no existing declaration. The landed
`exists_semilinear_equivariant_chow_modification` is the Chow input (proof dependency),
not this statement.

Findings: none in the Lean or the records.
