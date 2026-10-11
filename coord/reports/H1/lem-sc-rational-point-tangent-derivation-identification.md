## Worker report

The module `Sheaf.AlgebraicGeometry.RationalPointTangentDerivationIdentification` states
`AlgebraicGeometry.exists_rationalPoint_tangent_cotangent_linearEquiv`, with proof `sorry`.
It introduces no definitions and changes no informal statement or dependencies.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; the scheme over it is `(X : Scheme.{u})`
  with the explicit structure morphism `(p : X ⟶ Spec (.of k))`, as required by the
  recorded tangent-space declaration. The point is `(x : X)`.
- `R := X.presheaf.stalk x` is the local ring. `K := X.residueField x` is its residue
  field, and `IsLocalRing.maximalIdeal R` is its maximal ideal.
- `r : k →+* K` is the structural map: the germ of k at p(x), followed by the stalk
  map of p and the residue map at x. `Function.Bijective r` says precisely that
  this structural map is an isomorphism, rather than merely assuming an unrelated
  isomorphism of fields. This is the node's rationality hypothesis.
- `schemeTangentSpace k X p x` is exactly the recorded dual-number morphism definition,
  with both the closed-point condition and the over-k condition. Its existing additive
  group and K-module are used. `Module.compHom ... r` restricts scalars to k on both
  this space and the existing cotangent space. The intermediate K-module instance on
  the cotangent space is `inferInstanceAs` of Mathlib's residue-field instance; it
  supplies the same structure despite the bundled residue-field notation.
- For each theta, `hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x` records the
  consequence of the closed-point condition needed for the dependent stalk types.
  `sharp` is `Scheme.stalkClosedPointTo θ.val` precomposed with `eqToHom` to identify
  its source stalk with R. The named Mathlib map is literally the stalk map followed
  by `(stalkClosedPointIso ...).hom`, the inverse of the germ isomorphism, as requested.
- Clause (a) is `∃! D : R → k` together with the formula for every `a : R`.
  `TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))` is
  residue(a) + D(a) epsilon written in K-coordinates. Because r is bijective,
  this is precisely the node's expression after identifying K with k. The dependency
  defines tangent vectors using DualNumber K, so this identification is explicit,
  rather than changing the tangent-space definition. Unique dual-number coordinates
  and injectivity of r give uniqueness even without the second conjunct below.
- Clause (b) is the second conjunct, for every `a : IsLocalRing.maximalIdeal R`:
  `e θ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a`.
  Mathlib's `IsLocalRing.CotangentSpace R` is exactly m/m², and its `toCotangent`
  is the quotient map. Thus `e θ`, a bundled k-linear map on that quotient, realizes
  the specified rule and certifies its well-definedness and linearity.
- Clause (c) is the existential `e : schemeTangentSpace k X p x ≃ₗ[k]
  (IsLocalRing.CotangentSpace R →ₗ[k] k)`, with the above coefficient equation
  specifying its values. It is the requested map, not an unspecified isomorphism.
  Surjectivity of the quotient map determines each functional by this equation.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` explicitly fixes no declaration; schemes and their
  morphisms use Mathlib's `AlgebraicGeometry.Scheme` and its category.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.residue`, Mathlib.AlgebraicGeometry.ResidueField.
- `def-sc-scheme-tangent-space`: `AlgebraicGeometry.schemeTangentSpace`,
  `schemeTangentSpaceAddCommGroup`, `schemeTangentSpaceModule`, from
  Sheaf.AlgebraicGeometry.SchemeTangentSpace. No duplicate tangent definition.
- `def-weil-locally-ringed-space-morphism`: Mathlib's LocallyRingedSpace.Hom and
  Hom.stalkMap, underlying the scheme stalk maps in the statement.
- `lem-weil-pbc-morphism-from-spec-local-ring`: `Scheme.stalkClosedPointTo` and its
  underlying `stalkClosedPointIso`, Mathlib.AlgebraicGeometry.Stalk; also read the
  full `SpecToEquivOfLocalRing` correspondence used in the natural-language proof.
- The quotient and scalar structure are Mathlib's `Ideal.Cotangent`, `Ideal.toCotangent`
  and `IsLocalRing.CotangentSpace`, Mathlib.RingTheory.Ideal.Cotangent.

Edge cases: no finite-type, Noetherian, smoothness, separatedness, or algebraic-closure
assumption is imposed. For X = Spec k both spaces are zero; the coefficient function
is zero. At zero on A¹ the epsilon coefficient is the functional on the class of t.
The statement permits arbitrary characteristic (including 2), singular local rings,
and infinite-dimensional cotangent spaces. An empty scheme has no point x and creates
no excluded case. All universes and variables are explicitly bound, with k and X in
one arbitrary universe, matching the recorded dependency.

Searches (real msearch queries are also recorded in searches.jsonl):

- LeanFinder: `scheme tangent vectors at a rational point identified with the linear
  dual of the cotangent space`: eight hits, including SpecToEquivOfLocalRing and
  SpecToEquivOfField, but no scheme tangent/cotangent identification.
- Loogle: `IsLocalRing.CotangentSpace, DualNumber`: no hits.
- LeanSearch: `scheme tangent space rational point dual cotangent space`: HTTP 500,
  unavailable; no absence conclusion is drawn from this service.
- msearch grep: `tangent.*cotangent|CotangentSpace|schemeTangent` in Mathlib's
  AlgebraicGeometry directory: no hits. Direct rg in Mathlib/RingTheory/Ideal/Cotangent
  finds exactly the ring-level quotient and scalar structures reused here.
- Direct rg for `CotangentSpace|cotangentSpace|TangentSpace|tangentSpace` in the
  source AlgebraicGeometry and project AlgebraicGeometry directories finds the existing
  schemeTangentSpace dependency, tangent sheaves, and the group-scheme-focused
  `tangentSpaceAt` API in Picard/Jacobian; none states this theorem.
- Direct rg for `tangent.*cotangent` across the source and project additionally found
  WeilConjectures/Mathlib/RingTheory/Ideal/Cotangent.lean. Read it in full: its
  AlgHom.cotangentForm/toDualNumber constructions concern algebra maps lifting a
  k-point, not the scheme-tangent identification; no such construction is duplicated
  here. They may be useful in the stage-3 proof.
- grep for the item's exact id in the source gives no matches. The chosen theorem
  name has no match in Mathlib/source/project or dag/lean_names_upstream.json.

Sources checked online because literature/stacks-project/varieties.tex is absent on
this machine: https://stacks.math.columbia.edu/tag/0B2E gives the rational-point
identification, with m_s = 0 over Spec k; https://stacks.math.columbia.edu/tag/0B2D
explicitly writes phi(a) = c(a) + D(a) epsilon and derives the derivation condition.
The node's three-step proof is transcribed in the theorem docstring.
No statement fault or disputed claim was found.

## Second reading by H1

Independent review against the node, all five statement-dependency nodes and their
declarations, and the Stacks source: PASS. No Lean or node repair was necessary.

Object/hypothesis/conclusion checklist, written from the informal statement:

1. A field k: `(k : Type u) [Field k]`. Exact; arbitrary characteristic.
2. A k-scheme X: `(X : Scheme.{u}) (p : X ⟶ Spec (.of k))`. Exact;
   the explicit structure map is accepted because `schemeTangentSpace` takes it.
   The conventions node fixes no additional hypothesis here.
3. A point x: `(x : X)`. Exact; neither closedness nor finite type is added.
4. Local ring, maximal ideal and residue field/map: `R := X.presheaf.stalk x`,
   `IsLocalRing.maximalIdeal R`, `K := X.residueField x`, `(X.residue x).hom`.
   Exact. Read `Scheme.residueField` and `Scheme.residue` in
   Mathlib/AlgebraicGeometry/ResidueField.lean: they are the stalk quotient
   by its maximal ideal and its quotient map.
5. The structural map k to K is an isomorphism: `r` is the composite
   `StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x`, and the
   sole additional premise is `Function.Bijective r`. Exact; this is not an
   arbitrary abstract isomorphism. Restriction by `Module.compHom ... r` gives
   precisely the k-actions on tangent and cotangent spaces under this identification.
6. Tangent vectors with their canonical vector structure: `schemeTangentSpace k X p x`.
   Exact. Opened Sheaf/AlgebraicGeometry/SchemeTangentSpace.lean: its subtype
   requires both restriction to `X.fromSpecResidueField x` and commutation with p.
   Its instances select the structure specified by `exists_tangentVectors_vectorSpace`.
   Opened that theorem too: zero is the constant point, addition is pushout gluing,
   and scalar multiplication is precomposition with epsilon scaling. These are
   the node's operations, with no choice of an unrelated vector-space structure.
7. The induced stalk map followed by the inverse germ isomorphism: `sharp` is
   `Scheme.stalkClosedPointTo θ.val` preceded by the source-stalk equality transport.
   Exact. Read `stalkClosedPointTo` and `stalkClosedPointIso_inv` in Mathlib's
   Stalk.lean: this is literally the stalk map followed by the inverse of the germ.
   Read `LocallyRingedSpace.Hom` and `Hom.stalkMap`: the local maps are the
   recorded dependency's maps. The witness hx identifies θ(z) with x; it is a
   consequence of the tangent-vector condition, not a new premise.
8. Clause (a), a unique function D with the dual-number expansion for every a:
   `∃! D : R → k` and `∀ a : R, sharp a = TrivSqZeroExt.inl ... +
   TrivSqZeroExt.inr (r (D a))`. Exact after the structural identification K = k.
   The conjunction with clause (b) inside `∃!` does not weaken coefficient
   uniqueness: projecting the second coordinate and using injectivity of r
   already forces uniqueness among all functions satisfying the expansion.
9. Clause (b), well-defined k-linear functional on m/m² taking [a] to D(a):
   `e θ : IsLocalRing.CotangentSpace R →ₗ[k] k` with
   `∀ a : IsLocalRing.maximalIdeal R, e θ (...toCotangent a) = D a`.
   Exact. Read Mathlib/RingTheory/Ideal/Cotangent.lean: `CotangentSpace` is
   maximalIdeal.Cotangent, `toCotangent_eq` identifies classes modulo m²,
   `toCotangent_surjective` covers every class, and the residue-field module
   instance is canonical. No Noetherian instance is needed for these declarations.
10. Clause (c), the coefficient assignment is a k-linear isomorphism:
    `∃ e : schemeTangentSpace ... ≃ₗ[k] (IsLocalRing.CotangentSpace R →ₗ[k] k)`
    together with the universally quantified coefficient and evaluation equations.
    Exact; the equation fixes e on every tangent vector and every quotient class,
    so it states the prescribed identification, not just existence of some isomorphism.
    Choosing e before θ is appropriate for a single linear equivalence on all vectors.

Source check: varieties.tex is absent locally. Read the actual TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
labels lemma-tangent-space-cotangent-space and lemma-tangent-space-rational-point,
and checked https://stacks.math.columbia.edu/tag/0B2D and
https://stacks.math.columbia.edu/tag/0B2E. These assume arbitrary schemes and a
morphism; the latter requires equality of the induced residue fields. For S = Spec k,
the base maximal ideal is zero, so its quotient is m_x/m_x². No ambient variety,
Noetherian, smoothness, separatedness, or characteristic hypothesis is implicit.
The coefficient construction is the one in 0B2D; the docstring reproduces all
three node proof steps, including the inverse, locality, and linearity.

Edge cases: Spec k has m = 0, zero cotangent dual, and only the zero tangent
vector. Affine one-space at zero has the expected t-coefficient functional.
Singular/nonreduced and non-Noetherian local rings remain permitted, including
infinite-dimensional cotangent spaces. Characteristic 2 and positive characteristic
are not excluded. The empty scheme has no x, so the quantified assertion is vacuous.
There is no index-set or n parameter. The zero ring cannot be a stalk at a point
of a scheme; it contributes only the empty affine scheme case. `u` is explicit and
arbitrary, matching the existing tangent dependency; schemes and their base field
of initially different sizes can be placed in a common universe. No implicit
variable or universe remains unbound.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: `local homomorphisms into square zero extension correspond
  to linear forms on maximal ideal quotient`. Eight hits, all algebraic
  TrivSqZeroExt lifting constructions; no scheme tangent/cotangent identification.
- Loogle via msearch: `IsLocalRing.CotangentSpace, _ ≃ₗ[_] _`. Zero hits.
  The earlier query `SpecToEquivOfLocalRing, LinearEquiv` was rejected as an
  unknown identifier by that service; it is not absence evidence.
- LeanSearch via msearch: `Tangent vectors of a scheme at a rational point are
  linear forms on the maximal ideal modulo its square`. HTTP 500/unavailable;
  no absence inference from it.
- Direct rg across Mathlib/AlgebraicGeometry, WeilConjectures, and lean/Sheaf:
  `cotangent.*(Equiv|equiv)|dualNumber.*(Equiv|equiv)|[Tt]angent.*[Dd]ual|rationalPoint_tangent`.
  Read the source's TangentSpace.lean, the tangentSubgroup/tangentSpaceAt API
  in Picard/Jacobian.lean, the specialized dualCotangentToMatrix construction
  in GeneralLinear/ClosedSubgroup/Lie.lean, and the entire upstream
  Mathlib/RingTheory/Ideal/Cotangent.lean extension. The former is sheaf-level;
  the group/matrix APIs are specializations; AlgHom.cotangentForm and
  AlgHom.toDualNumber concern algebra maps. None is this scheme theorem.
  The delivery introduces no competing definition.

There are no new nodes, dependency modules, or statement correction to review.
The dependency declarations are usable as recorded. The file has one named
theorem with proof `sorry`, no definition, the required source and blueprint
docstrings, and appropriate imports. Checked the node's lean.statement against
the source text: verbatim equal. Server scompile passed in 2.2 seconds with
no errors or warnings. Changes by this second reading: this review section only.
