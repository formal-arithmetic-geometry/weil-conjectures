## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.Curve.DegreeTwoPencilUniqueness`, declaration
`AlgebraicGeometry.Scheme.degree_two_pencil_uniqueness`. Its sole theorem proof is `sorry`.
The original statement, proof and proof dependencies are unchanged. The new definition node
`def-sfb-complete-divisor-linear-system` is added to statement dependencies.

Hypotheses and clauses, matched against the node:

- `k : Type u`, `[Field k]`, `[IsAlgClosed k]` are the algebraically closed base field.
  `C : Scheme.{u}`, `f : C ⟶ Spec (.of k)` specify the curve and its structure morphism.
  `[IsConnectedCurve f]` includes separated finite type, connectedness, nonemptiness and
  dimension exactly one; `[Smooth f]` and `[IsHProjective f]` give smoothness and the recorded
  projective convention. `hg : 2 ≤ f.genus` is precisely the genus restriction.
- Effectivity of a divisor is `∀ P, 0 ≤ D P`, using the existing closed-point Finsupp divisor.
  `Divisor.degree C D = 2` is the sum-of-coefficients degree, not a reduced support cardinality.
- `Divisor.completeLinearSystem k C f D` is the effective divisors E with E-D in the existing
  `C.principalDivisors`. This is the requested linear equivalence, with no replacement by
  arbitrary isomorphism data or an abstract relation.
- The introductory description of members is rendered by the first conjunct: an equivalence
  from Mathlib's `Projectivization k (Divisor.linearSystemSections k C f D)` to that divisor
  set. The equation after this equivalence requires that every nonzero section is sent to
  the divisor with coefficients `D P + C.ord (s.val ⟨P.val, trivial⟩) P.val`.
  Thus the equivalence is the section/divisor dictionary, rather than an arbitrary bijection.
- The scheme of members is `Divisor.linearSystemScheme`: existing relative `ProjectiveSpace`
  indexed by `Module.Free.ChooseBasisIndex` of the actual section space. Coordinate vectors
  represent sections in this basis. This is the lines convention in the question; it is the
  quotient-convention `P(V dual)` in Stacks 0CCT. The new definition does not choose an object
  from a postponed mere existence theorem. The pencil conclusion also includes its scheme
  isomorphism with the existing `ProjectiveLine`.
- Two distinct members are the nested existentials `E₁`, `E₂` in the complete system with
  `E₁ ≠ E₂`. The first pencil conclusion is `Module.finrank k ... = 2`, on actual global
  sections of the dependency's O(D), restricted along the actual base-field map.
- Basepoint freeness is `∀ Q : closedPoints C, ∃ E ∈ ..., E Q = 0`. These are exactly the
  points that can belong to a divisor; the generic point is in no divisor. No reducedness
  or separability condition on the members is introduced.
- At most one complete moving degree-two system is the quantified E clause with exactly
  the same effectivity, degree and two-distinct-member hypotheses, concluding equality
  of the two sets of divisors.
- Exactly one member through each rational point is `∀ Q : closedPoints C, ∃! E, E ∈ ... ∧
  0 < E Q`. On a finite-type scheme over the algebraically closed k, closed points are
  precisely k-rational points. This uses the canonical closed-point encoding already
  built into `Scheme.Divisor`; it does not discard rational point lifts.
- A pencil is realized by `∃ (π : C ⟶ ProjectiveLine ...) (hπ : IsFinite π), ...` with the
  structure equation over k, `Hom.IsDegreeTwoCurveMap`, and equality of the full fibre-divisor
  range with the complete system.
- `Hom.IsDegreeTwoCurveMap` means nonconstant (no factorization through a k-point) and
  degree two for the actual generic-stalk map `π.functionFieldMap hη`. `Module.finrank`
  receives exactly the algebra/module structure of this map. The existence of hη records
  dominance, which is a consequence of nonconstancy for these proper integral curves;
  constant degree-zero maps are excluded. There is no separable-degree convention.
- `Hom.degreeTwoFiberDivisor` uses the existing `Divisor.pullback π (Finsupp.single Q 1)`.
  Finiteness is obtained in the conclusion. This retains ramification multiplicities and
  is not merely the set-theoretic fibre.
- The converse is quantified over every nonconstant degree-two k-map; it supplies finiteness
  and an effective moving degree-two divisor whose complete system is its fibre range.
- The last conjunct quantifies over two such k-maps and supplies `a : Aut (ProjectiveLine ...)`,
  the equation that a is over k, and `π₁ ≫ a.hom = π₂`. This is an actual scheme automorphism.

Dependency declarations used in the statement/constructions:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
  Read their class signatures and docstrings. AlgebraicClosure itself is not needed: the
  item assumes an arbitrary algebraically closed field, rather than a chosen closure.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`, `Scheme.Hom.genus`.
  The recorded genus is the differential-form version, identified with H¹(O) on proper
  smooth curves by the existing Serre-duality API; this is the node's stated equivalent form.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, exactly the
  finite homogeneous-coordinate projective embedding convention in def-kun-projective.
- `Sheaf.AlgebraicGeometry.DivisorModule`:
  `Scheme.Divisor.moduleOfSmoothConnectedCurve`, the explicit O(D) module. Its underlying
  top sections are locally constant rational functions with the specified valuation bounds.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`: `Scheme.Divisor`, `Scheme.div`,
  `Scheme.principalDivisors`, `Scheme.Divisor.degree`; no copies of these notions are made.
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`:
  `Scheme.smooth_connected_curve_local_rings`, whose integral proof is used only to install
  derived structure; Noetherianity is obtained by `isNoetherian_of_locallyOfFiniteType f`.
  These are consequences of the original hypotheses, not extra assumptions.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, `ProjectiveLine`.
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth` supplies the existing
  integral projective-line instance. Mathlib's `Projectivization`, `Projectivization.mk`,
  `Module.Free.ChooseBasisIndex`, and scalar restriction supply the standard vector APIs.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, `Scheme.Divisor.pullback` and its ramification-index
  construction; the full signatures and docstrings were read.

All currently recorded proof-dependency modules are imported. The smooth-local-rings and
DivisorModule modules are public through the definition module; Curve covers def-sc-pic0.
The remaining imports are ProjectiveLineGenusZero, ProjectiveImpliesProper,
Cohomology.DirectImage.FiniteFreeComplex, DivisorClassCurve, DivisorModuleLocal,
GlobalSectionsBijective, Curve.RiemannRoch, ProperCurveBundlePullbackDegree,
Curve.ProperFunctionFieldMorphisms, CurveSectionDegreePositivity, ProjectiveSpaceFunctorOfPoints,
ProjectiveSpaceHomOfGeneratingSections, RationalSectionDivisor,
ProperFiniteFibreFiniteNeighbourhood, and the Mathlib closed-point/properness modules.
`lem-sfb-linear-series-degree-dimension-bound` has neither a Lean record nor a mathlib_match
in the current DAG, so there is no module to import for that proof dependency. It is not a
statement prerequisite, and no copy of that theorem is introduced here.

Edge cases checked: no characteristic restriction, including characteristic two; no
separability assumption; a ramified member 2Q is counted with multiplicity and still gives
one member; genus two is included by the nonstrict genus bound; nonhyperelliptic curves
satisfy the conditional assertions without an invented existence assumption; constant
maps are explicitly excluded; the introductory dictionary also covers D=0; a zero section
is excluded from projectivization; empty and zero-dimensional schemes are excluded exactly
by the node's connected-curve meaning. Every universe and variable is explicit, with both
autoImplicit options false. No local notation, local instance, or private declaration is used.

Searches performed (actual queries and responses are in searches.jsonl):

- LeanFinder: “A smooth projective curve of genus at least two has a unique basepoint free
  degree two complete linear system”: eight Weierstrass-model hits, no matching theorem.
- Loogle: `"LinearSystem", "Divisor"`: zero hits. Grep Mathlib AlgebraicGeometry:
  `hyperelliptic|linear.?system|pencil|fiberDivisor`: zero hits.
- LeanSearch: “The complete linear system of a divisor is the projective space of its global
  sections modulo nonzero scalars”: eight hits, including `Projectivization` and its setoid;
  these are reused rather than redefined.
- LeanFinder: “Effective divisors linearly equivalent to a fixed divisor form its complete
  linear system”: eight number-field/Weierstrass class-group hits, none matches the notion.
- Grep Mathlib AlgebraicGeometry: `completeLinearSystem|linearSystem|fiberDivisor|hyperelliptic`:
  zero hits. Loogle `"Projectivization"` confirms the reused vector-space quotient API.
- Grep Mathlib: `linearSystemSections|linearSystemScheme|sectionRepresentsDivisor`: zero hits.
- Grep of live `lean/WeilConjectures` and `lean/Sheaf`, by the item id and by complete system,
  pencil, hyperelliptic, linearSystemSections, linearSystemScheme and sectionRepresentsDivisor:
  no copy of the item or the new notion. `CompleteLinearSystemClosed.lean` states a theorem
  about generating sections and closed immersions, not the divisor set or scheme of members;
  the ample and equivariant pencils concern different existence problems. The canonical
  divisor pullback found by this search is reused.
- DAG definition search and `tools/blueprint_refs.py search 'complete linear system'`:
  zero blueprint matches. Search `linear system` finds only def-sc-ample, which uses P(H⁰ dual)
  for the definition of very ampleness; it does not define the effective-divisor set or the
  section/divisor dictionary. Search `pencil`: zero matches. `lean_names_upstream.py show`
  and the upstream declaration-name JSON contain no matching item/new helper.

Source read: Milne PDF printed p.120 (PDF p.126), first paragraph of III Theorem 12.1(b);
Stacks curves.tex Tag 0CCT, remark-classical-linear-series, including the dual convention.
The current blueprint latest directory was searched for this supporting notion; the node
has no blueprint.is and is not its unit's own statement. No statement correction or dispute.

Validation: both delivered modules compiled separately, in dependency order, through
scompile.py against the server's live library. The final compile had no errors or warnings.

## New nodes

`def-sfb-complete-divisor-linear-system` defines the effective-divisor complete system,
its actual O(D) section space with the structural k-action, its coordinate projective scheme,
and the valuation formula saying a section represents a member. Source: Stacks 0CCT and
Milne III 12.1(b), p.120. The three search kinds above found the reusable projectivization
API but no divisor-system construction in Mathlib, the live project, or the DAG. All data
is constructed explicitly; the basis is chosen by Mathlib's proved vector-space basis API.
No theorem or new postponed property is hidden in this definition module.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
