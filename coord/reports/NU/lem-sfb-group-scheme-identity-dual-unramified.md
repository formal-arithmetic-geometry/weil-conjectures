## Worker report

The module `Sheaf.AlgebraicGeometry.GroupSchemeIdentityDualUnramified` states
`AlgebraicGeometry.isUnramified_iff_identityDualNumberPoints`, with its only proof `sorry`.
It introduces no definitions and changes only the item's `lean` field. The live Q17 delivery
was a stage-1 split, not a stage-2 statement: the base node has no `lean` record. The previous
worker's conclusion that the task was already completed confused those two stages.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field K: `{K : Type u} [Field K]`.
- A group scheme over K: `G : Over (Spec (.of K))` with `[GrpObj G]`. The underlying
  scheme is `G.left`, the structure map is `G.hom`, and the identity is `η[G].left`,
  the underlying morphism of the unit of the group object. The monoidal unit of the
  over category has underlying scheme `Spec K`; it is not a separately chosen point.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the conjunction
  in the dependency record. Quasi-compactness has not been discarded even though the
  mathematical argument only needs local finite type.
- D = Spec(K[epsilon]/epsilon²): `Spec (.of (DualNumber K))`. The dependency node
  explicitly identifies the dual-number ring with Mathlib's `DualNumber K`.
- The zero section i: `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)`.
  This is induced by the canonical projection `a + b epsilon ↦ a`, fixing K and killing
  epsilon. No arbitrary section or lifting assumption replaces it.
- The projection p: `Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))`.
  The algebra map is the canonical inclusion `a ↦ a + 0 epsilon`.
- Unramifiedness of the structure map: `IsUnramified G.hom`, using the dependency's
  existing conjunction of locally finite type and an open-immersion diagonal.
- If and only if: `↔`, so both directions are asserted.
- Every morphism v: `∀ v : Spec (.of (DualNumber K)) ⟶ G.left`.
- Being a K-morphism: the first antecedent, `v ≫ G.hom = p`, expresses commutation
  with the structure map. This is the explicit scheme-morphism presentation of a
  morphism in the over category, not an additional hypothesis.
- Restricting to the identity: the second antecedent, `i ≫ v = η[G].left`.
- Being constant at the identity: `v = p ≫ η[G].left`. Lean's composition order
  reverses the order of the node's functional notation `v ∘ i` and `e ∘ p`.
- No smoothness, reducedness, characteristic, affine, separated, commutative-group,
  perfect-field or algebraic-closure hypothesis occurs.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (Mathlib leaf).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp.
  It extends `MonObj` with inversion and the inverse identities. Its specialization
  to `Over (Spec K)` is exactly the recorded group-scheme interface. The identity
  comes from `MonObj.one` (notation `η[G]`). Mathlib's
  CategoryTheory.Monoidal.Cartesian.Over supplies the canonical monoidal structure.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact. Both are public imports.
- `def-sc-dual-numbers`: `DualNumber` and `DualNumber.eps`, Mathlib.Algebra.DualNumber.
  The canonical projection `TrivSqZeroExt.fstHom` is read in
  Mathlib.Algebra.TrivSqZeroExt.Basic; its inclusion is `algebraMap`.
- `def-weil-unramified-morphism`: `AlgebraicGeometry.IsUnramified`,
  Sheaf.AlgebraicGeometry.UnramifiedMorphism, read including its docstring and body.

Available proof dependencies are imported privately, as the stage rules require:
WeilConjectures.AlgebraicGeometry.Modules.Differentials (`Scheme.Hom.relativeDifferentials`),
Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
(`Scheme.Modules.tensorPullbackSectionAdjunction`, reexporting the explicit `tensorPullback`),
WeilConjectures.AlgebraicGeometry.SchemeTangentSpace (`schemeTangentSpace`),
Mathlib.LinearAlgebra.Dual.Lemmas (`LinearMap.dualMap_injective_iff`), and
WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
(`relativeDifferentials_affine_sections`). The two new stage-1 proof prerequisites,
`lem-sfb-rational-tangent-differential-fibre-duality` and
`lem-sfb-group-scheme-differentials-from-identity`, have no recorded Lean declaration
on the read base, so there is no module to import yet. They are unnecessary to type the
item's statement. Their exact mathematical roles are retained in its proof docstring;
they can be imported privately when stated. All five proof steps are explained there.

Source reading: groupoids.tex, lemma-group-scheme-module-differentials (047I), gives
Omega = f*e*Omega for any group scheme; morphisms.tex, lemma-unramified-omega-zero (02G5),
gives unramified iff locally finite type and zero differentials; varieties.tex,
definition-tangent-space and lemma-tangent-space-cotangent-space (0B2C/0B2D), identify
the relevant tangent vectors and cotangent dual; moduli-curves.tex,
lemma-in-DM-locus-vector-fields (0E6G), first proof paragraph, applies precisely this
argument at the K-rational identity. No source-based correction is necessary.

Edge cases checked before drafting:

- The trivial group `Spec K` satisfies the condition and is unramified.
- Finite constant groups satisfy it in every characteristic.
- The additive group has a nonzero infinitesimal identity point and is not unramified.
- In characteristic p, both alpha_p (epsilon as coordinate) and mu_p (1 + epsilon)
  have nonconstant identity-reducing dual points and fail unramifiedness. Nonreduced
  examples are therefore admitted and correctly detected.
- In characteristic 2 the same examples and the square-zero relation still apply;
  no division by 2, characteristic exclusion, or separability assumption is hidden.
- A nonaffine group is permitted: v is a morphism into an arbitrary scheme G.left,
  and the differential trivialization is global. No affine chart is part of the signature.
- The empty scheme has no identity over Spec of a field and hence is not a group
  scheme of this kind. Its exclusion follows from the given group structure.
- The universe u is explicitly bound and simultaneously sizes K and its schemes,
  using the project's recorded group-scheme interface. There is no additional test
  universe that can make the quantifier over v vacuous.

Searches performed:

- `msearch.py ... leanfinder "A finite type group scheme over a field is unramified if
  and only if every dual number point reducing to its identity is constant"`: eight
  results, concerning algebraic unramifiedness and its elementary properties; no
  group-scheme identity-only criterion. The closest result is
  `Algebra.FormallyUnramified.isReduced_of_field`, which is a different assertion.
- `msearch.py ... loogle '\"GrpObj\", \"FormallyUnramified\"'`: zero hits.
- `msearch.py ... grep 'unramified.*group|group.*unramified|identity.*[Dd]ual|[Dd]ual.*identity'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "A finite type group scheme over a field is unramified iff
  its only tangent vector at the identity is zero"`: UNAVAILABLE, service rate limit
  exceeded (60 per minute). No mathematical verdict is drawn from this unavailable search.
- `rg` with the same pattern in lean/WeilConjectures and lean/Sheaf found only unrelated
  duality text and the existing Lie/tangent/cotangent definitions and comparisons,
  including `GrpObj.lieIdentityTangentEquiv`; none asserts this equivalence.
- `grep -rn 'lem-sfb-group-scheme-identity-dual-unramified' lean/WeilConjectures`: no hits.
- `rg 'isUnramified_iff.*[Ii]dentity|unramified.*[Dd]ual|[Dd]ual.*unramified|isUnramified_iff'
  in the two AlgebraicGeometry directories: no hits.
- The proposed declaration name was also searched in dag/lean_names_upstream.json,
  lean/Sheaf and lean/WeilConjectures: no hits.

Validation: `scompile.py NU lem-sfb-group-scheme-identity-dual-unramified <module>`
compiled both the sandbox form and the actual library module cleanly, in 10.7 and
10.1 seconds respectively. The initial probe found that QuasiCompact was visible only
through a private import; explicit public imports of both finite-type component modules
fixed that visibility. There are no additional warnings or errors. Every variable and
universe is explicitly bound, with `autoImplicit false`.

No STATEMENT-DISPUTED flag, node fault, dependency repair, new definition node or
statement correction is needed. The worker did not start any other agents; the
maintainer performs the independent review after delivery.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
