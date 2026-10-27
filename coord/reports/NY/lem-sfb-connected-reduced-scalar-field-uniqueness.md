## Worker report

The module `Sheaf.AlgebraicGeometry.ConnectedReducedScalarFieldUniqueness` states
`AlgebraicGeometry.Scheme.connected_reduced_scalar_field_integralClosure_unique`,
with a single `sorry` and no new definitions. The node is unchanged except for `lean`.
The source was read in `literature/stacks-project/varieties.tex`: Tag 04MI,
`lemma-integral-closure-ground-field` (lines 5318 onward), and Tag 04MK,
`proposition-unique-base-field` (lines 5964 onward). The declaration docstring gives
all eight steps of the node's proof, including the quasi-compact comparison and the
propagation of one fixed monic polynomial across a connected open cover.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Scheme X | `(X : Scheme.{u})` |
| Nonempty and connected | `[ConnectedSpace X]`; its `toNonempty` field supplies nonemptiness, so no redundant `Nonempty` assumption is added |
| Reduced | `[IsReduced X]`, Mathlib's sectionwise condition, equivalent to reduced local rings |
| Two fields | `(k₁ k₂ : Type u) [Field k₁] [Field k₂]` |
| The two specified morphisms | `(a₁ : X ⟶ Spec (CommRingCat.of k₁))` and the analogous `a₂` |
| Each morphism locally of finite type | `[LocallyOfFiniteType a₁] [LocallyOfFiniteType a₂]` |
| A is global sections | `Γ(X, ⊤)` throughout, not a function field or a stalk |
| Induced scalar map rho_i | `((ΓSpecIso (CommRingCat.of kᵢ)).inv ≫ aᵢ.appTop).hom` |
| Both scalar maps are injective | The first and second `Function.Injective` conjuncts |
| C_i is the subring of integral elements | `@integralClosure kᵢ Γ(X, ⊤) _ _ rho_i.toAlgebra`, converted by `@Subalgebra.toSubring` to a subring of A |
| The two closures are equal inside A | Equality of those two `Subring Γ(X, ⊤)` terms, rather than an abstract isomorphism |
| The common subring is a field | `IsField` of the first subring; the preceding equality identifies the second with it |

The explicit `@Subalgebra.toSubring` receives exactly the same canonical algebra
argument as the fully specified `integralClosure` argument.
This avoids synthesizing an unrelated algebra structure. There is no arbitrary
scalar map, field instance, auxiliary choice, or hidden additional hypothesis.
Using one arbitrary universe `u` is the usual Mathlib scheme-category convention:
the fields and scheme can be placed in a common universe, with no fixed size bound.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field` (exported by the imports).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`. The same module defines `Scheme.ΓSpecIso` and
  `Scheme.Hom.appTop`, the canonical construction of the scalar map.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure` and its
  carrier predicate `IsIntegral`. `Subalgebra.toSubring` is Mathlib's existing
  conversion in `Mathlib.Algebra.Algebra.Subalgebra.Basic`.

Statement dependencies are publicly imported; available proof dependencies are
plain imports, including the recorded connectedness/idempotent theorem, the
polynomial generalized inverse, the tower-integrality theorem, the affine-target
adjunction, Noetherian facts, units finite generation, and the Noetherian topology
module. `lem-sfb-subfield-units-quotient-finite` has neither a Lean record nor a
Mathlib match in the read repository; it is a proof prerequisite only and has no
import to add yet. It is cited in the proof docstring for stage 3. There are no
missing statement notions, new nodes, dependency repairs, or statement corrections.

Edge cases checked before writing:

- The empty scheme is excluded by exactly the node's connectedness/nonemptiness
  condition. Otherwise its zero global-sections ring would invalidate injectivity
  and the field assertion.
- A connected reduced scheme need not be integral: two affine lines meeting in a
  point are allowed. No `IsIntegral X` or `IsDomain Γ(X, ⊤)` is assumed. Thus the
  domain-only existing field theorems are not substitutes for this node.
- Reducible, non-quasi-compact, and nonseparated schemes remain allowed; there is
  no compactness, irreducibility, separatedness, or finite-component hypothesis.
- The fields can coincide and the morphisms can coincide. Both closures then use
  the identical canonical scalar structure; equality is literal subring equality.
- Arbitrary characteristic is allowed. Neither perfectness nor algebraic
  closedness is assumed. The common closure need not be finite over either field.
- `IsField` states nontriviality and inverses for the inherited ring operations;
  it does not require choosing inverse data or changing the subring's ring structure.

Searches for an existing statement (2026-10-24), all through the required wrapper:

- LeanFinder: "On a nonempty connected reduced scheme locally of finite type over
  two fields the integral closures of the two fields in global sections coincide
  and are fields". Eight hits: function fields of integral schemes,
  `AlgebraicGeometry.isField_of_universallyClosed`, and
  `IsIntegralClosure.isField`, among others. None compares two scalar fields;
  the latter field results assume an integral/domain hypothesis absent here.
- Loogle: `"integralClosure", "IsField"`. One hit,
  `IsIntegralClosure.isField`, with an `IsDomain` assumption. Not an exact match.
- LeanSearch: "The integral closures of two fields in the global sections of a
  connected reduced scheme locally of finite type over both fields coincide".
  Eight hits about integral closure and integral closedness; none states this
  scheme theorem or the comparison of two scalar structures.
- Mathlib grep: `unique.base.field|integral.closure.ground.field|integralClosure.*global|global.*integralClosure`.
  Zero hits.
- `rg -n 'integralClosure|unique_base_field|scalar.field.uniqueness'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: many unrelated normalization and
  arithmetic closures, but no comparison theorem. The upstream
  `WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Algebra.isField_integralClosure`
  was opened: it assumes a domain and only states a field conclusion.
- `grep -rn 'lem-sfb-connected-reduced-scalar-field-uniqueness' lean/WeilConjectures`:
  no hits. A narrower name check for `scalar_field_integralClosure_unique`,
  `connected_reduced_scalar_field`, and `unique_base_field` in both source roots
  and `dag/lean_names_upstream.json` also found none.

No statement dispute was found. The source's missing prime in its proof conclusion
is already documented by stage 1; the node's statement and its proof route are sound.

## Second reading by NY

Self-check only, as this dispatcher assignment prohibits starting other agents;
the maintainer supplies the independent review. Reopened the node and final Lean
file and matched every row above. `ConnectedSpace` includes nonemptiness, while
`IsReduced` supplies the exact sectionwise reducedness used in the proof. The two
`LocallyOfFiniteType` instances attach to the actual named morphisms. For each
closure the algebra is induced by that same morphism and the inverse of the
canonical spectrum/global-sections isomorphism, in the correct direction from
k_i into A. Conversion to `Subring A` forgets only the coefficient-field label,
so it permits comparing the two closures as subsets of the same ring. The equality
and the `IsField` conjunct say exactly that the common closure is a field. Both
injectivity clauses from the prose are present, rather than being silently omitted.
No stronger domain, finite-type, compactness, or algebraic-closedness hypothesis
was introduced. The only compile-driven change was making the existing
`Subalgebra.toSubring` algebra argument explicit; it changes no mathematics.

Validation: the required `scompile.py NY
lem-sfb-connected-reduced-scalar-field-uniqueness` compiled the final module in
both sandbox and library modes, with exit code 0 and no diagnostics. All Lean
lines are at most 100 characters. A structural comparison of the node copy with
the read repository found exactly one changed top-level field: `lean`.
