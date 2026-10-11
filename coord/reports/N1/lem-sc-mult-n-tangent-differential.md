## Worker report

The module `Sheaf.AlgebraicGeometry.MultNTangentDifferential` states
`AlgebraicGeometry.mult_n_tangent_differential`.  It uses the group-scheme encoding
`G : Over (Spec (.of k))` with `[GrpObj G] [IsCommMonObj G]`, and the multiplication-by-
`d` morphism represented by the `d`th power `𝟙 G ^ d` in the group-object hom group.
The hypothesis `d ≥ 1` is the explicit binder `hd : 1 ≤ d`.  The existential residue-field
bijection is exactly the `he` required by `schemeTangentMap`.  The displayed transport
along the equality that `[d]` sends the identity point to itself makes the target tangent
space precisely `T_{G/k,e}`.  The final clause says its value on every tangent vector is
`d • v`, i.e. scalar multiplication by the natural number `d` in the additive group.

Dependencies used:

- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
  `AlgebraicGeometry.isMonHom_npow_id` (the n-fold multiplication is a homomorphism).
- `Sheaf.AlgebraicGeometry.SchemeTangentSpace`,
  `AlgebraicGeometry.schemeTangentSpace` and `AlgebraicGeometry.schemeTangentMap`.
- `Sheaf.AlgebraicGeometry.GroupAdditionTangentDifferential`,
  `AlgebraicGeometry.group_addition_tangent_differential` (used by the stage-3 proof).
- The group-scheme notion is `CategoryTheory.GrpObj` as recorded by
  `def-sc-group-scheme`.

The identity-point transport is rendered by the unit-hom law
`IsMonHom.one_hom`; no additional hypothesis is introduced.  Edge cases checked include
`d = 1` (the base induction case), positive characteristic (the scalar is the natural
number action), and arbitrary field universe `Type u`.  The source's empty/zero cases do
not apply because the statement assumes `d ≥ 1`.

Searches made: `msearch.py leanfinder` for “differential multiplication by n group scheme
 tangent space” (no algebraic-geometry tangent theorem); `msearch.py loogle` for
“tangent nsmul” (unknown identifier); `msearch.py grep` for `nsmul.*tangent|tangent.*nsmul`
(no matches); `rg` over `WeilConjectures` and `lean/Sheaf` for multiplication/tangent
names (only the recorded group-addition and tangent-space declarations).  No exact
existing declaration states this theorem.

## Earlier second reading (a previous round; superseded)

The statement was checked against the node clause by clause: `k` is a field, `G` is a
commutative group scheme, `e` is `GrpObj.onePoint G`, and the positive integer condition
is `hd : 1 ≤ d`.  The morphism `[d]` is the existing group-object power `𝟙 G ^ d`; the
residue-field bijection and identity-point transport are the data needed to form its
`tangentMap`.  The conclusion is pointwise equality with `d • v` on the tangent space at
the identity.  No definition is duplicated and no hypothesis is added beyond the explicit
positivity condition already present in the node statement.

## Second reading by N1

I independently read the item node, all four dependency nodes, SchemeTangentSpace.lean,
GroupAdditionTangentDifferential.lean, and the upstream GroupScheme/Defs.lean and Basic.lean.
The repository lacks the Stacks checkout; I read the available identical source place in
/home/ubuntu/c1-stacks-review/groupoids.tex, lemma-group-scheme-addition-tangent-vectors.
It assumes only a scheme S, group scheme G/S and point s; specialization to Spec k imposes
no smoothness, finiteness or characteristic hypotheses. Its proof uses the two unit
inclusions, functoriality and linearity, exactly the induction recorded in this node.

Clause-by-clause inventory and verdict:

- Field k: `(k : Type u) [Field k]`; exact, arbitrary universe u.
- Commutative group scheme G/k: `(G : Over (Spec (.of k))) [GrpObj G]
  [IsCommMonObj G]`; exact. The recorded group-scheme declaration is the general group
  object, specialized here to schemes over the field, with no extra geometric instances.
- Identity e: `GrpObj.onePoint G`, defined in upstream GroupScheme.Basic as the image of
  the unique point of Spec k under the unit section; exact.
- Integer d at least one: `(d : ℕ) (hd : 1 ≤ d)`; exact positive integer range.
- Multiplication morphism [d]: `(𝟙 G ^ d).left`; exact. Upstream Defs documents the
  pointwise hom-group power and `isMonHom_npow_id` supplies its homomorphism instance.
  This is the recursive multiplication already used by the dependency node. Only this
  part of that dependency is needed here; its other recorded clauses are not replaced.
- Tangent space at e: `schemeTangentSpace k G.left G.hom (GrpObj.onePoint G)`; exact
  dependency definition, dual-number k-morphisms with prescribed closed point. Its
  canonical additive group and residue-field module are selected from named existence
  theorems, not hollow definitions.
- Differential at e: `schemeTangentMap ... (𝟙 G ^ d).w ... he`; exact dependency
  linear map with prescribed postcomposition formula. The existential `he` supplies
  bijectivity of the induced residue map, guaranteed since e is rational and [d] is over k.
- Same source and target tangent space: existential `hp` asserts [d](e)=e, and `hp ▸`
  transports the differential value to that tangent space. This is required typing data,
  already intrinsic to the node, not an extra hypothesis or a new geometric assertion.
- Scalar conclusion: for every vector v the transported value equals `d • v`; exact.
  Natural-number repeated addition equals multiplication by d in the canonical residue
  field vector space, including when the characteristic divides d. Quantifiers are
  witnesses of typing facts followed by all v, without existential choice of a map.

Edge cases: d=0 is excluded by the node itself; d=1 gives identity. The trivial group
scheme and zero tangent space are included. An empty group scheme over a field cannot
have a unit section, so no allowed empty case is lost. There is no index set. No
characteristic restriction, algebraic closure, smoothness, Noetherian, finite-type or
separatedness binder was introduced. Both field and scheme live in arbitrary u, as the
recorded tangent-space dependency requires; there are no independent test universes.

Independent searches: msearch LeanSearch for “The differential of the power endomorphism
of a commutative group scheme at its unit is repeated addition on tangent vectors” was
unavailable (Internal Server Error); Loogle `"tangent", "pow"` returned only analytic
cone and Euclidean sphere results; Mathlib AlgebraicGeometry grep
`tangent.*(pow|power|mul)|differential.*(pow|power)` returned no matches. Direct rg on
upstream WeilConjectures and project lean/Sheaf for power/multiplication differentials
found group addition, unrelated ring differentials and commutator statements, no exact
multiplication-by-d theorem. No definition was added or duplicated.

Mismatches repaired: removed the prohibited `show ... from` and inline proof in the
transport, replacing them with existential fixed-point proof data `hp`. Removed the
unused group-addition import (a stage-3 proof dependency), which also lacked an olean in
the current build. Added direct upstream Basic import for onePoint and retained Defs for
the power homomorphism instance. Added the standard copyright header and explicit
transport-witness explanation and dependency names in the proof docstring. All actual
theorem proofs remain `sorry`. The natural-language node statement was not changed;
there are no new nodes, dependency modules or statement_change records. Updated
lean.statement verbatim to the repaired signature. Compiled the repaired single module
with scompile; only long docstring lines remained and were shortened before final check.
