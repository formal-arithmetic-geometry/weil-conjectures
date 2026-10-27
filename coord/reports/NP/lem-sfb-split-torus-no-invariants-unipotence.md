## Worker report

The module `Sheaf.AlgebraicGeometry.SplitTorusNoInvariantsUnipotence` states
`AlgebraicGeometry.splitTorus_noInvariants_splitUnipotent`, with `sorry` as its entire proof.
It introduces no new definitions and leaves the natural-language statement unchanged.
The docstring follows all five proof steps of the node, including the corrected big-cell
argument in place of the invalid strict-definiteness inference in Milne 16.62.

Hypothesis and conclusion correspondence:

- The arbitrary field is `(k : Type u) [Field k]`; no characteristic or perfectness
  instance is present.
- The group schemes are `H S : Grp (Over (Spec (.of k)))`. This is the bundled form
  of the recorded `CategoryTheory.GrpObj` definition, including all scheme group laws.
- Affineness is `[IsAffine H.X.left]`, finite type is the pair
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, smoothness is
  `[Smooth H.X.hom]`, and geometric connectedness is
  `[GeometricallyConnected H.X.hom]`. Mathlib's definition tests connectedness of
  all field pullbacks; over a field it is equivalent to connectedness after algebraic closure.
- The split torus of arbitrary nonnegative rank is `(r : ℕ)` and
  `hS : Nonempty (S ≅ MultiplicativeType.splitTorus k r)`. The isomorphism is in
  group schemes, rather than merely schemes or abstract groups.
- The algebraic action is `[ModObj S.X H.X]`: the morphism, identity and
  associativity equations are part of that structure. `hAut` uses the existing
  `TorusCharacterTangent.ActsByGroupAutomorphisms S H`, which imposes preservation
  of multiplication on every test scheme. Inverses in S make these endomorphisms
  automorphisms. No arbitrary tangent representation is supplied.
- `GrpObj.Lie H.X` is the canonical relative identity tangent space, identified
  with the recorded `schemeTangentSpace` by the existing
  `GrpObj.lieIdentityTangentEquiv` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv` (read in full).
  Its `GrpObj.tangentPoint v` is the actual point with values in k[epsilon].
- `hInv` says a vector is zero if, for every commutative k-algebra R and every
  `s : points S.X R`, its scalar-extended tangent point is fixed. The left term
  `points.map S.X (TrivSqZeroExt.inlAlgHom k R R) s` is the constant lift of s
  to R[epsilon]. The coefficient map is the inlined Mathlib
  `DualNumber.lift ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
  DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩`. It fixes the square-zero
  coordinate and applies k → R to the coefficients. Both occurrences
  of the vector are its canonical extension by `points.map H.X`. Thus this is
  the algebraic fixed subspace, including tests over nonreduced R, and does not
  differentiate characters or test only S(k). Injectivity of the canonical
  tangent-point identification identifies this condition exactly with h^S = 0.
- The finite chain is `m : ℕ`, `U : Fin (m + 1) → Grp ...`, with
  `Nonempty (U 0 ≅ H)` and `Nonempty (U (Fin.last m) ≅ Grp.trivial _)`.
  Every term has `Smooth` and `GeometricallyConnected` structure morphism.
  Every step has a group-scheme map `i : U a.succ ⟶ U a.castSucc`, with
  `IsClosedSubgroupScheme i.hom.hom` and `IsNormalSubgroupScheme i.hom.hom`.
  Composing these inclusions and the first isomorphism makes every term a closed
  k-subgroup of H. The actual quotient map is
  `q : U a.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k)`.
- `SolvableGroupStructure.IsFppfQuotient i.hom.hom q` gives flatness, surjectivity,
  local finite presentation, and the identification of i with the scheme-theoretic
  kernel. This is the recorded represented fppf right-coset sheafification convention.
  Since q is between affine finite-type schemes, its covering is finitely presented.
- The matrix assertion is `SolvableGroupStructure.IsUnipotent H`, whose full
  definition was read: it supplies a closed faithful finite-dimensional matrix
  representation and, over every algebraically closed extension field, a positive
  integer N with `(matrix - 1)^N = 0`.

Dependency declarations used (full source signatures and docstrings read):

- `Field`, in `Mathlib.Algebra.Field.Defs`.
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, in
  `Mathlib.CategoryTheory.Monoidal.Grp`; group-scheme specialization and
  `IsClosedSubgroupScheme` / `IsNormalSubgroupScheme` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `LocallyOfFiniteType`, `QuasiCompact`, `Smooth` in the recorded Mathlib morphism
  modules `FiniteType`, `QuasiCompact`, `Smooth`.
- `ConnectedSpace`, in `Mathlib.Topology.Connected.Basic`, and its geometric
  specialization `GeometricallyConnected`, in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`.
- `StandardGroupSchemes.additive` and its canonical group instance in
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `schemeTangentSpace`, its canonical additive/module structures and
  `schemeTangentMap`, in `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`.
  The statement uses its canonical identity Lie model via `GrpObj.tangentPoint`.
- `SolvableGroupStructure.IsUnipotent` and `.IsFppfQuotient`, in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.
- `MultiplicativeType.splitTorus`, in
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`;
  `TorusCharacterTangent.ActsByGroupAutomorphisms`, in
  `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`.
  These two already recorded definition nodes are added to stmt_deps; no node is restated.
- `DualNumber`, `DualNumber.eps` and the universal coefficient map `DualNumber.lift`,
  in `Mathlib.Algebra.DualNumber`, owned by `def-sc-dual-numbers`.
- `GrpObj.Lie` and its tangent-point realization, supplied through the recorded
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` module of
  `def-wf-lie-algebra-derivation`, which is now explicitly in stmt_deps. The full
  definition Lie := Hom(e*Omega,O) and tangentPoint signature/docstring were reread.
  Its upstream module defines the notion over every field, as required here.
  The weight-space definition in TorusCharacterTangentWeights tests rational points
  and is deliberately not used for the arbitrary-field invariant condition.

The stated proof dependencies available on the base are imported: proper/smooth
base change (`Mathlib.AlgebraicGeometry.Morphisms.Proper`, smoothness available from
public imports), smooth composition (same Smooth module), geometric connected
product components (Geometrically.Connected), and Borel/maximal-torus conjugacy
(`Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy`). The seven other
proof dependencies have no Lean record or Mathlib match yet; they are retained as
proof dependencies and named in the proof docstring, and none is needed to type
this stage-2 statement.

Edge cases checked before writing: r = 0 is permitted by splitTorus's unit case;
then all tangent vectors are fixed and the hypothesis forces zero tangent space.
H = 1 admits m = 0, with a single term and no quotient steps. Empty tangent
spaces and rank-zero matrix spaces are permitted. Finite fields, imperfect fields,
and positive characteristic are not excluded. In particular a character t^p in
characteristic p is tested by its algebraic action on every R, not by its zero
Lie differential. The zero test algebra is allowed. Every variable and universe
is explicit and `autoImplicit` is false. No local notation or local instance is used.
The series conclusion expressly includes geometric connectedness. The existing
recursive interface `SplitUnipotentLength` defines the same split additive series;
the equivalent explicit chain is retained, as accepted by the return. No new
splitness predicate or alternative definition is introduced.

Searches for an existing statement:

- `msearch.py ... leanfinder "A split torus action without invariant tangent vectors
  forces split unipotence"`: eight hits about Lie algebra Cartan subalgebras,
  generalized weight spaces, triangularizable Lie modules and root pairings;
  no group-scheme theorem.
- `msearch.py ... loogle '"Unipotent"'`: six categorical biproduct unipotent
  matrix isomorphisms; no algebraic group result.
- `msearch.py ... grep 'SplitUnipotent|splitUnipotent|torus.*unipotent|unipotent.*torus'`:
  no Mathlib hits.
- `rg` in the named `lean/WeilConjectures` and `lean/Sheaf` directories, for the
  item id, split torus invariants, SplitUnipotent and action/tangent names:
  no existing theorem matching this criterion. Found and reused the above action,
  split torus, dual-number maps, unipotence and quotient interfaces. The existing
  `SplitUnipotentLength` definition has smooth connected terms; the statement here
  directly asserts a finite chain with geometrically connected terms, adding no
  alternative definition.

Source checked: extracted the local Milne PDF around printed pp.345--347 and read
Theorem 16.58 and Propositions 16.62--16.63. The split-unipotent conclusion agrees
with 16.63; the item's proof already records the replacement for strict definiteness.
Also read the latest blueprint's standard-group-scheme source location.
No statement correction or STATEMENT-DISPUTED issue was found.

Validation: the original delivered file compiled in sandbox and library module mode.
The repaired file passed scompile.py in sandbox and library module mode with
exit code 0 and no errors or non-sorry warnings (reported elapsed times 475.2 s
and 3.8 s; the wrapper includes server scheduling/dependency work). The requested
per-file timeout was not changed. The delivery wrapper repeats compilation and
preflight against the refreshed live main branch.

## Repair of immutable head 205b632f0e5f

Compared the retained sandbox packet with the current main node. Only `lean` and
`stmt_deps` differed. Rebuilt the node copy from current main, retained its statement
and proof unchanged, and regenerated the verbatim Lean signature after the repair.
The delivery wrapper refreshes main before building the replacement delivery commit.

H2 (1): took the return's inline construction option. Removed the public import of
`Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus` and both occurrences of its
`dualMap`. Each occurrence now uses the exact `DualNumber.lift` expression requested
in the return. Added the owner `def-sc-dual-numbers` to stmt_deps and removed the
incorrect theorem dependency `lem-sfb-affine-group-dual-number-calculus`. No new
node, copied definition, or unowned plain helper is introduced. The canonical map
sends a + b epsilon to algebraMap(a) + algebraMap(b) epsilon, so the mathematical
fixed-vector condition is unchanged.

H2 (2): added `def-wf-lie-algebra-derivation` to stmt_deps and publicly imported its
recorded module `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`.
This records the existing owner of `GrpObj.Lie` and its tangent-point realization.
The node's newest blueprint text explicitly describes Lie for any group scheme,
and the recorded Lean declarations have no algebraically-closed or characteristic
restriction; adding the owner adds no hypotheses to this item.

H11: replaced the previous dispatcher wording with the actual second reading below.
No independent worker was spawned, following this item's explicit isolation rule;
this is a second pass by the dispatched worker, not a claim of independent review.
The maintainer still performs the independent review.

Advisory on `def-sfb-split-unipotent-series`: reread its recursive declaration.
`SplitUnipotentLength` already defines split additive series. The present explicit
finite-chain conclusion is an equivalent way to spell out the terms and quotients,
with the requested geometric connectedness visible. Retained this reviewer-accepted
conclusion and introduced no second definition of split unipotence.

## Second reading by NP

Second pass with the node statement and the repaired Lean file open, checking every
hypothesis and clause rather than relying on the compiler:

1. The node's arbitrary field k is exactly `(k : Type u) [Field k]`. There is no
   hidden perfectness, characteristic-zero, infinitude or algebraic-closure binder.
   `H S : Grp (Over (Spec (.of k)))` are schemes over the same field with their
   actual group objects, not abstract groups of rational points.
2. The four geometric restrictions on H match independently: `IsAffine` on its
   underlying scheme; `LocallyOfFiniteType` and `QuasiCompact` on its structure
   map for finite type; `Smooth` on that map; and `GeometricallyConnected` on that
   map. There is no extra restriction on S beyond its split torus isomorphism.
3. `r : ℕ` permits r = 0. `Nonempty (S ≅ MultiplicativeType.splitTorus k r)` is an
   isomorphism of group objects and hence includes the split torus group law.
   It does not replace the stated split torus with one split only after extension.
4. `ModObj S.X H.X` supplies the actual action morphism with its identity and
   associativity laws. `hAut` supplies multiplication preservation on all test
   schemes, hence group automorphisms. These match all the action axioms in the
   node, and no arbitrary linear action is substituted for differentiation.
5. `v : GrpObj.Lie H.X` is the relative tangent vector at the identity. Its
   canonical `GrpObj.tangentPoint v` is a k[epsilon]-point reducing to 1.
   Reread Lie.Basic and Lie.Ring for these types and definitions; their owner is
   now `def-wf-lie-algebra-derivation`. The existing identity tangent equivalence
   relates this model to the recorded general scheme tangent space.
6. In `hInv`, R ranges over every commutative k-algebra in the project's universe,
   and s ranges over every R-point of S. The inlined `DualNumber.lift` has source
   k[epsilon] and target R[epsilon]; its coefficient map is `Algebra.ofId k ...`
   and its epsilon image is epsilon. Thus each `points.map H.X` is the scalar
   extension of the *same* v. The `inlAlgHom` term gives the constant R[epsilon]
   lift of s. Equality states precisely fixedness of that tangent vector under
   s after extension. The implication to v = 0 is exactly vanishing of the fixed
   subspace. It tests all algebras, including nonreduced and zero algebras, rather
   than only k-points or the Lie algebra of S. Found no mathematical mismatch;
   found and fixed the original unowned helper/theorem stmt_dep mismatch.
7. The existential m and `Fin (m + 1)` family give finitely many terms with the
   first isomorphic to H and the last to the trivial group. Every term explicitly
   satisfies `Smooth` and `GeometricallyConnected`. The first isomorphism and the
   composite inclusions identify the terms as actual closed k-subgroups of H.
8. At each `a : Fin m`, the arrow goes from `U a.succ` to `U a.castSucc`, so the
   series descends in the stated direction. `IsClosedSubgroupScheme` and
   `IsNormalSubgroupScheme` express exactly closedness and normality in the
   predecessor, not just normality of rational points.
9. Each q is a homomorphism to the existing standard additive group. The recorded
   `IsFppfQuotient` imposes flatness, surjectivity, local finite presentation and
   a kernel identification commuting with i. This represents the stated fppf
   sheafification of right cosets and does not assume surjectivity on every
   algebra's points. No multiplicative quotient is allowed in this series.
10. The final conjunct `IsUnipotent H` uses the previously read faithful closed
    matrix representation definition, quantified over all algebraically closed
    extension fields and their points, with a positive nilpotence exponent N.
    This renders the node's additional matrix clause without adding a chosen
    representation as a hypothesis.
11. For m = 0, there is one term, endpoint isomorphisms force H = 1, and there
    are no quotient steps; the statement therefore includes the empty series.
    For r = 0 every tangent vector is fixed, so hInv forces the zero tangent
    space, as required. Finite fields and characters t^p in characteristic p
    remain covered by all-algebra testing. There are no new definitions with
    postponed data, no auto-bound variables, and the sole postponed proof is
    the named item theorem. No additional statement mismatch was found.

The repair changes the canonical coefficient-map expression, imports and dependency
ownership only; it preserves the reviewer-accepted mathematical content. This
second reading found both reported ownership omissions and the absent actual
second-reading text, all now repaired.
