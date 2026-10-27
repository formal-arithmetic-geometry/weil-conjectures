## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CommutativeMultiplicativePart` states
`AlgebraicGeometry.commutative_multiplicative_part`. Its sole theorem has proof `sorry`.
There are no new definitions, dependency repairs, new nodes, or statement corrections.
The original node is copied unchanged except for its `lean` field.

Source checked directly: Milne, Algebraic Groups (2017), Theorem 16.13(a), printed
p.328, and Note 16.17, printed p.329, extracted from the supplied PDF. The first gives
the largest multiplicative subgroup and unipotent quotient; the note explicitly gives
commutation with extension of the base field. The node does not include the theorem's
additional characteristic-subgroup assertion, and neither does this Lean statement.

Hypotheses and clauses, in order:

- The base field is `{k : Type u} [Field k]`; the group scheme is
  `C : Grp (Over (Spec (.of k)))`. Its group operations are the recorded group-object
  operations, and morphisms in this category are group homomorphisms.
- Affineness and finite type are `[IsAffine C.X.left]`,
  `[LocallyOfFiniteType C.X.hom]`, and `[QuasiCompact C.X.hom]`.
  Commutativity is `[IsCommMonObj C.X]`. No smoothness, connectedness, reducedness,
  characteristic, or perfectness assumption occurs.
- The asserted subgroup and quotient are the existential group schemes `S Q`,
  with maps `i : S ⟶ C` and `q : C ⟶ Q`.
  `SolvableGroupStructure.IsAlgebraic S` and `IsAlgebraic Q` express their affine
  finite-type status exactly as the node's convention for all groups.
- Closed subgroup inclusion is `IsClosedSubgroupScheme i.hom.hom`.
  Multiplicative type is the recorded `MultiplicativeType.IsMultiplicativeType S`:
  after scalar extension to `AlgebraicClosure k`, there is a closed subgroup
  inclusion into `MultiplicativeType.splitTorus (AlgebraicClosure k) n` for some
  natural `n`, including `n = 0`. This uses the actual recorded multiplicative group.
- Largest means the universal factorization clause for every `H` and `j : H ⟶ C`:
  if `j` is a closed subgroup and `H` has multiplicative type, then
  `∃ f : H ⟶ S, f ≫ i = j`. Affine finite type of such an H follows from its closed
  inclusion into the affine finite-type C; no restriction on the test subgroups is added.
- The represented fppf quotient is
  `SolvableGroupStructure.IsFppfQuotient i.hom.hom q`. Its existing definition says
  that q is flat, surjective, locally finitely presented and that S is its
  scheme-theoretic kernel with the specified inclusion i. Its docstring explains
  the coset sheafification: local lifts exist and two lifts differ by a unique
  kernel point. Because the groups are affine finite type over a field, the
  morphism is quasi-compact and quasi-separated, so this is the finitely presented
  faithfully flat quotient of the node, not only a quotient on k-points.
- Unipotence is the displayed `∃ n : ℕ, 0 < n ∧ ∃ r ...` clause. The map
  `r : Q.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k` satisfies
  `IsClosedSubgroupScheme r`, hence is a group homomorphism and closed immersion.
  For every commutative k-algebra A and every A-point x, `homMulEquiv` identifies
  its image matrix; all diagonal entries are 1, and the entries at (a,b) for b < a
  are 0. These are precisely the equations of the closed subgroup U_n in GL_n.
  Thus r factors through U_n, with closed immersion into U_n: a surjection onto
  k[Q] factors through the quotient imposing these equations. Conversely a closed
  subgroup embedding into U_n gives exactly this condition. This avoids introducing
  another unitriangular construction or using smooth geometric unipotence.
- For every `(K : Type u) [Field K] [Algebra k K]`, use the recorded
  `MultiplicativeType.baseChange`. The actual mapped inclusion `baseChange.map i`
  is closed, its source `baseChange.obj S` has multiplicative type, and every
  multiplicative-type closed subgroup of `baseChange.obj C` factors through this
  same inclusion. This says `(C_s)_K` IS the largest subgroup `(C_K)_s`.
  Equality of closed subgroup schemes is expressed independently of presentations:
  two largest inclusions factor through each other, and their monomorphisms force
  these factors to be inverse isomorphisms commuting with the ambient inclusions.
  This is equality of represented subfunctors on all algebras, not just on K-points.
  The common universe u is arbitrary, as in the dependency's scalar extension API;
  all fields, schemes, extensions and test algebras can be placed in a common universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`; and
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsCommMonObj`
  (def-sc-group-scheme), with their specialization documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme` (def-sc-group-scheme-subgroup).
  The latter includes `IsClosedImmersion`, from its recorded Mathlib module
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, together
  with `IsAlgClosure` from Basic (def-weil-algebraic-closure), used inside the
  multiplicative-type definition.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange`, `splitTorus`, `IsMultiplicativeType`
  (def-sfb-tori-multiplicative-type).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup` (def-sc-gm-ga),
  used through the actual split torus. Its affine spectrum and maps are reused
  by the dependency constructions.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` (def-sc-general-linear-group)
  publicly imports the existing general-linear implementation
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`. The node's main recorded
  declaration is specialLinear, but its module explicitly uses this upstream GL
  for its general-linear clause, so no repair or duplicate is needed.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsAlgebraic`, `IsFppfQuotient`
  (def-sfb-solvable-group-structure).
  Its `IsUnipotent` is explicitly smooth geometric unipotence and is not the notion
  asserted in this item. We use the item's explicit matrix condition instead,
  following the already landed CharZeroCommutativeUnipotentVectorGroup and
  AdjointKernelCentralQuotientUnipotent statements. No dependency repair is needed:
  the quotient and algebraic-group portions of the recorded interface are usable.

Imports: statement dependencies are public (directly or through the three public
imports); already stated proof dependencies are plain imports. These include
AffineFiniteTypeAlgebra.affine_finiteType_algebra_of_field,
AffineNormalQuotientGeometry.affine_normal_quotient_geometry and
HomomorphismFactorization.algebraicGroup_homomorphism_factorization, plus the
Mathlib finite-type Noetherian, Noetherian-ring, affine tensor-product pullback,
affine coordinate Hopf-algebra and tensor-map interfaces. The remaining proof
nodes (faithfully-flat quotient universal property, unitriangular extension,
multiplicative-additive vanishing criterion, split-torus subgroup diagonalizability,
and diagonalizable-to-unipotent vanishing) have no recorded modules to import.
The theorem docstring preserves all seven steps of the node's proof.

Edge cases checked before writing:

- The trivial group has S = C, trivial quotient, rank-zero multiplicative embedding,
  and a unitriangular embedding with n = 1; no positive torus-rank condition is imposed.
- In characteristic p, mu_p has S = C and trivial quotient; alpha_p has trivial S
  and embeds into U_2 through its closed embedding in Ga. Smoothness is not inferred
  or assumed for these groups. Gm times alpha_p has S = Gm and quotient alpha_p.
- Ga has trivial multiplicative part; Gm has multiplicative part itself.
- Arbitrary imperfect fields and purely inseparable extensions are included.
- All matrix equations quantify over commutative algebras, including nonreduced
  algebras, so infinitesimal subgroup schemes are visible. n = 1 correctly gives
  the trivial unipotent group. No false empty-scheme case is introduced: a group
  scheme has its identity section.
- The identity extension is included in the final universal quantifier.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: "Every commutative affine algebraic group has a largest
  multiplicative type subgroup with unipotent quotient compatible with field
  extensions" returned eight abstract/Galois-group results, including
  Field.absoluteGaloisGroupAbelianization, frattini, ValuationSubring.decompositionSubgroup,
  InfiniteGalois.profiniteGalGrp and CommGroup.isSolvable. None is a group-scheme result.
- msearch.py loogle: `"GroupScheme", "CommGroup"` returned zero hits.
- msearch.py grep: `multiplicative.?type|unipotent.*quotient` returned three
  unrelated type-tag/to_additive hits and no relevant Mathlib theorem.
- rg on WeilConjectures, Sheaf and dag/lean_names_upstream.json for the item id,
  `commutative_multiplicative_part`, and largest/multiplicative combinations found
  no existing theorem. grep for the item id in WeilConjectures returned no match.
  The related MultiplicativeTypeLargestSubtorus theorem concerns a largest smooth
  torus INSIDE an already multiplicative-type group; it does not state this item.
- rg for unitriangular/IsUnipotent found the smooth predicate above and existing
  statements using the same explicit matrix equations for general unipotence.
  Reused those interfaces rather than introducing any duplicate definition.

Validation: scompile.py compiled the single delivered module both as sandbox and
as its intended library module, cleanly, within the default 60-second limits.
No STATEMENT-DISPUTED issue was found. No statement has been corrected.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
