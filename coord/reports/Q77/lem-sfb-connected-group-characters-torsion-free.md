## Worker report

The module Sheaf.AlgebraicGeometry.ConnectedGroupCharactersTorsionFree states
AlgebraicGeometry.character_eq_one_of_pow_eq_one, with its proof `sorry`.
It introduces no definitions and preserves every field of the accepted DAG split except `lean`.
The inherited BLOCKED ending concerned stage-1 re-splitting, whereas this stage-2 item has no
Lean record. The current brief-stage2 §0 explicitly authorizes this handoff. The queue marks
this item stage 2. No repair note exists for the item.

Hypothesis and clause matching:

- An algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- An F-group scheme: `(G : Over (Spec (.of F))) [GrpObj G]`. No commutativity is
  imposed on G. Over morphisms are morphisms over F, not arbitrary scheme maps.
- Affineness: `[IsAffine G.left]`.
- Finite type over F: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, precisely
  the recorded conjunction from def-weil-finite-type-morphism.
- Smoothness: `[Smooth G.hom]`.
- Connectedness including nonemptiness: `[ConnectedSpace G.left]`.
- A character χ: `(χ : G ⟶ StandardGroupSchemes.multiplicative F) [IsMonHom χ]`.
  The target is exactly the recorded Laurent Hopf group scheme, not its abstract F-points.
  IsMonHom imposes compatibility with the group laws (including the unit).
- An integer n ≥ 1: `(n : ℕ) (hn : 1 ≤ n)`. Positive integers and positive naturals
  give the same power criterion; neither n = 1 nor orders divisible by the characteristic
  are excluded.
- The identity χ^n = 1 of group-scheme morphisms: `(hχ : χ ^ n = 1)` in the Hom type.
- The conclusion χ = 1: `χ = 1` in that same Hom type. Thus this is equality of
  morphisms, not just equality on F-points. The positive-power criterion is the node's
  explicit meaning of torsion-freeness. Pointwise multiplication on the characters is
  the additive convention for X*(G) expressed multiplicatively.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field (definition class extending CommRing and DivisionRing).
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed (all polynomials split; its docstring
  identifies this with every nonconstant polynomial having a root). This is the
  algebraically-closed clause of def-weil-algebraic-closure's recorded Mathlib match.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj and IsMonHom, specialized
  to Over (Spec F), as instructed by def-sc-group-scheme; the project explanation in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs was read as well.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType, together with
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.Topology.Connected.Basic: ConnectedSpace, which includes Nonempty.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative, affine, multiplicativeGroup.
  These construct Spec F[t,t⁻¹] from the actual Laurent Hopf algebra.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Grp: CategoryTheory.GrpObj.Hom.group;
  its parent monoid structure defines pointwise multiplication and the constant unit map.
  The scoped CategoryTheory.MonObj instances must be opened for the powers and 1.

Proof-only dependencies are imported without `public`:
WeilConjectures.AlgebraicGeometry.Regular contains both IsRegular.of_smooth and
IsRegular.isIntegral (the latter also requires local Noetherianity, available from
finite type over a field). Mathlib.Algebra.Polynomial.Splits contains
Polynomial.Splits.eq_prod_roots, used with IsAlgClosed.splits.
Mathlib.Algebra.Polynomial.Laurent supplies LaurentPolynomial. The remaining recorded
proof notions IsIntegral and Spec are in Mathlib.AlgebraicGeometry.Properties and
Mathlib.AlgebraicGeometry.Scheme, already exposed by the statement imports.
The four proof steps are reproduced in the theorem docstring with their DAG references.

Source and edge cases: read Milne iAG2017, printed pp.392–393, Proposition 18.19 proof
and Theorem 18.25 proof, both using torsion-freeness because the group is smooth and
connected. Read the current latest blueprint direct-images proof (3); this is the existing
supporting algebraic-group node, not a change of that unit. Checked n = 1, trivial G = Spec F,
G_m (character lattice Z), and G_a (only the trivial character). Empty G is excluded by
ConnectedSpace and by the group identity section, as intended. In characteristic p, no
invertibility of n is assumed: repeated roots of T^n - 1 are allowed. Dropping smoothness
would fail for μ_p in characteristic p; dropping connectedness would fail for a nontrivial
smooth μ_n with n prime to the characteristic. No statement correction or dispute is needed.
The universe u is explicitly bound and arbitrary. All other binders are explicit.

Searches actually run for this assignment:

- msearch.py leanfinder: "The group of characters of a smooth connected affine group scheme
  over an algebraically closed field is torsion free". Eight results, including CharacterModule,
  MulChar.finite and IsAffineMonoid.toIsMulTorsionFree; none concerns scheme characters.
- msearch.py loogle: `"IsMulTorsionFree", "IsMonHom"`. Zero hits.
- msearch.py grep: `character.*torsion|torsion.*character|characterGroup`.
  Ten unrelated hits about characteristic-zero rings, ramification and root systems.
- msearch.py leansearch: "A finite order algebraic character of a smooth connected affine
  group scheme is trivial". Eight abstract MulChar/AddChar hits, no scheme theorem.
- rg over lean/WeilConjectures and lean/Sheaf with
  `character.*torsion|torsion.*character|characterGroup|lem-sfb-connected-group-characters-torsion-free`
  (case insensitive): only unrelated sheaf/torsion-character material, no matching statement.
- grep by the exact node id in lean/WeilConjectures: no hits.
- rg by `character_eq_one_of_pow_eq_one` in dag/lean_names_upstream.json,
  lean/WeilConjectures, lean/Sheaf and Mathlib: no collision.

Validation: first scompile run exposed the missing scoped Hom power instances; repaired by
opening CategoryTheory.MonObj. The second scompile run compiled the sandbox and actual
library module cleanly (5.0 s and 4.5 s), with no errors or unexpected warnings.

## Second reading by Q77

Reread the node and the final module in this worker session; no other agent was started,
as required by the dispatcher brief. The maintainer supplies the independent review.
F, the affine finite-type F-group G, smoothness and nonempty connectedness are all retained.
The character has exactly the recorded multiplicative-group target and the existing
IsMonHom condition; G is allowed to be noncommutative. The operations are the actual
pointwise Hom group operations, so the power hypothesis and conclusion express triviality
as scheme morphisms. Natural n with 1 ≤ n covers exactly the specified positive integer
orders. No reducedness, characteristic-zero, prime-to-characteristic, or rational-point
assumption was introduced. The only mismatch during elaboration was the absent scoped
instances; opening their existing scope fixed it without altering the mathematical statement.
No new or dependency modules were needed. Exactly one theorem is postponed and its full
four-step proof plan is in the docstring; there is no postponed data.
