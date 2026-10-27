## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup` states
`AlgebraicGeometry.charZero_commutative_unipotent_vectorGroup`. Its sole theorem has
proof `sorry`; it defines no new objects and proves nothing. The docstring gives
all nine steps of the current accepted split. The node is copied from the live
read clone, and only its `lean` field changes. In particular Q86's reviewed proof,
proof dependencies and review record are preserved.

I read Milne, Algebraic Groups (2017), Proposition 14.32, Corollary 14.33 and the
following paragraph, printed p.289 (PDF page 301), and their proof. Proposition
14.32 supplies the exponential isomorphism, which is a group isomorphism for a
commutative group; 14.33 and its following paragraph identify the group with a
finite power of Ga after choosing a basis. The inherited BLOCKED ending was a
stage-1 supersession issue. The explicit stage handoff in brief-stage2 section 0
permits a stage-2 statement of the accepted split, which is what this packet does.

Hypothesis and clause correspondence:

- The field k is `{k : Type u} [Field k]`; characteristic zero is `[CharZero k]`.
- A k-group scheme is `G : Grp (Over (Spec (.of k)))`. Its underlying k-scheme is
  `G.X`, with structure morphism `G.X.hom`; the bundled group structure supplies
  the multiplication, identity and inverse diagrams.
- Affineness is `[IsAffine G.X.left]`. Finite type is the conjunction expressed
  by `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Smoothness is `[Smooth G.X.hom]`. Connectedness is
  `[ConnectedSpace G.X.left]`, including nonemptiness. Commutativity is
  `[IsCommMonObj G.X]`.
- The existence of n >= 1 is the opening `∃ (n : ℕ), 0 < n ∧` in
  `hunitriangular`. The matrix indices are `ULift.{u} (Fin n)`: this is a copy of
  the same finite index set in the universe required by the existing GL API.
  There is no restriction on n and no relation between distinct universe levels.
- The embedding is `r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k`, with
  `IsClosedSubgroupScheme r`. This recorded class includes the homomorphism
  condition, injectivity on every algebra's points and closed immersion.
- Its target is restricted to U_n by the two exact coordinate equations, for
  every `(R : Type u) [CommRing R] [Algebra k R]` and every R-point `x` of G:
  the diagonal entries of `(GeneralLinearGroup.homMulEquiv ... (x ≫ r)).val`
  are one, and its entry `(i,j)` is zero whenever `j < i`. Invertibility is
  already part of GL. No condition is placed on entries strictly above the
  diagonal. Thus these equations are precisely upper unitriangular matrices,
  on every commutative algebra, not merely geometric points.
- This is the same embedding hypothesis as a closed immersion into U_n.
  Composing such an immersion with U_n -> GL_n gives exactly the displayed
  conditions. Conversely the universal point on the affine coordinate algebra
  of G satisfies them, so their defining functions vanish on G. The coordinate
  map from k[GL_n] therefore factors through the quotient defining U_n, and
  the factor map remains surjective. Hence the factorization G -> U_n is a
  closed immersion and a group homomorphism. This inline rendering requires
  neither a second definition of unipotence nor a new unitriangular object.
- The conclusion is `∃ d : ℕ, Nonempty ((∏ᶜ (fun _ : Fin d ↦
  Grp.mk (StandardGroupSchemes.additive k))) ≅ G)`. A natural number is exactly
  an integer d >= 0. The isomorphism is in the category of group objects over
  Spec k, so preserves the k-structure and the group operations in both
  directions. It is stronger than a mere scheme isomorphism only in exactly
  the way required by the node: it is a group-scheme isomorphism.
- `StandardGroupSchemes.additive k` is the dependency's actual Ga, Spec k[y]
  with comultiplication y -> y tensor 1 + 1 tensor y, counit y -> 0, and
  antipode y -> -y. Its finite categorical power is Ga^d with componentwise
  addition. Limits of group objects are created in the underlying category,
  so for d=0 this is the terminal k-group scheme, namely Spec k with trivial
  group law. No nonempty condition on `Fin d` is imposed.

Recorded dependency declarations read and reused:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`, line 180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  `CategoryTheory.IsCommMonObj` and `CategoryTheory.IsMonHom`, in
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Mon`. These are exposed by the
  recorded subgroup/additive modules; the bundled Grp is used for the conclusion.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, line 43, and
  `AlgebraicGeometry.QuasiCompact` in `.QuasiCompact`, line 43.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, line 62, imported publicly.
- `def-weil-connected-scheme`: `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, line 705.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, with its full
  inherited `IsSubgroupScheme` / `IsMonHom` fields and closed immersion field.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.additive`,
  `additiveComul`, `additiveCounit`, `additiveAntipode` and `additiveGroup` in
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`. I read the definitions and
  the unique group-law characterization; the statement uses this exact group.

Other existing API used: `AlgebraicGeometry.GeneralLinearGroup` and
`.homMulEquiv` in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`;
`CategoryTheory.Grp` limits in `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`.
Both are reused, not copied. Plain proof imports include the recorded additive
subgroup polynomial quotient, connected rational point, affine normal quotient
and tangent-space modules. The remaining proof prerequisites have no Lean
record in the read clone and are described by their node ids in the docstring.

Edge cases checked before writing: n=1 forces every image matrix to be [1],
so the closed embedding forces G to be trivial and the conclusion permits d=0.
The trivial group embeds also for larger n. Ga embeds in U_2, and Ga^d has
its standard block embedding; no positive-dimensional case is excluded.
Noncommutative U_3 is excluded by the explicit commutativity hypothesis.
Positive characteristic is excluded by CharZero; the additive-polynomial
coefficient argument is not valid there. The empty scheme is excluded by
ConnectedSpace and independently by the group identity. Nonreduced test
algebras are retained; checking only field points would lose scheme-theoretic
information and is not the statement here. All test algebras have the base
field's universe, so the coordinate algebra of the arbitrary affine G is
available as a test; this hypothesis is not vacuous in any universe.

Searches actually run (through the prescribed msearch.py wrapper):

- leanfinder: `A smooth connected commutative unipotent group scheme in characteristic zero is a finite product of additive groups`.
  Eight hits: AffineSpace, a smooth cotangent lemma, a Galois-category lemma,
  CommGroup.nilpotencyClass_le_one, two Lie-group instances, and two unrelated
  instances. None states this algebraic-group theorem.
- loogle: `"IsMonHom", "GrpObj"`. Zero hits.
- grep: `unitriangular|vectorGroup|commutative.*unipotent`. Zero Mathlib hits.
- leansearch: `Every commutative unipotent affine group scheme over a characteristic zero field is isomorphic to a finite power of the additive group`.
  Eight hits concerning additive group categories, a representation instance
  and characteristic-zero conversion. No matching theorem.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `unitriangular|vector.?group|commutative.*unipotent|unipotent.*commutative`
  found documentation in a matrix file, PerfectSolvableUnipotentTorus and
  SplitSolvableTorsorsAndVariety; none states this theorem. The explicit node-id
  search of `lean/WeilConjectures` found nothing. Subsequent searches located
  the existing GL, additive-group and finite-product APIs used above.

No new nodes, dependency repairs, statement corrections or STATEMENT-DISPUTED
findings are needed. All variables and the universe are bound explicitly and
`autoImplicit` is disabled. The initial scompile.py run compiled both the
sandbox check and the library module cleanly (only the expected sorry is
postponed). The delivery dry run is recorded below when complete.

Validation: deliver2.py --no-push printed `OK (dry run): commit c2a06e1f33a
passes the preflight and compiles; nothing pushed`. The packet contains exactly
this report, the item's node and its one module. The wrapper supplies the
administrative second-reading section stating that no worker second reading
was performed: the maintainer's independent review is the review for this
self-delivered assignment.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
