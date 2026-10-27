## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric` states
`AlgebraicGeometry.isNormalSubgroupScheme_of_geometric_conjugations`, with `sorry`
as its entire proof. It introduces no definitions or additional nodes. The item
is changed only in `lean`; the Q81 accepted split, natural-language statement,
statement dependencies and proof dependencies are preserved verbatim.

The inherited BLOCKED ending concerned a stage-1 unchanged-item rejection.
The current assignment and queue say stage 2, and the item has no Lean record.
The stage handoff in brief-stage2 section 0 explicitly authorizes this statement
delivery through deliver2.py. There is no repair note for this item.

Source read: Milne, Algebraic Groups (2017), printed pp.31–33, in particular
Proposition 1.83 (the normalizer tests all extension algebras), Corollary 1.85
(the smooth ambient normality criterion), and Proposition 1.90. The latter
supplies the use in the parent solvable-group node. The current latest blueprint
unit sk-thm-sf-ctf-stability and its direct-images proof were also read. This is
an auxiliary input, not a change to the unit or its route.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The chosen algebraic closure is `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. This uses the recorded algebraic-closure notion, and
  allows any chosen closure rather than only a particular implementation.
- The k-group schemes J and N are `(J N : Over (Spec (.of k))) [GrpObj J]
  [GrpObj N]`. No commutativity of the groups is imposed.
- Affineness of both group schemes is `[IsAffine J.left] [IsAffine N.left]`.
- Finite type is `[LocallyOfFiniteType J.hom] [QuasiCompact J.hom]` and
  `[LocallyOfFiniteType N.hom] [QuasiCompact N.hom]`, exactly the conjunction
  prescribed by def-weil-finite-type-morphism.
- Smoothness is `[Smooth J.hom]`, exclusively on the ambient group.
- A closed subgroup N in J is `(i : N ⟶ J) [IsClosedSubgroupScheme i]`.
  This includes the homomorphism and injectivity on algebra-valued points.
- Every geometric point g of J is quantified by
  `g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ J`.
- Equality `Int(g)(N_Ω) = N_Ω` of subgroup schemes is rendered by equality
  between the conjugate image of the image of N(T) and the image of N(T),
  for every `T : Over (Spec (.of Ω))`. The functor
  `Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))` forgets a
  test scheme's Ω-structure down to its k-structure. By the ordinary
  base-change adjunction its morphisms to J and N are precisely the T-points
  of J_Ω and N_Ω. The canonical morphism `Over.homMk T.hom` pulls g to T;
  multiplication and inverse use the existing group on morphisms into a group
  object. `Set.image (fun x ↦ g_T * x * g_T⁻¹) (Set.range (fun n ↦ n ≫ i))`
  is exactly the conjugated subfunctor. Equality for all test schemes is
  equivalent by Yoneda to the stated equality of closed subschemes. It is
  not equality merely on Ω-valued points. Conversely, a subgroup-scheme
  equality gives every one of these pointwise equalities, so this imposes no
  extra mathematical condition.
- The conclusion is `IsNormalSubgroupScheme i`, the dependency's existing
  class: for every commutative k-algebra R its image subgroup is normal.
  Normality is equivalent to `j N(R) j⁻¹ = N(R)` for every j. No smoothness
  or connectedness of N, connectedness of J, or perfection of k is assumed.

The arbitrary scheme T formulation avoids constructing a second model of the
base-changed group. The equality is the usual functor-of-points expression of
equality of subgroup schemes, not a replacement by topological supports. Even
restricting T to affine Ω-schemes would detect the same equality; all schemes
are used here for direct Yoneda clarity. The scheme and ring universes are
explicitly u; T ranges over the same Scheme universe as J and N, not an
independent smaller universe. This includes the base-changed N itself, which
already tests the universal point. Every variable and universe is explicit.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs: def-weil-field.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and
  `CategoryTheory.Hom.group`, Mathlib.CategoryTheory.Monoidal.Cartesian.Grp:
  the group-object and point-group interfaces of def-sc-group-scheme.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme` and
  `IsNormalSubgroupScheme`, WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  def-sc-group-scheme-subgroup. Their full class signatures and docstrings
  were read. The normality class quantifies all commutative k-algebras.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, respectively
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  def-weil-finite-type-morphism.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth:
  def-sbc-smooth-morphisms.
- `IsAlgClosure`, Mathlib.FieldTheory.IsAlgClosed.Basic, exposed by
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure:
  def-weil-algebraic-closure. The recorded AlgebraicClosure construction
  and the record's stated IsAlgClosure interface were read.
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic, was read for
  def-weil-connected-scheme. Connectedness is explicitly not an assumption
  of this node, so no binder or otherwise unused import is added for it.
- `IsAffine`, Mathlib.AlgebraicGeometry.AffineScheme, is already exposed by
  the subgroup module. `Over.map` and `Over.homMk`, Mathlib.CategoryTheory.Comma.Over.Basic,
  and the canonical group operations render the existing scheme constructions.

Proof-only imports preserve the stated proof plan: Mathlib.AlgebraicGeometry.Pullbacks
for pullbackSpecIso; Mathlib.LinearAlgebra.Basis.VectorSpace for
Module.Free.of_divisionRing; WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
for Smooth.geometricallyReduced; and WeilConjectures.Mathlib.RingTheory.Nullstellensatz
for the three recorded affine Nullstellensatz declarations, especially clause 2,
eq_zero_of_forall_algHom_apply_eq_zero. The closed-immersion criterion and
base-change stability are already exposed by GroupScheme.Defs; the affine
finite-type criterion is exposed by the public FiniteType import.
The proof dependency lem-sfb-constant-source-closed-factorization-locus has
neither a Lean record nor a Mathlib match at this reading. It is not needed to
type the item, so no invented import or proof is supplied. Its place in the
unchanged proof plan is fully documented in the theorem docstring.

Edge cases checked before writing:

- N = J and the identity subgroup give the expected conjugation equalities.
- A disconnected finite constant group J is permitted; no ConnectedSpace or
  irreducibility instance occurs in the signature.
- In positive characteristic α_p inside G_a is permitted: N may be nonreduced
  and nonsmooth. Tests over Ω[ε]/(ε²) and all other nonreduced algebras remain
  part of the hypothesis. Restricting to Ω-points would lose this information,
  which is why the test-scheme quantifier is essential.
- A nonnormal subgroup of a smooth constant group fails hconj, so it is not
  an unconditional normality assertion. A smoothness hypothesis solely on N
  would not suffice; the statement retains precisely Smooth J.hom.
- Imperfect base fields and either characteristic are permitted; no
  PerfectField or CharZero binder occurs. Algebraic closure is algebraic,
  not assumed separable over k, just as in the node.
- The zero algebra is included in normal_range, and the empty test scheme
  occurs among T. An empty group scheme over a field is excluded by its unit
  section, rather than by an added nonemptiness hypothesis.
- Universe u is shared with the recorded subgroup-scheme API and is not
  an independent bound below the base field or ambient scheme.

Searches for an existing statement:

- msearch.py leanfinder, query "A closed subgroup scheme of a smooth affine
  algebraic group is normal if all geometric conjugations preserve it": 8 hits,
  including Subgroup.Normal.of_conjugate_fixed, Subgroup.Normal.conjAct,
  Subgroup.normalCore_isClosed, and Subgroup.Normal. These concern a single
  abstract or topological group, not extension from geometric conjugations to
  all algebra-valued points of a group scheme.
- msearch.py loogle, query `"normalizer", "Smooth"`: 0 hits.
- msearch.py grep, query
  `normalizer.*[Ss]mooth|[Ss]mooth.*normalizer|[Nn]ormal.*[Gg]eometric`: 0 hits.
- msearch.py leansearch, query "A closed subgroup scheme of a smooth affine
  algebraic group is normal if every geometric conjugation fixes it as a
  subgroup scheme": 8 abstract-group hits, including Normal.of_conjugate_fixed,
  Normal, Normal.conjAct, Normal.casesOn, Normal.conj_mem, Normal.mk,
  Normal.conj_smul_eq_self, Normal.conj_mem'. No scheme-theoretic criterion.
- rg searches of WeilConjectures and Sheaf for conjugation, normalizers,
  IsNormalSubgroupScheme, smooth normality and geometric normality found the
  existing subgroup classes, kernels, rational conjugation in
  GroupScheme.Basic, and unrelated scheme/ring normality. They give none of
  this theorem. The `conjBy` construction there is rational conjugation;
  our inline point expression uses the same existing group operations and
  does not define another conjugation map.
- The exact node-id search in WeilConjectures returned no hits. A source-tree
  search for the proposed theorem name and an upstream-name-index search
  returned no existing declaration. The parent PerfectSolvableUnipotentTorus
  mentions this node only in its proof docstring, not as an existing theorem.

No statement correction, new node, unusable dependency, or disputed statement
was found. The only postponed proof is the named theorem attached to this item.
All five accepted proof steps and their dependencies appear in its docstring.

Validation: scompile.py compiled the single file cleanly in both sandbox and
library module modes, within the default 60-second per-file limit. No warning
was emitted. Delivery preflight is run with deliver2.py --no-push, followed by
the prescribed delivery invocation.

## Second reading by Q66

No second worker was started: the task brief forbids starting agents and directs
the worker to deliver itself. The maintainer's independent review is the second
reading. A final self-check compared the node and file clause by clause: all
field, algebraic-closure, group, affine, finite-type, smoothness and closed
subgroup hypotheses are present; the conjugation equality is tested on every
Ω-scheme and retains nilpotents; the conclusion is the recorded normality
class. No connectedness or smoothness of N was introduced, and the accepted
split and statement remain unchanged.
