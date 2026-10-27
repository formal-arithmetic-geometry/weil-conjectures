## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety` states
`AlgebraicGeometry.exists_general_borel_flag_variety`, with its sole proof `sorry`.
It introduces no definitions or additional postponed theorems. No node statement is
changed. The existing landed `def-sfb-borel-subgroup-scheme` is added to `stmt_deps`
to reuse its Borel predicate instead of writing another one.

Source read: Milne, Algebraic Groups (2017), Theorem 17.9 and its proof, printed
p.354; the paragraph following Definition 17.12, printed p.355; Theorem 17.48,
printed p.367; Section 17f and Lemma 17.52 with its torus example, pp.368--369.
The theorem docstring records all eight steps of the accepted node proof,
including reducedness of the action source and the all-algebras stabilizer argument.

Hypothesis and clause matching:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  All variables and the universe are explicitly bound; `autoImplicit` is false.
- `G : Grp (Over (Spec (.of k)))` is the group scheme with its actual scheme
  multiplication, inverse and unit. `hG : SolvableGroupStructure.IsAlgebraic G`
  means exactly affine, locally of finite type and quasi-compact. The two instances
  `[Smooth G.X.hom] [ConnectedSpace G.X.left]` give the remaining hypotheses.
  There is no reductivity, characteristic-zero, positive-rank or dimension hypothesis.
- A Borel is a `Subobject G.X` whose representative carries a group structure for
  which `IsBorelGroupScheme ... B.arrow` holds. This is the existing definition:
  closed subgroup, smooth, connected, termination of the scheme-theoretic derived
  series, and maximality under subgroup factorization. The existential group
  structure is only a proof witness in a subtype predicate: no unspecified data
  are selected to construct the variety or the action. A monomorphism into a group
  admits at most one compatible group structure. Subobject equality identifies
  exactly isomorphic embeddings of the same subgroup, avoiding a bijection with
  duplicate presentations of one Borel.
- Solvability/unipotence/torus terminology is provided by the recorded
  `SolvableGroupStructure` module; the Borel predicate uses the recorded
  scheme-theoretic derived-series predicate from `GroupScheme.Semisimple`.
  The accepted node proof explains the equivalence of its finite-series and
  derived-series formulations. The statement does not quantify over unipotent
  groups or maximal tori; those words introduce background terminology only.
- `X : CategoryTheory.Mod (Over (Spec (.of k))) G.X` supplies the underlying
  k-scheme `X.X` and its internal action `ModObj.smul : G.X ⊗ X.X ⟶ X.X`.
  `ModObj.one_smul` and `ModObj.mul_smul` are precisely the unit and multiplication
  identities. The tensor is the fibre product over k, not an ordinary product
  of underlying sets. The induced action on every hom type is Mathlib's `•`.
- The first eight conjuncts are the stated `Nonempty`, `Smooth`, `ConnectedSpace`,
  `IsHProjective`, `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`
  assertions on the underlying scheme and structure morphism. `IsHProjective`
  is the node's finite projective-space embedding convention.
- The existential `b : {B : Subobject G.X // ...} ≃ (𝟙_ (...) ⟶ X.X)` is a
  literal bijection between Borels and all k-rational points. The terminal object
  of schemes over `Spec k` is `Spec k` with its identity map.
- Transitivity is the conjunct `∀ x y, ∃ g, g • x = y`, on k-rational points.
- Conjugation compatibility is `b C = g • b B ↔ ...`. The right side says on
  every commutative k-algebra A that z is in C(A) if and only if g_A⁻¹ z g_A
  is in B(A). Membership means factorization through the actual subobject arrow,
  so this is exactly C = gBg⁻¹ as subgroup schemes, not only on rational points.
  The equivalence is the presentation-independent form of the requested label
  identity. Since b is bijective, it also supplies the conjugate Borel for each g,B.
- The next conjunct is the requested stabilizer equality, element by element:
  `g • (toUnit ... ≫ b B) = toUnit ... ≫ b B ↔ ∃ t, t ≫ B.val.arrow = g`.
  It quantifies over every `A : Type u` with `[CommRing A] [Algebra k A]` and
  every g in G(A). `toUnit ... ≫ b B` is the scalar-extended point `(b_B)_A`.
  No reducedness or field condition is imposed on A, including the zero algebra.
- Every torus is contained in a Borel: for all `T : Grp ...`, `i : T ⟶ G`,
  `IsClosedSubgroupScheme i.hom.hom` and `SolvableGroupStructure.IsTorus T`,
  the next conjunct gives a rational point x, hence its Borel `b.symm x`, and a
  morphism j with `j ≫ (b.symm x).val.arrow = i.hom.hom`. Factorization is
  inclusion of subgroup schemes; compatibility with group laws follows by the
  monomorphism to G. The torus definition includes rank zero and splits over the
  algebraic closure; since k is algebraically closed this is the stated split torus.
- The final conjunct uses the same arbitrary torus inclusion and states for every
  Borel B that all its A-valued torus points fix `(b_B)_A`, for every k-algebra A,
  if and only if the inclusion factors through B. Since b is onto, this describes
  exactly all scheme-theoretically T-fixed rational points, as requested.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`.
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.Hom.group`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `AlgebraicGeometry.IsClosedSubgroupScheme`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic`, `IsSolvable`, `IsTorus`;
  the last is the existing `MultiplicativeType.IsTorus` abbreviation.
- Added landed dependency `def-sfb-borel-subgroup-scheme`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `AlgebraicGeometry.IsBorelGroupScheme`;
  it uses `IsSolvableGroupScheme` and `GroupSchemeDerivedLength` from
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`.
- Mathlib field/scheme/finite-type/smooth/connected/proper definitions:
  `Field`, `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`,
  `ConnectedSpace`, `IsProper`, `IsSeparated`, in the recorded dependency modules.
- `Mathlib.CategoryTheory.Subobject.Basic`: `Subobject`, its coercion to a
  representative object, and `Subobject.arrow`; no custom quotient or subgroup copy.
- `Mathlib.CategoryTheory.Monoidal.Mod` and `Monoidal.Cartesian.Mod`:
  `Mod`, `ModObj`, the action identities, and `CategoryTheory.Hom.mulAction`.
- The stated proof dependencies are imported without `public`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (Jacobson space),
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic` (closed-point residue field),
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (composition), and
  `Sheaf.RingTheory.SmoothAlgebraReduced` (`Algebra.isReduced_of_smooth`).
  Projectivity is already a public statement dependency. The other seven proof
  prerequisites currently have neither a Lean record nor a Mathlib match, so
  there are no modules for them to import. Their accepted proof steps are retained
  verbatim in the node and fully described in the theorem docstring.

Edge cases checked before writing: G=1, a torus, and a smooth connected unipotent
or other solvable group each have one Borel, themselves, so X is a point, with
full stabilizer. For GL₂, X is P¹; the diagonal torus fixes exactly the two Borel
points containing it. The rank-zero torus factors through every Borel and fixes
all X(k). Positive characteristic and nonreduced test algebras are retained;
no switch to the abstract group G(k) occurs in subgroup/stabilizer membership.
The empty scheme is not permitted as connected G or X, consistent with the node.
The same universe u for field, schemes and test algebras contains the coordinate
algebras needed for the universal-point/Yoneda tests; no independently smaller
universe is used. Subobject representatives may vary but the predicate and
membership condition are invariant under isomorphism.

Searches actually run (through `msearch.py Q03 lem-sfb-general-borel-flag-variety`):

- LeanFinder: `Smooth connected affine algebraic group projective variety of
  Borel subgroups and scheme theoretic stabilizers`: eight unrelated hits,
  including Proj, Galois-category actions and connected components; no match.
- Loogle: `AlgebraicGeometry, GrpObj, Borel`: zero hits, with diagnostic
  unknown identifier `AlgebraicGeometry`; this query alone is not negative evidence.
- grep: `Borel|borel|GroupSchemeAction` in `AlgebraicGeometry`: zero hits.
- LeanSearch: `Projective scheme of Borel subgroup schemes smooth connected
  affine group`: eight hits on schemes/smoothness, no matching theorem.
- Loogle: `CategoryTheory.ModObj` locates the internal-action predicate; its
  actual defining sources and `Mod` were read and reused.
- grep: `Subobject|IsBorelGroupScheme` in `CategoryTheory/Subobject` locates the
  generic subobject API, not a Borel-variety assertion.
- Direct `rg` in the project's `lean/Sheaf/AlgebraicGeometry` for Borel, IsTorus,
  IsSolvable and scheme actions found the existing Borel and solvability modules
  and the use of Mathlib `ModObj` in SchemeActionTorsorGroupoids; these were read.
- Direct `rg` in `lean/WeilConjectures/AlgebraicGeometry/GroupScheme` and the
  wider upstream tree found the group-scheme/subgroup API but no Borel variety.
  The exact item-id search in `lean/WeilConjectures` returned no match.
- The name search `borelSubobjects|exists_borel_flag_variety|general_borel_flag_variety`
  in `dag/lean_names_upstream.json`, `lean/Sheaf` and `lean/WeilConjectures` found
  no previously declared assertion. The delivered name is new.

Compilation: prescribed `scompile.py` compiled the sandbox and the destination
library module cleanly (6.2 s and 4.5 s), without errors or other warnings.
Initial diagnostics were repaired by opening the existing `MonObj` scope for the
scoped group-on-hom instance and typing the containment witness via `b.symm x`.
No new node, dependency repair, statement correction or disputed statement is needed.

## Second reading by Q03

I reread the original node and the final signature clause by clause after the clean
compile. This is a second pass by the assigned worker, not a claim of an independent
agent review: the dispatcher prohibits starting other agents, and the maintainer
performs the independent delivery review.

The field, affineness/finite type, smoothness and connectedness binders agree exactly.
The Borel subtype reuses the landed derived-series definition; taking subobjects,
rather than unquotiented embeddings, is necessary for the stated bijection. Its
existential compatible group structure does not enlarge the collection. The
bundled Mod carries a genuine scheme morphism and both identities. Every geometric
property of X appears explicitly, including properness, separatedness and both
finite-type conditions. The label map is an Equiv. The transitivity clause ranges
only over k-points as in the node. The conjugation equivalence has the correct
orientation: z in gBg⁻¹ precisely when g⁻¹zg is in B. Both this clause and the
stabilizer use all commutative test algebras. The torus existence clause picks
B=b.symm(x), and the final equivalence tests scheme-theoretic fixity for every
Borel point and torus, including rank zero. There is no maximal-torus restriction.
No mathematical mismatch was found or corrected. Only the two elaboration repairs
listed above changed the first draft. Every line is at most 100 characters, and
the JSON signature is extracted verbatim from the final file before `:=`.
