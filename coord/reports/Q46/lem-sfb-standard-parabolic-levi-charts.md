## Worker report

Item: `lem-sfb-standard-parabolic-levi-charts`. Group Q46, stage 2.

The delivery adds `Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts`,
with the single theorem `AlgebraicGeometry.standard_parabolic_levi_charts`, proved
by `sorry` as required in stage 2. There are no definitions, auxiliary postponed
lemmas, new nodes, dependency repairs or statement corrections. The theorem
asserts existence of representatives of precisely the subgroup schemes and
quotient in the node. Their inclusions, equations and universal properties specify
them independently of representatives. The node copy changes only `lean`.

I read the full node, all five statement-dependency nodes and their recorded
signatures/docstrings, the full Borel-pair and root-subgroup modules, and the
underlying group, Borel, semisimple, reductive, torus, character-weight and
unipotence definitions. I checked Milne directly in the local PDF: printed
pp.453--455 (PDF pp.465--467), pp.265--266 (PDF pp.277--278), and pp.545--546
(PDF pp.557--558). Notation 21.89 and Proposition 21.90 give exactly the kernel
torus, centralizer, restricted root datum and Borel intersection in the node;
Theorem 21.91 gives the radical and Levi product; 13.33(d) and 25.9(a) give the
open quotient charts. The theorem docstring includes all 15 proof steps of the
node, with their cited node IDs, rather than substituting a different route.

Hypotheses, matched individually:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  `Field` is the recorded Mathlib match of `def-weil-field`; `IsAlgClosed` is
  the algebraic-closedness part of the recorded match of
  `def-weil-algebraic-closure`. No chosen closure or extension is assumed.
- Group schemes are `Grp (Over (Spec (.of F)))`. This bundles exactly the
  recorded `CategoryTheory.GrpObj` structure on schemes over F, with its
  multiplication, identity and inverse diagrams. Every arrow between these
  bundled groups is a group-scheme homomorphism.
- Semisimplicity is `hG : IsSemisimpleGroupScheme G.X`, the existing predicate
  with smoothness, connectedness, affineness, finite type and the absence of
  nontrivial smooth connected solvable normal closed subgroups. Its solvability
  is `IsSolvableGroupScheme`, termination of the scheme-theoretic derived series.
- The chosen split maximal torus is `iT : T ⟶ G`, `hT` and `hsplit`.
  `hT` uses the recorded `ReductiveTorusCentralizer.IsMaximalTorus`; `hsplit`
  uses `MultiplicativeType.splitTorus F r`, allowing r = 0.
- The chosen Borel is `iB : B ⟶ G` with `hB : IsBorelGroupScheme iB.hom.hom`.
  `j : T ⟶ B` and `hj : j ≫ iB = iT` express T contained in that Borel.
- The actual character/cocharacter lattices are the additive Hom groups
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` and the
  reverse Hom group. The commutativity witnesses match exactly the witnesses
  in the Borel-pair dependency. They provide their pointwise abelian group laws.
- `aG`, `aB`, `haG`, `haB` specify the actual conjugation actions of T on G
  and B, rather than independent actions whose weights could be unrelated.
- `Φ`, `D : RootDatum Φ ...`, `b : D.Base`, `hred`, `hroot`, `hpair`, `hΦ`,
  `hpos` spell out the root datum and positive/simple roots supplied by the
  Borel-pair dependency: `D.root α = α.val`; the pairing is composition with
  the integer power map; roots are exactly the nonzero tangent characters;
  and `b.IsPos` is exactly occurrence in Lie(B). Here D names the root datum
  to leave P available for the parabolic. No abstract replacement lattice is used.
- `U`, `iU`, `hU` name the root subgroups: closed, smooth, connected,
  normalized by T, with tangent image precisely the corresponding character
  weight space. These are the characterizing properties of the unique root
  subgroups in `reductive_root_subgroup_parametrizations`. The same existing
  `TorusCharacterTangent.IsStable` and `weightSpace` are used. No arbitrary
  one-dimensional subgroup is substituted.
- `I : Set Φ` and `hI : I ⊆ (b.support : Set Φ)` express an arbitrary subset
  of the simple roots. There is no nonemptiness, rank, characteristic,
  simply-connectedness or proper-subset assumption.

Conclusions and introduced objects, matched clause by clause:

- Phi_I is written directly as the roots whose `D.root α` belongs to
  `Submodule.span ℤ (D.root '' I)`. This is precisely Phi intersect ZI.
- The existential `TI`, `s : TI ⟶ T` satisfy a closed torus inclusion,
  `∀ α ∈ I, s ≫ α.val.toMul = 1`, and factorization of every other closed
  torus inclusion annihilated by I through s. This is exactly the largest
  subtorus of the simultaneous kernels. It is not the possibly nonreduced
  entire simultaneous kernel, nor merely an unspecified maximal torus.
- The closed inclusion `iL : L ⟶ G` has point image equal to
  `ReductiveTorusCentralizer.centralizerPoints (s ≫ iT) A` for every
  commutative F-algebra A. That existing predicate in turn quantifies over
  every further A-algebra extension and every TI-point; it includes nilpotents.
- `ReductiveTorusCentralizer.IsReductive L`, `tL ≫ iL = iT` and
  `ReductiveTorusCentralizer.IsMaximalTorus tL` are reductivity of L and the
  given T as its maximal torus. The already bound `hsplit` applies to the
  identical T, hence also supplies splitness in L without another choice.
- `DL` is a root datum on the SAME character and cocharacter lattices, indexed
  by `{α : Φ // D.root α ∈ Submodule.span ℤ (D.root '' I)}`. Its pairing is
  `D.toLinearMap`, and `DL.root α = D.root α.val` and
  `DL.coroot α = D.coroot α.val` retain both the ambient roots and coroots.
  `aL` is pinned to conjugation by tL, and its nonzero character weights are
  exactly Phi_I. Thus DL is identified as the root datum of (L,T), not merely
  some unrelated abstract root datum with the same number of roots.
- `BI`, `bB : BI ⟶ B`, `bL : BI ⟶ L` and
  `IsPullback bB.hom.hom bL.hom.hom iB.hom.hom iL.hom.hom` specify the
  scheme-theoretic intersection B intersect L. `IsBorelGroupScheme bL.hom.hom`
  is exactly its Borel property in L. `tBI` and its two triangle equations
  retain the original T in this intersection.
- `aBI` is conjugation by tBI; its root weight for α is nonzero exactly when
  `D.root α ∈ Submodule.span ℤ (D.root '' I) ∧ b.IsPos α`. These are precisely
  Phi_I intersect Phi_0^+. The closed inclusions into L and G preclude any
  other nonzero weights beyond the ambient roots.
- `P`, `iP`, `bP` are a closed subgroup of G containing B. The condition
  `∃ β ∈ I, α.val = -β.val` selects exactly the negative simple root groups
  used in the generating set. Each factors through P, and every closed
  subgroup K containing B and those groups receives a factorization of iP.
  This is the least closed subgroup generated in the node, retaining its
  scheme structure. `Smooth P.X.hom ∧ ConnectedSpace P.X.left` is the
  asserted smoothness and connectedness. Closedness in finite-type G also
  gives finite type without an additional hypothesis.
- `lP : L ⟶ P` and `lP ≫ iP = iL` retain this very centralizer as the Levi
  subgroup in the parabolic.
- `R`, `rP : R ⟶ P` are closed, normal, smooth, connected and unipotent.
  Every smooth connected normal unipotent closed subgroup N of P factors
  through rP, giving exactly the largest subgroup defining the radical.
  The reused `SolvableGroupStructure.IsUnipotent` tests geometric points
  in a faithful closed matrix representation by a positive power of u - 1.
- Each root group with `b.IsPos α` and root outside `Submodule.span ℤ ...`
  factors through R. The next universal property says R factors into every
  closed subgroup of G containing these groups, so R is GENERATED by exactly
  the specified positive roots outside Phi_I. No assertion merely on rational
  points replaces generation of closed subgroup schemes.
- `rB ≫ bP = rP` places R in B compatibly with its inclusion into P.
  The two `IsIso` clauses are the actual multiplication morphisms R × L → P
  and R × BI → B, in the displayed order. Both domains are the product
  schemes over F. Since rP is normal, the group law transported by these
  multiplication maps is precisely the conjugation semidirect product law;
  a direct-product group law is not imposed.
- `Q : Over (Spec (.of F))`, `q : G.X ⟶ Q`, `IsProper Q.hom`,
  `LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom` give a proper finite-type
  F-scheme. `Flat q.left ∧ Surjective q.left` is faithful flatness.
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` of q are
  finite presentation, as in the recorded homogeneous-quotient interface.
- The right-invariance equation uses `g * p`, and the `IsPullback` clause
  identifies G × P with G ×_Q G by exactly `(g,p) ↦ (g,gp)`.
- `Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q)`
  and the existential arrow ηq from the coequalizer of the two right-action
  arrows, agreeing with `yoneda.map q` on generators and inducing a bijection
  on maps to every sheaf, give the full sheafification universal property
  for the right-coset presheaf. The site is the very fppf topology used in
  `exists_homogeneous_fppf_quotient`, with flat finitely presented jointly
  surjective coverings; no etale or fpqc quotient is substituted.
- `m : ℕ`, `V : Fin m → Over ...`, `v`, `σ` give finitely many regular
  sections over open immersions into Q. `σ k ≫ q = v k` is the section
  equation and `∀ x : Q.left, ∃ k, x ∈ Set.range (v k).left` is covering.
  Every open subscheme can serve as V k; no affine or principal-open
  restriction is imposed.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the relevant part
  of the recorded algebraic-closure Mathlib match).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`,
  `CategoryTheory.Grp`, with the over-scheme specialization documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. The statement uses
  the exact actual-Hom root datum, conjugation action and Borel-pair interface
  of that theorem and its existing terminology imports.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`.
  Its closed/smooth/connected/stable/tangent characterization specifies the
  given U_alpha; its parameter point and coordinate helper definitions are
  unnecessary here because no parametrization is part of this node's statement.
- Existing predicates and constructions from their transitive imports:
  `IsSemisimpleGroupScheme`, `IsBorelGroupScheme`,
  `ReductiveTorusCentralizer.IsMaximalTorus`, `.IsReductive`, `.centralizerPoints`,
  `MultiplicativeType.IsTorus`, `.splitTorus`, `SolvableGroupStructure.IsUnipotent`,
  `TorusCharacterTangent.weightSpace`, `.IsStable`, and `GrpObj.differential`.
  None is copied or replaced by a private definition.

All currently recorded proof-dependency modules are imported non-publicly when
not already public statement imports. The proof-only imports include character
antiduality, largest subtorus, rank-one reflections, Borel intersection,
homogeneous quotient geometry, homogeneous quotient, transverse subgroup product,
properness, finite type and the CompactSpace defining module. Proof dependencies
without a recorded Lean module have no module to import yet; they remain named
in the proof docstring and their original DAG edges remain unchanged.

Edge cases checked before writing and reread after compilation:

- I empty: the kernel condition is empty, TI = T, L = T, BI = T, P = B;
  the radical roots are all positive roots. The restricted root datum has an
  empty index but retains the full torus character/cocharacter lattices.
- I = Delta_0: TI is the trivial torus (the roots span rationally), L = G,
  P = G, BI = B, R = 1 and Q = Spec F. The radical-generation universal
  property includes its empty generating family, and one open section suffices.
- Rank zero/trivial G: Φ and I are empty, and both product isomorphisms reduce
  to multiplication by the trivial group. No nonempty root/base binder occurs.
- Positive characteristic, including PGL_2 in characteristic 2: the simultaneous
  kernel can be nonreduced; TI is explicitly its largest TORUS. The centralizer
  is tested after every algebra extension; weights are characters, not their
  derivatives. No simply-connectedness, characteristic-zero or separability
  hypothesis is introduced.
- All schemes and affine test algebras are in the common field/scheme universe
  u; no independent smaller testing universe can make a universal condition
  vacuous. The finite cover permits arbitrary open subschemes, and its covering
  condition rules out an empty cover of the nonempty group quotient.

Searches (via the prescribed msearch.py wrapper, plus local source reads):

- LeanSearch: `standard parabolic group scheme Levi decomposition Zariski locally
  trivial torsor` returned eight hits on AddTorsor and parabolic matrices;
  none states the group-scheme theorem.
- LeanFinder: `standard parabolic subgroup Levi decomposition reductive group
  scheme quotient Zariski local sections` returned eight hits on Geck root
  constructions, GL_2 parabolic matrices and Iwasawa structures; no match.
- Loogle: `RootPairing.Base, IsClosedSubgroupScheme, IsProper` returned no hits;
  it reports unknown identifier IsClosedSubgroupScheme, which is project-local.
- Mathlib grep: `Parabolic|IsParabolic|Levi` returned modular-form matrix and
  Hopkins-Levitzki name hits, not algebraic-group parabolic subgroups or Levi
  decompositions.
- `rg -n 'standard.parabolic|StandardParabolic|ParabolicLevi'` in both
  `lean/WeilConjectures` and `lean/Sheaf`, and in `dag/lean_names_upstream.json`,
  returned no match. `grep -rn 'lem-sfb-standard-parabolic-levi-charts'
  lean/WeilConjectures` returned no match. Broader `parabolic|Parabolic|Levi`
  searches in the algebraic-geometry source trees returned only unrelated
  Hopkins-Levitzki imports. Existing centralizer, torus, radical, root-weight,
  Borel and homogeneous-quotient interfaces were located and reused.

The prescribed server scompile.py compiled the complete theorem in both its
sandbox name and library module name with no errors or warnings. The initial
parser error was one extra closing parenthesis in the finite-cover binder;
that was corrected before the clean compilation. Nothing was proved.

## Second reading by Q46

I reread the original node and the final Lean file side by side, following the
hypotheses and conclusions listed above. This is the dispatcher's single-worker
second pass; no other agent was started, and the maintainer supplies the
independent review of the delivery. The subgroup-minimality quantifiers range
over closed subgroup SCHEMES, the kernel torus is the largest subtorus rather
than the whole kernel, and the centralizer uses the recorded all-extension
condition. The restricted datum keeps the same lattices, pairing and actual
coroots. The radical is characterized both by maximal normal unipotence and by
its exact closed root generators. Both multiplication maps use R on the left.
The torsor has finite presentation and its specified right action; the quotient
also has the coset-sheaf universal property. The finite open charts have genuine
scheme morphism sections and cover every point of Q.

I found no missing clause or mathematical change. The only code change after
successful compilation was adding the non-public `Mathlib.Topology.Defs.Filter`
proof-dependency import, to include the module recorded for the quasi-compactness
leaf. The required dry run recompiles the final file. There is no disputed
statement, unit-statement fault, dependency repair or new node.
