## Worker report

The delivery states Milne Corollary 21.50, printed p.440, as
`AlgebraicGeometry.semisimpleGroupScheme_perfect` in
`Sheaf.AlgebraicGeometry.GroupScheme.SemisimplePerfect`. Its proof is `sorry`;
its docstring contains all four steps of the accepted DAG proof. No other
postponed theorem, axiom, hollow data, or statement correction is introduced.
The reviewed stage-1 split is preserved. The inherited previous worker's
"already split" refusal referred to stage 1, whereas the live node has no Lean
record and this assignment is stage 2. The current queue lists stage 2.

Clause-by-clause correspondence:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- H is an F-group scheme: `(H : Over (Spec (.of F))) [GrpObj H]`.
- Semisimplicity is `hH : IsSemisimpleGroupScheme H`. Unfolding gives precisely
  `Smooth H.hom`, `ConnectedSpace H.left`, `IsAffine H.left`,
  `LocallyOfFiniteType H.hom`, and `QuasiCompact H.hom`, and the absence of
  nontrivial smooth connected solvable normal closed subgroup schemes.
- For each subgroup N, its inclusion i uses the existing
  `IsClosedSubgroupScheme i` and `IsNormalSubgroupScheme i`, and the additional
  tests are exactly `Smooth N.hom`, `ConnectedSpace N.left`, and
  `IsSolvableGroupScheme N`. Triviality is `Nonempty (IsTerminal N)` in the
  over-category, equivalently that its structure morphism is an isomorphism.
  A group object on the terminal F-scheme is necessarily the trivial group.
  No assumption about finite type of N is added; it follows from being a
  closed subgroup of the finite-type affine H.
- Solvability is termination of successive algebraic derived subgroups:
  `IsSolvableGroupScheme` asserts some `GroupSchemeDerivedLength G n`.
  Length zero is the trivial group; a successor existentially specifies a
  group object D and its derived subgroup inclusion i, and decreases n.
  These are proposition-valued definitions, with no selection of data from
  an unproved mere existence theorem.
- `groupSchemeCommutator G` is the actual scheme morphism
  `fst G G * snd G G * (fst G G)⁻¹ * (snd G G)⁻¹` on the categorical product.
  Existing `Hom.group` multiplication and inverse are induced by the
  group-scheme multiplication and inverse; therefore its value is xyx⁻¹y⁻¹.
- `IsDerivedGroupScheme i` requires that i is a closed subgroup inclusion,
  that the actual commutator morphism factors through i, and that i factors
  through every closed subgroup through which that commutator factors.
  This is the node's smallest-closed-subgroup definition at scheme level.
- The conclusion `IsDerivedGroupScheme (𝟙 H)` says that H itself, with its
  identity inclusion into H, is this smallest closed subgroup. This expresses
  H^der = H intrinsically, without requiring an arbitrary chosen representative
  of the derived subgroup or adding a hypothesis that it exists. In particular
  the conclusion supplies existence. For any other derived inclusion D → H,
  minimality of the identity produces an inverse section, and closed immersion
  gives monicity, so this is exactly equality of the subgroup schemes.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, a commutative division ring.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, whose docstring
  identifies splitting all polynomials with the node's root condition.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, with the
  multiplication, unit, inverse and group identities.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Grp:
  `CategoryTheory.Hom.group`, the group structure on morphisms into a group
  object. The existing `MonObj` scope enables it.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsClosedSubgroupScheme` and `IsNormalSubgroupScheme`; these already use
  the functor of points over every F-algebra, not just F-rational points.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, including nonemptiness.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.AffineScheme: `IsAffine`, the canonical
  X → Spec Γ(X) being an isomorphism; this renders the affine clause of
  def-pc-scheme. It is available through the existing group-scheme imports.
- Mathlib category-theory terminal-object API: `IsTerminal`, in the category
  `Over (Spec (.of F))`, for actual triviality of the underlying F-scheme.

Edge cases checked mathematically: the trivial group is included (derived
length zero, semisimple and perfect). The empty scheme cannot carry the
required group unit over the nonempty spectrum of F; connectedness explicitly
includes nonemptiness. G_a and G_m are smooth connected affine solvable groups
and therefore fail the semisimplicity test, as their own normal subgroup is
nontrivial. Finite nonreduced subgroup schemes such as mu_p are not discarded
by the derived predicate or replaced by their rational-point groups; the
semisimplicity test restricts to smooth connected normal subgroups exactly
as the node requires. There is no characteristic-zero assumption: the cubic
argument uses s(s²-1)=1, including characteristic two. Universes are explicitly
bound (`universe u` and `Type u`), and `autoImplicit false` is set in both files.
Subgroup schemes and all closed test subgroups have the same scheme universe;
all closed subgroups of H have representatives in that universe.

Searches actually made: msearch leanfinder on "semisimple affine algebraic
group scheme is equal to its derived subgroup" returned abstract-group and
Lie-algebra results, not this theorem. Loogle `"IsSemisimple", "commutator"`
returned zero hits; grep `semisimple|derivedSubgroup|commutatorMorphism` in
Mathlib/AlgebraicGeometry returned zero. LeanSearch on "semisimple algebraic
group scheme derived closed subgroup and solvable derived series" returned
abstract-group solvability and derivedSeries. Further leanfinder, loogle and
grep searches for the new notions are recorded verbatim as search-log records
in the new definition node. rg of the existing Sheaf and WeilConjectures
sources found semisimple representations and Lie algebras only, plus the
already reused group-scheme subgroup interfaces. Searching the item's exact
blueprint id in WeilConjectures found no existing statement. Blueprint search
for "semisimple group" and "semisimple group scheme" found no matching node;
"derived subgroup" found only an unrelated monodromy restriction statement.
DAG-wide definition-node search found representation and Lie-algebra notions,
not semisimple group schemes. No repair note for this item was found.

Source read: the local Milne PDF, Proposition 6.18 and Corollary 6.19,
Proposition 6.30, section 6.44, Proposition 21.49 and Corollary 21.50.
The source identifies the derived group with the subgroup generated by the
commutator morphism and solvability with termination of its derived series.
Its radical definition of semisimplicity is the absence of nontrivial smooth
connected solvable normal subgroups over the algebraically closed field.

Validation: both delivery files were compiled separately in dependency order
with the prescribed scompile.py Q102 lem-sfb-semisimple-group-perfect wrapper.
Both passed with no errors or unexpected warnings; file times 8–11.5 seconds.
No global build or direct shared-repository write was performed.

## New nodes

`def-sfb-semisimple-group-scheme` records the missing semisimple group-scheme
notion and its commutator/derived/solvability vocabulary. It lives in
`Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` and has five public definitions,
all with source and matching blueprint docstrings, and no theorem or sorry.
The main declaration is `AlgebraicGeometry.IsSemisimpleGroupScheme`; supporting
names are listed in lean.declarations. It uses the original item's seven
statement dependencies and def-pc-scheme for affineness. Its source is Milne
Propositions 6.18, 6.30 and 6.44, and its exact searches are in mathlib_searches.
Existing DAG lemma lem-sfb-smooth-connected-derived-subgroup supplies a later
existence/properties theorem, not these definitions, and still has no Lean
record; none of its conclusions is assumed here. No replacement theorem or
parallel statement of that lemma is created. The creation chain has no
machine-resolved blueprint ancestor: blueprint_refs.py ancestor returned none;
the inherited unit and descriptive blueprint.from.place are retained and the
new via prepends this item. The item's stmt_deps gains only the new definition.

## Second reading by Q102

A second pass by this same dispatched worker re-read the live node, both Lean
files, and the Milne passages. It checked every binder and clause listed above,
especially the scheme-level minimality quantifying all closed test subgroups,
the use of terminality rather than rational-point triviality, and the exact
smooth/connected/solvable/normal/closed test in the semisimple predicate. It also
checked that the identity inclusion conclusion provides existence rather than
assuming the missing derived subgroup theorem. No statement mismatch was found.
This is a worker self-check, not a claim of an independent worker review: the
brief expressly prohibits starting other agents and assigns the independent
review to the maintainer. Source page references were checked and corrected
in the new node. Both modules use explicit universes and real definitions;
only the item's theorem has sorry. No source statement or accepted proof split
was changed, no STATEMENT-DISPUTED issue remains, and no dependency record
repair was needed.
