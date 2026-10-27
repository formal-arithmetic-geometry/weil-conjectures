## Worker report

The delivery states `AlgebraicGeometry.exists_unipotent_cckpKernel_wound_criterion`
in `Sheaf.AlgebraicGeometry.UnipotentCckpKernelWoundCriterion`. Its sole theorem
has proof `sorry`. The supporting definition module contains three real Prop-valued
definitions and no postponed data. The item’s mathematical statement, proof and proof dependencies are unchanged.
The statement text gains explicit terminology citations requested in the return.

Source read: Brian Conrad, *The structure of solvable groups over general fields*
(2014), https://math.stanford.edu/~conrad/papers/appbnew.pdf, Definition 2.1 on
printed p.10, Definition 3.1 and the separable-extension paragraph on printed p.15,
and Proposition 3.2 (1) and (3), printed pp.15–16. The source explicitly uses all
scheme morphisms from the affine line. It states the same largest central p-torsion
subgroup, separable-extension compatibility and wound equivalence. No source or
mathematical statement correction is needed. The citation-only text update is recorded
under `statement_change` as required by the delivery field contract.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. Positive prime characteristic is
  `(p : ℕ) [Fact p.Prime] [CharP k p]`; primality includes `p > 0`.
- The group scheme is `U : Grp (Over (Spec (.of k)))`. The recorded
  `SolvableGroupStructure.IsAlgebraic U` means exactly affine underlying scheme,
  locally finite type and quasi-compact structure map, hence affine finite type.
- Smoothness is `[Smooth U.X.hom]`; connectedness is `[ConnectedSpace U.X.left]`.
  The latter includes nonemptiness, as in the dependency node.
- Faithful finite-dimensional geometric matrix unipotence is
  `SolvableGroupStructure.IsUnipotent U`: its definition uses a closed subgroup
  representation into GL on `ULift (Fin n)` and nilpotence of matrix minus identity
  on every algebraically closed extension. Its smoothness conjunct repeats an
  existing hypothesis but imposes no extra restriction.
- The existential `(F : Grp ...) (i : F ⟶ U)` supplies the actual subgroup and its
  group homomorphism. `IsCckpKernel p i` includes `IsCentralPTorsionSubgroup p i`.
  The latter includes `IsAlgebraic F`, `IsClosedSubgroupScheme i.hom.hom`,
  `Smooth F.X.hom`, and `ConnectedSpace F.X.left`.
- Centrality is membership of every `x ≫ i.hom.hom` in the existing
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 U) A`. That predicate quantifies
  over every further A-algebra and every U-point, so the assertion is universal
  scheme-theoretic centrality, including on nonreduced test algebras.
- The p-torsion condition is `∀ (A : Type u) [CommRing A] [Algebra k A]
  (x : StandardGroupSchemes.affine k A ⟶ F.X), x ^ p = 1`.
  The Hom-group multiplication is the recorded group-object operation. Thus the
  multiplicative power is the p-fold sum in the source's additive terminology.
- Largestness is the second conjunct of `IsCckpKernel`: every `j : B ⟶ U`
  satisfying the same subgroup condition factors by a group homomorphism
  `f : B ⟶ F` with `f ≫ i = j`. Requiring affine finite type of B loses no
  subgroup: a closed subgroup of the affine finite-type U has these properties.
- `IsCommMonObj F.X` is the explicit commutativity conclusion.
- For every other cckp inclusion `i' : F' ⟶ U`, the conclusion supplies
  `e : F ≅ F'` with `e.hom ≫ i' = i`. This is equality of the closed subgroups
  they represent, expressed independently of presentations of their source schemes;
  it is not an abstract isomorphism forgetting their inclusions.
- For every field extension `[Algebra k K] (hK : Algebra.IsSeparableExtension k K)`,
  `IsCckpKernel p ((MultiplicativeType.baseChange (K := K)).map i)` asserts that
  the actual pullback inclusion is the largest subgroup after scalar extension.
  It uses no chosen replacement inclusion and does not restrict to finite extensions.
- `IsWound U ↔ IsWound F` is the last conjunct. `IsWound` includes the smooth,
  connected, affine algebraic and unipotent conditions, and then quantifies over
  `f : StandardGroupSchemes.additive k ⟶ G.X` in `Over (Spec k)`, not `Grp`.
  The equality `f = StandardGroupSchemes.map k (Algebra.ofId k (Polynomial k)) ≫ x`
  says that f factors through its rational value `x : Spec k ⟶ G`.
  Here `StandardGroupSchemes.additive k` is the recorded `Spec k[X]`.
- No perfectness, nontriviality, positive dimension or positive matrix-size
  hypothesis is added. All fields, groups, test algebras and extension fields use
  the existing library's common ambient universe `u`; no independent smaller
  universe is used for a quantified test category.

Dependency declarations used (full signatures and their docstrings read in source):

- `Field`, `Mathlib.Algebra.Field.Defs`.
- `Algebra.IsSeparableExtension`, `WeilConjectures.FieldTheory.SeparableExtension`: 
  every finitely generated intermediate field is separably generated (Stacks 030O),
  with no algebraicity assumption on K/k.
- `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj`, and the Hom-group operations,
  `Mathlib.CategoryTheory.Monoidal.Grp` and its imported monoid-object interface.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.LocallyOfFiniteType`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
  `QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`;
  `Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
  `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- `AlgebraicGeometry.Spec` and `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`;
  `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`.
- `StandardGroupSchemes.affine`, `.map`, `.additive`,
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `SolvableGroupStructure.IsAlgebraic`, `.IsUnipotent`,
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.
- `MultiplicativeType.baseChange`, `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
- `ReductiveTorusCentralizer.centralizerPoints`,
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`.

The item additionally cites the landed structure, base-change and general separability
terminology nodes for these interfaces.
No dependency interface was replaced. Public imports expose statement dependencies.
The plain proof imports cover every currently recorded proof dependency with a
module: the centre theorem, kernel interface, geometrically reduced group smoothness,
smooth geometric reducedness, connectedness with rational section, and density of
rational points. The other proof nodes have no recorded Lean declarations yet:
separable-point scheme core, finite-type identity subgroup, unitriangular embedding,
unitriangular filtration and vector/wound factor. They are recorded in the six-step
proof docstring; this delivery needs none of their absent interfaces to type its statement.

Edge cases checked against the definitions:

- For the trivial group every affine-line morphism is the unique constant one,
  its sections are p-torsion and central, and all subgroup inclusions into it factor
  through it. Thus the statement permits exactly U = F = 1, without excluding it.
- Ga has its nonconstant identity curve, so its wound predicate is false; in
  characteristic p its p-torsion central kernel is Ga itself. This checks both
  sides of the equivalence without confusing scheme maps and homomorphisms.
- A nontrivial smooth connected wound form over an imperfect field is admitted;
  neither IsWound nor the theorem assumes algebraic closedness or perfection.
- Alpha_p is not a smooth candidate; a disconnected étale p-torsion subgroup is
  not a connected candidate. The definition does not accidentally maximize over
  infinitesimal or disconnected p-torsion.
- The zero test algebra is not excluded, and all nonreduced test algebras occur in
  both centrality and torsion. The identity field extension and separable
  transcendental extensions are covered by the repaired `IsSeparableExtension`
  hypothesis. The original delivery’s `Algebra.IsSeparable` did not cover the
  transcendental case; the earlier report claim was incorrect.
- The affine line is the entire scheme Spec k[X]; constancy is equality of scheme
  morphisms, not constancy of the map on topological spaces or of rational points.

Searches actually run with `msearch.py` (exact queries and answer digests are in
the new node's `mathlib_searches` and the tool-generated `searches.jsonl`):

- LeanFinder: `The largest smooth connected central subgroup killed by p of a
  unipotent group is wound if and only if the group is wound`. Eight hits, on
  abstract nilpotence and central series; no matching algebraic-group theorem.
- Loogle: `IsUnipotent, GroupScheme, IsWound`. Zero hits, with unknown identifier
  `IsUnipotent`; no usable declaration.
- LeanSearch: `wound unipotent group canonical central p torsion kernel`.
  Eight hits, including Sylow, abstract-group central kernels and IsPGroup;
  none defines woundness or the cckp-kernel of a group scheme.
- Mathlib grep: `cckp|IsWound|[Uu]nipotent`. Eight irrelevant hits concerning PSL
  stabilizers or preadditive matrices. More focused `cckp|IsWound|[Ww]ound` has
  one irrelevant prose hit in `Algebra/Group/ForwardDiff.lean`.
- Project `rg` on `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found the existing unipotence interfaces, but no
  IsWound, IsCckpKernel or IsCentralPTorsionSubgroup. Searching the item id in
  `lean/WeilConjectures` found no existing theorem.
- DAG `rg` for wound/cckp found statement nodes that introduce those notions
  inline, but no definition node carrying them. `tools/blueprint_refs.py search`
  returned zero matches for each of `wound` and `cckp`; a search in the current
  `literature/blueprint/latest/` also found none. The ancestor command returned
  `None`; the new node preserves this recorded ancestry and prepends the item
  to its via chain, rather than inventing a blueprint ancestor.

Validation: both files compile separately in dependency order through the prescribed
`scompile.py`. An initial missing scoped Hom-group instance was fixed by opening
`MonObj` in the definition module. The wrapper's local attempt reported no disk
space, then its automatic server confirmation compiled both final modules cleanly
(2.1 s and 2.0 s, respectively), with no non-sorry warning. No local library build
or repository mutation was performed.

## New nodes

`def-sfb-wound-cckp-kernel` supplies the missing woundness and cckp-kernel terminology
from Conrad's Definitions 2.1 and 3.1, together with the smooth connected central
p-torsion candidate predicate used to spell out largestness. Its three definitions
use existing group schemes, algebraic groups, geometric unipotence, standard affine
schemes and the universal centralizer. The node has no theorem or proof steps.
It defines conditions, not a chosen subgroup, so it has no existence oracle or
postponed construction. Its statement is self-contained, and it cites every
underlying terminology node. The searches above show no duplicate. The original
item cites it in stmt_deps and cites the already-landed structure, base-change and general separability
terminology dependencies. Its citation-only statement change is recorded below.

The first delivery dry run caught a metadata extraction error at the named argument
`(K := K)`. The recorded theorem signature now includes the entire declaration
through its final wound-equivalence conjunct. Two grouped citations in the new
node were also made explicit to match the DAG citation checker.

## Returned delivery repair

Returned head: `006646d5f4fd`. Compared the retained sandbox with the current
read-only main node: only the prior Lean record and added statement dependencies
differed; the new definition node is still absent on main and remains in this packet.
The delivery wrapper rebases the repaired packet on the current published main.

1. H3, general separability: replaced `[Algebra.IsSeparable k K]` with the explicit
   binder `(hK : Algebra.IsSeparableExtension k K)` and publicly imported
   `WeilConjectures.FieldTheory.SeparableExtension`. Read the defining module’s
   complete definitions and docstrings: `IsSeparableExtension` quantifies over
   finitely generated intermediate fields and does not assert K/k algebraic.
   Added `def-weil-pbc-separable-field-extension` to stmt_deps and cited it in
   the statement text. Updated lean.statement verbatim from the full signature.
   The old report incorrectly claimed the algebraic predicate included
   transcendental separable extensions; that claim is corrected above.
2. H2/H4 citation metadata: the statement now cites
   `def-sfb-wound-cckp-kernel`, `def-sfb-solvable-group-structure` and
   `def-sfb-tori-multiplicative-type` explicitly. No notion is redefined; the
   previously approved supporting definition node and module are retained.
   The citation-only statement update has the required statement_change record
   and full citer audit. The proof and proof_deps remain unchanged.

## Statement corrected

The original natural-language statement is preserved verbatim in
`statement_change.old_statement`. It already meant every separable extension.
The revised text adds four explicit definition citations, retaining that meaning.
The actual defect was its Lean rendering: Mathlib’s `Algebra.IsSeparable` implies
algebraicity, so it omitted separable transcendental K/k. The repaired rendering
uses `Algebra.IsSeparableExtension` (Stacks 030O) as requested. The source remains
Conrad’s Definitions 2.1 and 3.1 and Proposition 3.2, especially the paragraph
following Definition 3.1 about every separable extension.

Full citer audit: `lem-sfb-split-unipotent-central-vector-subgroup` — holds true.
Read its full statement and proof: positive-characteristic step 3 uses the wound
equivalence; step 5 uses the cckp-kernel after separable closure and its largestness
to deduce automorphism invariance. Both uses are preserved. This is the only node
whose stmt_deps or proof_deps name the item; no citer is edited.

Repair validation: `scompile.py` compiled both final modules with exit 0 and no
warning or error. The output reports the definition module at 1.6 s, a queued
sandbox pass at 406.2 s, and the final theorem library pass at 4.4 s. The
per-file limits were left at their defaults.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
