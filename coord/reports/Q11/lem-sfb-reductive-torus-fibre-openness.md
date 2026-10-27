## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.ReductiveTorusFibreOpenness states
AlgebraicGeometry.reductive_torus_fibre_openness, with its sole postponed theorem
proof `sorry`. Its docstring gives all ten DAG proof steps and their dependencies.
The two real helper definitions bundle the existing open neutral component and
its canonical inclusion for the actual pullback fibre. They introduce no new
choice, subgroup, axiom, representation, or existence assumption. Local instances
inside these definitions only expose existing pullback instances.

Hypothesis and clause correspondence:

- The arbitrary scheme S is `{S : Scheme.{u}}`. The group with its actual diagrams
  is `G : Grp (Over S)`, using CategoryTheory.GrpObj through its bundled `grp`.
- Smooth is `[Smooth G.X.hom]`; affine over S is `[IsAffineHom G.X.hom]`, rather
  than absolute affineness of G. Finite presentation is
  `[LocallyOfFinitePresentation G.X.hom]` together with quasi-compactness and
  quasi-separatedness supplied by the affine morphism. This includes nonaffine S.
- The point and its geometric lift are `s : Spec (.of k) ⟶ S`, with `k : Type u`,
  `[Field k] [IsAlgClosed k]`. Its underlying point is `s (IsLocalRing.closedPoint k)`.
  Every point of a Scheme.{u} has such a lift using the algebraic closure of its
  residue field in Type u. Conversely a geometric lift induces a field extension
  of that residue field. Reductivity and maximality of tori are geometric
  properties, so allowing an arbitrary algebraically closed lift represents the
  same pointwise hypothesis and conclusions as choosing the residue-field closure.
- `groupFibreNeutralComponent G s` is literally the recorded
  `GrpObj.identityComponent` of `((Over.pullback s).mapGrp.obj G).X`, bundled by
  `Grp.mk`; its scheme structure is the canonical open subscheme, not a reduction
  or a supplied representative. `hred` says it is reductive using the existing
  `ReductiveTorusCentralizer.IsReductive`. Over an algebraically closed field this
  is smooth, affine finite type, connected and without a nontrivial smooth
  connected normal unipotent closed subgroup. The recorded unipotence notion
  uses a faithful matrix closed immersion and geometric matrix unipotence.
- The first conjunct provides `U : S.Opens`, membership of the underlying point,
  and reductivity of the neutral fibre for every algebraically closed field K and
  every geometric point t with underlying point in U. These are precisely the
  geometric points over the open subscheme U (unique open-immersion factorization).
- In the second conjunct `r : ℕ` includes zero, and
  `j : relativeSplitTorus S r ⟶ G` is the given subgroup homomorphism with the
  explicit premise `IsClosedImmersion j.hom.hom.left`. `relativeSplitTorus` is the
  previously landed Hopf-spectrum construction over arbitrary S, with its actual
  group law; in rank zero it is the trivial group.
- Maximality of the specified fibre in its neutral component is the existence of
  `i` with `i ≫ groupFibreNeutralComponentι G s = (Over.pullback s).mapGrp.map j`
  and `ReductiveTorusCentralizer.IsMaximalTorus i`. This is exactly factorization
  of the original fibre inclusion into the open identity component, with maximal
  torus property there. It does not replace j by an unrelated maximal torus.
- The conclusion gives `V : S.Opens`, membership of the original point and the
  same factorization/maximality for every geometric point over V. The two opens
  are independent, as in the node. The second assertion retains the original
  reductivity hypothesis at s; no reductivity at other fibres is assumed.

Recorded dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, Grp and Grp.ofHom.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion.
- Mathlib.Topology.Connected.Basic: ConnectedSpace, via the existing reductivity
  predicate and identity-component construction.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive and IsMaximalTorus.
- Sheaf.AlgebraicGeometry.RelativeSplitTorus: AlgebraicGeometry.relativeSplitTorus.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Basic:
  AlgebraicGeometry.GrpObj.identityComponent and identityComponentι.

The last three already-landed definition nodes were added to stmt_deps. No new
node, dependency repair, or statement correction is needed. Source consulted:
Brian Conrad, Reductive Group Schemes (2014), Proposition 3.1.9(1),(2), printed
pp.85--88, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . The node
selects reductivity and the split-torus maximality instance; it does not request
the source's additional semisimplicity or centralizer equality conclusions.

Proof-only imports are the recorded modules for smooth section component
openness, reductive torus self-centralizer, reductive Borel-pair structure,
relative torus bundle weights, reductive rank-one reflections, tangent dimension
smoothness, perfect solvable unipotent-torus structure and the corank-one
centralizer reductivity test, plus Mathlib's universally-open instance and the
upstream smooth-flat-LFP statement. Other proof dependencies have no published
recorded Lean module in this checkout and are not fabricated or duplicated here.

Edge cases checked: arbitrary and nonreduced bases; no affine-base, Noetherian,
perfect-residue-field, characteristic-zero, or connected-total-group hypothesis;
nonidentity components of G allowed; r=0; a trivial neutral fibre; empty root set;
empty base (no s exists, so the pointwise statement is vacuous); geometric fields
in the scheme's universe, with no smaller independent universe that would make
field-valued testing vacuous. The theorem has no let-binders, hidden arbitrary
map, extra hypothesis or tautological conclusion. There is no STATEMENT-DISPUTED
flag or known node fault.

Searches before construction (2026-10-24):

- msearch.py leanfinder: "Reductivity of geometric identity components and
  maximality of a split torus are open conditions for smooth affine group
  schemes". Eight hits, including Algebra.isOpen_smoothLocus and affine/open
  scheme infrastructure; none states this theorem.
- msearch.py leansearch: "Reductivity and maximality of a split torus persist near
  a fibre of a smooth affine group scheme". Eight hits on affine fibres,
  smoothness, etale base change and other infrastructure; none matches.
- msearch.py loogle: "AlgebraicGeometry.IsReductive, IsMaximalTorus, IsOpen".
  Zero hits; unknown identifier AlgebraicGeometry.IsReductive (the project's
  predicate is in ReductiveTorusCentralizer).
- msearch.py grep: "reductive|[Mm]aximal[Tt]orus|[Rr]eductive[Ll]ocus" in
  AlgebraicGeometry. Zero Mathlib hits.
- rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  reductive openness, maximal-torus openness and torus_fibre_openness, and the
  requested item-id search in lean/WeilConjectures: no matching theorem. Broader
  IsReductive/IsMaximalTorus/identityComponent/splitTorus searches found the
  existing definitions reused above. Read the relative-split-torus, reductivity
  terminology and algebraic-component DAG records and full source declarations.
- Checked the proposed helper names in both project Lean roots: no existing
  groupFibreNeutralComponent or groupFibreNeutralComponentι declaration.

Validation: each compile uses the prescribed scompile.py wrapper against the live
published library, with module mode and no global build. Final compile and
preflight results are recorded by the delivery wrapper.

## Second reading by Q11

Independent clause-by-clause reading by the maintainer's stage-2 reviewer (written in the
review FIX, replacing the worker's self-check under the direct-delivery policy).

Node clauses and their Lean rendering:

1. S an arbitrary scheme: `{S : Scheme.{u}}`. Correct; no affine, Noetherian or nonempty assumption.
2. G -> S an S-group scheme with the group diagrams: `G : Grp (Over S)` (Mathlib GrpObj). Correct.
3. Smooth, affine, finite presentation: `[Smooth G.X.hom] [IsAffineHom G.X.hom]
   [LocallyOfFinitePresentation G.X.hom]`. Relative affineness plus LFP gives finite presentation
   (qc + qs come from the affine morphism). Not stronger than the node.
4. Geometric neutral fibre G^0_sbar with its open-subscheme structure: `groupFibreNeutralComponent G s`
   is `Grp.mk (GrpObj.identityComponent ((Over.pullback s).mapGrp.obj G).X)`, the recorded owner of
   def-wf-algebraic-components (connected component of the identity point as an open subscheme, with the
   restricted group law and the IsMonHom inclusion `identityComponentι`). The two helpers have real data,
   only expose existing pullback LocallyOfFiniteType/QuasiCompact instances, and duplicate nothing in
   Sheaf/ or WeilConjectures/ (searched: identityComponent, neutralComponent, fibre identity component).
5. The point s with an algebraic closure of kappa(s): a geometric point `s : Spec k ⟶ S`, k : Type u
   algebraically closed, with underlying point `s (closedPoint k)`. Equivalent to the node: taking
   k = AlgebraicClosure kappa(x) (in Type u) gives the node; conversely reductivity of G^0 is invariant
   under extension of algebraically closed fields. The conclusions quantify over the same kind of points.
6. Reductive (smooth, connected, affine finite type, no nontrivial smooth connected normal unipotent
   closed subgroup, unipotence via faithful matrix representation): the recorded
   `ReductiveTorusCentralizer.IsReductive` (IsAlgebraic, Smooth, connected after kbar, every
   algebraic closed normal connected unipotent U over kbar is ≅ trivial). Matches the node; over an
   algebraically closed field the extra base change is harmless.
7. First conclusion: `∃ U : S.Opens`, s's point ∈ U, and IsReductive of the neutral fibre at every
   geometric point t whose point lies in U (= geometric points of U, as Spec K is one point). Correct.
8. r ≥ 0 and the closed subgroup immersion j : G_{m,S}^r -> G: `r : ℕ`, `j : relativeSplitTorus S r ⟶ G`
   (Grp morphism, i.e. homomorphism), `IsClosedImmersion j.hom.hom.left`. relativeSplitTorus is the
   recorded owner of def-sfb-relative-split-torus (rank 0 = trivial group). Correct.
9. j_sbar a maximal torus of G^0_sbar: `∃ i` into the neutral fibre with `i ≫ ι = (Over.pullback s).mapGrp.map j`
   and `IsMaximalTorus i`. Since ι is a mono, i is unique, so this is exactly "the fibre of j lies in
   G^0 and is maximal there" (a torus is connected, so the factorization is no extra condition).
   IsMaximalTorus matches the node's "maximal among closed tori".
10. Second conclusion: `∃ V`, s's point ∈ V, same factorization and maximality at every geometric point
   over V; V independent of U; hred retained as in the node ("Suppose ... Moreover"). Correct.

Edge cases: r = 0 (trivial torus, maximal iff G^0 has no nontrivial torus); empty S (no s, vacuous);
nonreduced or nonaffine S; disconnected G; trivial neutral fibre; all characteristics. Universes:
one universe u for S, k, K; the node's points (algebraic closures of residue fields) live in Type u.
No let-binders, no arbitrary choice, no extra instance, no tautological clause; the only proof is `sorry`.

Records: delivery diff vs live item = `lean` record + three already-landed definition stmt_deps
(def-sfb-reductive-torus-centralizer-terminology, def-sfb-relative-split-torus,
def-wf-algebraic-components), each actually used in the statement. Statement text unchanged.
lean.statement verbatim equal to the file signature. All imports exist in the live tree.

Mismatch found and corrected: proof steps 3 and 10 of the theorem docstring called the torus-lift base
change "etale"; lem-sfb-geometric-torus-fppf-lift (and the node, steps 3 and 10) give a flat, finitely
presented, quasi-finite base change p : S' -> S. Docstring corrected; recompiled clean.
