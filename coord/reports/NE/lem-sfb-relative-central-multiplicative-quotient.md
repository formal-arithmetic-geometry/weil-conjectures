## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RelativeCentralMultiplicativeQuotient`
states `AlgebraicGeometry.RelativeReductive.relative_central_multiplicative_quotient`.
Its sole theorem proof is `sorry`; no theorem is proved. The additional definition module has
seven explicit Prop-valued definitions, with no postponed data or embedded sorry.

The original statement, proof and proof dependencies are unchanged. The item gains one statement
dependency, `def-sfb-relative-reductive-quotient-terminology`. No statement correction is needed.

Clause-by-clause rendering:

- Nonzero commutative Noetherian ring: `(A : Type u) [CommRing A] [Nontrivial A]
  [IsNoetherianRing A]`. The base throughout the theorem is `Spec (.of A)`.
- Group schemes and their actual group homomorphisms: `Grp (Over (Spec (.of A)))`,
  with `c : C ⟶ G`. These carry multiplication, identity, inverse and the group diagrams.
- Reductivity of G: `hG : RelativeReductive.IsReductive G`. Its definition requires
  `Smooth G.X.hom`, `IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom`,
  `QuasiCompact G.X.hom`, and the existing field `ReductiveTorusCentralizer.IsReductive`
  on every pullback along `s : Spec (.of K) ⟶ S` with `[Field K] [IsAlgClosed K]`.
  That field predicate includes connectedness over an algebraic closure and triviality of all
  smooth connected normal closed unipotent groups, using the existing faithful-matrix
  unipotence predicate. Over an algebraically closed K its algebraic closure gives the same
  geometric condition. Affineness here is relative, so the definition also works after a
  nonaffine base change. The original base is affine.
- C closed: `hc : IsClosedImmersion c.hom.hom.left`.
- C central: `hcentral : IsCentral c`, defined by commutation of all C- and G-points on
  every test S-scheme U. Since U ranges over all test schemes, this includes every extension
  of every test algebra, including nonreduced extensions.
- C of multiplicative type: `hC : IsMultiplicativeType C`. This is an fppf cover by affine
  charts `Spec (R i) ⟶ S`, with characters `N i : AddCommGrpCat`, `AddGroup.FG (N i)`,
  and group-scheme isomorphisms to `ringDiagonalizableGroup (R i) (N i)`. Refining splitting
  coverings by affine open covers gives precisely these charts; no global splitting is assumed.
- Represented reductive quotient: `∃ Q p, IsReductive Q ∧ IsFppfGroupQuotient c p`.
  The reused `IsFppfGroupQuotient` explicitly gives the cartesian identity/kernel square,
  fppf local surjectivity, sheafness of the representable, the torsor isomorphism with
  projections g and gc, and the sheafification universal property for the right-coset
  coequalizer presheaf. This is the quotient stated in the node, not just an arbitrary
  surjective homomorphism with a pointwise kernel.
- Faithfully flat and finitely presented p: `Flat p.hom.hom.left ∧
  Surjective p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
  QuasiCompact p.hom.hom.left`. These are the project's scheme conventions. Flat plus
  surjective means faithfully flat; finite presentation is lfp plus quasi-compact, as in the
  Mathlib module documentation. Relative affineness also implies separatedness here.
- Centre of Q equal to the quotient of the centre of G: existential group schemes ZG,ZQ,
  inclusions zG,zQ, and homomorphisms cZ,pZ with `cZ ≫ zG = c`,
  `pZ ≫ zQ = zG ≫ p`, `IsCentre zG`, `IsCentre zQ`, and
  `IsFppfGroupQuotient cZ pZ`. In `IsCentre`, the image on each U is exactly the points
  that commute with every G-point after every further `V ⟶ U`, not merely points central
  in the abstract group G(U). The inclusions are closed immersions.
- Maximal torus: `IsMaximalTorus i` uses a closed immersion, the reused
  `IsRelativeTorus T.X`, and the existing field maximal-torus predicate on every geometric
  pullback. Thus the condition is fibrewise geometric maximality, not just maximality among
  torus subgroups defined over S. Relative tori use fppf local finite products of units,
  allowing rank zero and ranks varying across covering members.
- Every maximal torus T of G contains C and its quotient is maximal in Q:
  the forward clause of `HasMaximalTorusCorrespondence c p` supplies U,j,q and a
  factorization `k : C ⟶ T` with `k ≫ i = c` and `IsFppfGroupQuotient k q`.
- Inverse of the correspondence is scheme-theoretic inverse image: each such square has
  `IsPullback i.hom.hom q.hom.hom p.hom.hom j.hom.hom`. Conversely, every maximal
  torus j in Q occurs in such a square with a maximal torus i in G. Cartesian uniqueness
  identifies T with p-inverse-image(U) as an actual subgroup; the quotient presentation
  identifies U with T/C. Consequently the two projections of this relation give inverse
  bijections on subgroup schemes, rather than a bijection of redundant presentations.
- Arbitrary base change for quotient, p and centre identification: the final
  `∀ (S' : Scheme.{u}) (f : S' ⟶ Spec (.of A))` asserts reductivity, represented quotient,
  flatness, surjectivity, finite presentation, centre representations and centre quotient
  for the pullbacks of the SAME Q,p,zG,zQ,cZ,pZ. In particular no unrelated centre
  identification can be chosen after base change. The restriction equations pull back by
  functoriality of `(Over.pullback f).mapGrp`.
- Arbitrary base change for the torus correspondence: the final theorem clause supplies
  the correspondence on each S'. Moreover `HasMaximalTorusCorrespondence` asserts that
  every specified maximal-torus quotient square pulls back to that same kind of square,
  with the actual pulled arrows. Cartesian uniqueness gives naturality of inverse image;
  the specified fppf quotient gives naturality of T/C. New maximal tori over S' are also
  covered by the surjectivity clauses on S'. There is no Noetherian, affine, reduced or
  nonempty hypothesis on S'.
- No hypothesis requires C smooth or imposes a residue-characteristic restriction.

Dependencies read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, `isNoetherianRing_iff`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`: `ringDiagonalizableGroup` and
  `ringDiagonalizableGroupMap`, using the real group-algebra Hopf construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (nonempty, not just preconnected).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeTorus`: `IsRelativeTorus` and its units-product functor.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `ReductiveTorusCentralizer.IsMaximalTorus`;
  these reuse `SolvableGroupStructure.IsUnipotent` and `IsAlgebraic` and the field torus
  and base-change definitions. Their field-only scope is why the new relative predicates
  are needed; they are reused on fibres, not repaired or copied.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`, recorded by `def-sfb-fppf-group-quotient-presentation`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the underlying convention
  is `Over.pullback` on schemes and morphisms; `.mapGrp` transports the group law.
- Proof-only imports: `Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer`
  (`reductive_torus_self_centralizer`), and `Mathlib.LinearAlgebra.FreeModule.PID`
  (`Submodule.basisOfPid`). All other non-Mathlib proof dependencies had no recorded
  declarations when read, and are not restated as assumptions.

Source read: [Conrad, Reductive group schemes](https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf),
Definitions 3.1.1 (p.81), 3.2.1 (p.91), Lemmas 3.3.1(2), 3.3.2 (pp.96--98),
Corollary 3.3.5 and proof (pp.100--101), and the fppf local convention at the beginning
of the text and Appendix B.1. The current blueprint unit is the six-functors stability
unit; the present statement is a supporting structural input, not that unit's own statement.

Edge cases checked mathematically: C=1 (identity quotient); C=G=G_m (trivial quotient);
central mu_p in characteristic p (C not smooth, still fppf multiplicative type and allowed);
rank-zero tori and trivial reductive groups; disconnected bases with varying torus ranks;
nonreduced A; base change to a non-Noetherian or empty scheme; identity base change and
new tori after base change. All remain covered. The universal test schemes include affine
ones of the same size universe as A; the field test universe is u, not an independent smaller
universe. No generic-fibre or reduced-point shortcut appears in the definitions.

Searches: msearch leanfinder on the whole quotient statement returned abstract-group centre
and nilpotent-quotient lemmas only; loogle `AlgebraicGeometry, Grp, Over` returned no match
(unknown identifier AlgebraicGeometry); grep `Reductive|MaximalTorus|MultiplicativeType|IsTorus`
in Mathlib AlgebraicGeometry returned zero hits. For the new definitions, msearch leansearch
and leanfinder on relative reductive schemes/geometric maximal tori/fppf diagonalizable groups
returned scheme, root-data and ring-property declarations only; grep
`Reductive|MaximalTorus|MultiplicativeType|centre|center` in Mathlib AlgebraicGeometry
returned zero hits. Exact outputs of the latter three searches are in the new node.
Project rg searches in `lean/WeilConjectures` and `lean/Sheaf` found the reusable field
predicates, relative torus and general fppf quotient presentation, but none of the missing
relative predicates. Search for the item id in WeilConjectures returned no occurrence.
DAG definition searches and `tools/blueprint_refs.py search 'relative reductive'` found
no duplicate; `ancestor` returned null, preserved in the new node's blueprint metadata.

Validation: both files compiled separately with scompile.py, including their overlay/import
relationship. A first compile found that the group structure on Hom sets requires the
existing `MonObj` scope; adding `open scoped MonObj` fixed this. No definition or theorem
was changed to avoid a mathematical case. Final compiler and delivery preflight results
are recorded below after running the prescribed dry run.

## New nodes

`def-sfb-relative-reductive-quotient-terminology` introduces only the missing relative
multiplicative-type, reductive, maximal-torus, centrality and centre predicates and the
maximal-torus quotient-square relation/correspondence. Its source is Conrad's definitions
and Corollary 3.3.5, as above. It reuses the existing field group predicates, relative torus,
diagonalizable groups and general fppf quotient, and does not duplicate any of those.
Search outputs and all the definition-node metadata are included. Every definition has
real logical data; no existence theorem supplies unspecified construction data. The node
is cited by the item. The original item statement is unchanged.

## Second reading by NE

A separate second pass by this worker reread the original node and both completed modules.
The dispatcher explicitly forbids starting other agents; this section records a self-check,
not an independent worker's review. Independent review is supplied by the maintainer after
delivery, as required by the brief.

The second pass checked every clause against the mapping above and inspected the full reused
quotient definition. In particular, it checked that the centre condition quantifies over further
test schemes, that geometric maximality is used (the weaker global-containment definition
is not substituted), that the torus relation has BOTH surjective projections and the
cartesian inverse-image square, that its quotient map has the specified C kernel, and
that the same centre arrows pull back. It also checked that arbitrary base changes may
introduce additional maximal tori and that the statement still covers them.

This pass removed an unnecessary quasi-separated conjunct from the finite-presentation
clauses (Mathlib uses lfp plus quasi-compact) and corrected the page citation for Definition
3.2.1 to p.91. The theorem's hypotheses, original node statement and proof plan remain
unchanged. No statement dispute or known node fault remains. Only the one named theorem
has a postponed proof, with all eleven DAG proof steps in its docstring.

Final validation: `deliver2.py NE lem-sfb-relative-central-multiplicative-quotient --no-push`
reported `OK (dry run): commit 49c4cc69c41 passes the preflight and compiles; nothing pushed`.
Both final modules compiled cleanly, including the private sibling overlay. Node signature
strings match their source verbatim; only `lean` and the authorized `stmt_deps` addition
change on the existing item. Both modules satisfy the 100-character line limit.
