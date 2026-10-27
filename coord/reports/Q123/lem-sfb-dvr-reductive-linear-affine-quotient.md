## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.DvrReductiveLinearAffineQuotient`
states `AlgebraicGeometry.exists_dvr_reductive_linear_affine_quotient`. Its only
proof is `sorry`; it introduces no definitions or axioms. The declaration docstring
contains all five steps of the accepted DAG proof, including the finite-free
regular subcomodule, coefficient calculation, algebraic-space quotient, affine
quotient criterion, and arbitrary-base-change sheaf argument.

The mathematical sources were opened and read: [Milne, Basic Theory of Affine
Group Schemes](https://www.jmilne.org/math/CourseNotes/AGS.pdf), VIII, Theorem 9.1
and Aside 9.4, printed pp.125--126 (especially its Dedekind-domain paragraph), and
[Alper, Adequate moduli spaces](https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf),
Corollary 9.7.7 and Proposition 9.7.8, printed p.528. No correction to the node's
statement or proof is needed.

Hypothesis and conclusion correspondence:

- A DVR: `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
  The Mathlib class is a local PID with nonzero maximal ideal, as the recorded
  dependency requires; in particular fields and the zero ring are not included.
- An A-group scheme: `H : Grp (Over (Spec (.of A)))`. `GrpObj` is the recorded
  general category-theoretic group object, specialized to the slice over Spec A.
  Its structure has the multiplication, unit, inverse and all their diagrams.
- Smooth, affine, finite type: `[Smooth H.X.hom] [IsAffineHom H.X.hom]`
  and `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`. These use exactly the
  morphism predicates recorded on the dependencies. The affine base identifies
  affine over Spec A with having an affine underlying scheme.
- Connected geometric fibres without a nontrivial smooth connected normal
  unipotent subgroup: `hred` quantifies over every algebraically closed field
  `Ω : Type u` and every ring map `A →+* Ω`, then applies the existing
  `ReductiveTorusCentralizer.IsReductive` to the pulled-back group. Its definition
  was read in full, as were `SolvableGroupStructure.IsAlgebraic` and
  `SolvableGroupStructure.IsUnipotent`. It says smooth affine finite type,
  geometric connectedness, and triviality of every connected closed normal
  unipotent subgroup. Its unipotence predicate includes smoothness and a faithful
  closed matrix representation whose geometric matrices satisfy `(M-1)^N = 0`
  for some positive N. Affineness, smoothness and finite type of the fibres are
  already consequences of the preceding hypotheses. Testing the algebraic
  closure of an already algebraically closed Ω is the same geometric condition.
  The existing landed node `def-sfb-reductive-torus-centralizer-terminology` is
  added to `stmt_deps` to record reuse, under the rule allowing added landed
  statement dependencies. No existing definition is repaired or copied.
- Positive dimension and embedding: `∃ (n : ℕ) (_ : 1 ≤ n) (i : H ⟶ Grp.mk
  (GeneralLinearGroup (ULift.{u} (Fin n)) A)), IsClosedImmersion i.hom.hom.left`.
  The bundled group morphism expresses compatibility with multiplication and unit,
  and hence inverse; closed immersion concerns the actual scheme map. ULift only
  raises the index type into the coordinate ring's universe and does not change
  the number of rows or columns. The reused upstream general linear group is
  Spec of the polynomial matrix coordinate ring localized at its determinant,
  canonically the displayed ring A[x_ab,d]/(d det(x_ab)-1), with matrix group law.
- Affine quotient and represented torsor: the witnesses are `Q : Over (Spec A)`,
  `P : RepresentedRightTorsor H Q`, `e : P.space ≅ GeneralLinearGroup ... A`,
  and `IsAffineHom Q.hom`. The quotient map on the literal GL scheme is
  `e.inv ≫ P.projection`. This is only transport along the displayed isomorphism,
  not a different choice of coset construction.
- The right H-action is specified rather than arbitrary: for every test R and
  points p,h, `lift p h ≫ P.action ≫ e.hom = (p ≫ e.hom) * (h ≫ i.hom.hom)`.
  Thus the action is exactly right multiplication through i. P itself includes
  both right-action laws, flatness, surjectivity, local finite presentation,
  quasi-compactness, quasi-separatedness and the cartesian torsor square.
- The fppf sheaf quotient is the sheafification of right cosets: for every
  `(T : Scheme.{u}) (f : T ⟶ Spec A)`, write F for `Over.pullback f` in this
  explanation (there is no let binder in the Lean signature). The presheaf
  `coequalizer (yoneda.map (F.map (fst P.space H.X)))
  (yoneda.map (F.map P.action))` is the pointwise orbit/coset presheaf.
  Pullback preserves products, so its domain is canonically the product of the
  pulled-back space and group. The conclusion says `yoneda.obj (F.obj Q)` is a
  sheaf for `Scheme.fppfTopology.over T` and gives an arrow eta from that coset
  presheaf. `coequalizer.π _ _ ≫ eta = yoneda.map (F.map P.projection)` fixes
  its value on coset generators. Bijectivity of postcomposition with eta for
  every fppf sheaf Z is exactly the recorded sheafification universal property.
  It avoids an added sheafification-existence or smallness hypothesis.
- Representation and quotient map commute with every base change: the above
  property uses exactly `F.obj Q` and `F.map P.projection`, not unrelated
  existential quotient data. The five morphism-property clauses and
  `IsPullback (F.map fst) (F.map P.action) (F.map P.projection)
  (F.map P.projection)` state the torsor property of these very maps. After the
  canonical product comparison this is the right H_T torsor square. The
  pullback of e identifies its source with GL_n,A ×_A T, and the pulled-back
  action equation identifies its action with the base change of i.
- No splitness, completeness, perfection, characteristic, or residue-field
  assumption occurs. Scheme base changes and sheaves are in the fixed universe
  of the site, as in the recorded fppf-site dependency.

Dependency declarations read and reused:

| Node | Module and declaration |
| --- | --- |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic: IsDiscreteValuationRing |
| def-sc-group-scheme | Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, CategoryTheory.Grp and their homomorphisms |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth |
| pqf-def-affine-morphism | Mathlib.AlgebraicGeometry.Morphisms.Affine: AlgebraicGeometry.IsAffineHom |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact |
| def-weil-connected-scheme | Mathlib.Topology.Connected.Basic: ConnectedSpace, used within IsReductive |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion |
| def-sfb-split-solvable-right-torsors | Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions: RepresentedRightTorsor, including every field |
| def-pc-fppf-site | Mathlib.AlgebraicGeometry.Sites.Fpqc: Scheme.fppfTopology; Mathlib.CategoryTheory.Sites.Over: GrothendieckTopology.over |
| def-weil-pbc-sheafification | Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf and sheafificationAdjunction, rendered by their universal property |
| def-sfb-reductive-torus-centralizer-terminology | Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology: ReductiveTorusCentralizer.IsReductive |

GeneralLinearGroup and its group-object instance are reused from
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`; its coordinate
ring and point equivalence were read, including the localization definition in
`WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup`. `Over.pullback` and
its `mapGrp` transport are those of Mathlib's Cartesian monoidal slice. Proof
imports include all currently recorded proof-dependency modules; the three
statement-only proof inputs without Lean records (finite-free lattice, invariant
power lifting, free affine quotient) have no import to add yet.

Edge cases checked before writing:

- H trivial is allowed; it embeds in GL_1 and has quotient GL_1. n=0 is excluded
  exactly as the statement requests, rather than making nontriviality of H an
  extra hypothesis.
- Empty T is allowed in the universal base-change quantifier; its empty products
  and quotient satisfy the same torsor and representability assertions.
- Identity base change is explicitly covered by taking T=Spec A and f=identity;
  canonical pullback isomorphisms recover the original quotient and torsor map.
- Nonaffine T, nonflat base changes, closed and generic geometric fibres, mixed
  and positive characteristic, nonsplit tori and imperfect residue fields remain
  included. There is no field-base substitution for the original DVR.
- An empty H cannot be a group object over nonempty Spec A: its identity section
  prevents it. ConnectedSpace, as used on fibres, includes nonemptiness.
- Test fields Ω are in Type u, the same universe as A, so maps to geometric
  residue fields are available; no unrelated smaller universe makes hred vacuous.
- All variables and the universe u are explicit; `autoImplicit` is false.

Searches run (msearch.py uses group Q123 and this item's id throughout):

- LeanSearch: `A reductive group scheme over a DVR has a faithful linear
  representation with affine quotient` returned eight results including
  `Rep.mkQ_hom`, `FGModuleRepr.repr` and `Representation.quotient_apply`; none
  concerns group schemes or their affine homogeneous quotients.
- LeanFinder: `A reductive group scheme over a discrete valuation ring embeds
  in a general linear group with affine fppf quotient` returned eight results,
  including topological special-linear embeddings and Weierstrass good
  reduction; no match for the statement.
- Loogle: `"GeneralLinearGroup"` returned twelve declarations concerning
  `LinearMap.GeneralLinearGroup`, not a group-scheme quotient theorem.
- msearch grep: `Reductive|reductive|Unipotent|GeneralLinearGroup` in Mathlib's
  AlgebraicGeometry returned zero hits.
- Local rg in lean/WeilConjectures for the exact node id returned no occurrence;
  rg for reductivity, general-linear groups, unipotence and cosets in
  lean/WeilConjectures and lean/Sheaf located the upstream GL construction,
  SolvableGroupStructure, ReductiveTorusCentralizerTerminology and the existing
  field-only homogeneous quotient theorems. Full signatures and docstrings were
  opened; none states this DVR theorem with universal affine quotient.
- rg for the proposed declaration name and DVR/reductive affine-quotient phrases
  found no declaration collision. DAG records were read for all stmt_deps,
  the additional reductive definition, and the existing homogeneous-quotient
  interfaces; no new notion or duplicate node is necessary.

Validation: scompile.py compiled the file in both sandbox and library module modes
cleanly. The first probe had a parser conflict with the scoped symbol eta; the
bound variable was renamed to the ordinary identifier `eta` before the successful
compile. Delivery dry-run and final compile results are recorded below.

## Second reading by Q123

I reopened the complete node and the delivered signature for a separate reading.
This is a second pass by the same dispatcher worker, not an independent-agent
review; the maintainer performs the independent delivery review. No other agents
were started.

The DVR, group object, smoothness, affine morphism and both finite-type components
match the initial hypotheses. The geometric-fibre predicate uses the existing
faithful-matrix definition rather than a new reductivity assumption. The positive
rank and closed group morphism match the linear-embedding conclusion. Q is affine
over the original base, and the pointwise action equation ties P's torsor to that
particular embedding. The coset coequalizer and its universal arrow specify the
fppf quotient rather than merely a map with unspecified fibres. Every scheme base
change uses the actual pullback of Q, projection, action and first projection,
and retains both the torsor square and universal arrow on generators.

I checked especially that the torsor space is only renamed by the displayed
isomorphism e, that the action uses right multiplication without an inverse, and
that no local-section, splitness, completeness or perfection hypothesis was
introduced. Using a pointwise presheaf coequalizer avoids adding a second quotient
definition or assuming existence of a small-valued sheafification on the large
site. No mathematical mismatch was found. Direct public imports were added for
all used statement-dependency notions after this reading; the signature did not
change.
