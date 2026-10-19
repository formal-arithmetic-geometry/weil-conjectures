## Worker report

The delivery states `AlgebraicGeometry.ContractedComponentData.generic_data` in
`Sheaf.TraceFormula.ContractedComponentGenericData`, with one theorem proof `sorry` and no
other postponed proofs. Its helper definitions construct the component's actual vanishing
ideal, restrict the scalar structure and cohomology action, and write down the sets and triples
already specified by this node. None chooses data from an existence theorem.

The source was read in Temkin, *Stable modification of relative curves*, §1.2, printed p. 2,
and Lemma 5.1(ii), printed p. 34:
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf . The former explicitly permits
empty markings and nonproper, nonseparated curves. The latter uses the contracted-component
weighted incidence graph. The node expressly gives an agent-stated generic numerical
refinement, retaining self-loops and all marking/ambient incidences; this delivery follows
that refinement verbatim. It does not add a modification or generic-isomorphism hypothesis.

Hypothesis and conclusion correspondence:

- Integral Noetherian base: `T : Scheme.{u}`, `[IsIntegral T]`,
  `[IsLocallyNoetherian T]`, `[CompactSpace T]`. These are exactly nonempty integral,
  locally Noetherian and quasi-compact, without imposing an extra base-field structure.
- The two multipointed curves: `P Q : MultipointedCurve T`, with P the node's `(Y,E)`
  and Q its `(X,D)`. The existing structure supplies flatness, local finite presentation,
  quasi-compactness and quasi-separatedness of both structural morphisms, fibrewise pure
  dimensions one and zero, the closed marking, and its commutative structural triangle.
  The last two finiteness properties together with local finite presentation express finite
  presentation, and are not separatedness or properness.
- Compatible T-morphisms: `f : P.Hom Q`. Its `curve_over`, `marking_over` and `comm`
  fields give both T-morphism conditions and compatibility with the markings.
- Properness of both maps: `hproperCurve : IsProper f.curve` and
  `hproperMarking : IsProper f.marking`. Neither concerns P.x or Q.x.
- Nodal geometric curve fibres: `hnodal` quantifies over all base points and all nonsmooth
  points in the chosen algebraic-closure fibre. `Orgogozo.IsOrdinaryDoublePoint` gives an
  isomorphism of the maximal-ideal completion to the actual two-variable quotient
  `Orgogozo.nodeRing`, compatible with the scalar field. The existing `geometricPoint`
  is Spec of the algebraic-closure map followed by `T.fromSpecResidueField t`.
- Etale markings in the ordinary fibres: `hetale` is
  `Etale (P.d.fiberToSpecResidueField t)` for each t. `hmarking` puts every point of the
  pulled-back marking in the smooth locus of the curve fibre over `T.residueField t`.
  In particular this is the stated fibrewise assumption, rather than an independently
  stronger global marking assumption.
- All choices of algebraic closure in the conclusions: quantify over `k : Type u`,
  `[Field k]`, `[Algebra (T.residueField t) k]`, `[IsAlgClosure (T.residueField t) k]`.
  `closurePoint` writes out the recorded geometric-fibre formula for this arbitrary k.
  The hypotheses use the standard chosen closure; this is exactly testing nodality after
  passage to an algebraic closure, while the conclusion asserts independence of the choice.
- Reduced irreducible components: `R : irreducibleComponents (pullback P.x s)` indexes
  components by their actual underlying subsets. `ideal R` is the existing
  `Scheme.IdealSheafData.vanishingIdeal` of its closed support; `(ideal R).subscheme` and
  its canonical immersion give the reduced induced closed subscheme, not a chosen or
  unconstrained representative.
- Contraction to one point: membership in `contracted f s` means that the image of R
  under the canonical `f.curveBaseChange s` is subsingleton. An irreducible component is
  nonempty, so its image is nonempty; thus this is a singleton, not the empty-image case.
- Properness over k: the first componentwise conjunct is
  `IsProper ((ideal R).subschemeι ≫ pullback.snd P.x s)`, with its actual scalar map.
- The invariant p: `genus k p R` invokes the existing `Scheme.arithmeticGenus` on the
  reduced component itself with `over k p R`; it does not normalize the component. That
  definition is `Module.finrank k` of `Scheme.Modules.H` of its structure module in degree
  one. `Scheme.Modules.H` is the Zariski cohomology of the underlying abelian sheaf,
  `Sheaf.H`, not module-sheaf derived cohomology. This is the same RΓ as the recorded
  `Sheaf.H'` at the terminal open, canonically identified by the free-representable
  description at the terminal object. The reused arithmetic-genus declaration already
  equips it with the natural scalar action via global sections; `h1Module` exposes that
  exact action. The explicit `Module.Finite` conjunct proves finiteness, independently
  of the default value of finrank on an infinite-dimensional vector space.
- The invariant a: `selfNodes p R` is the set of nonsmooth ambient points on R through
  which R is the unique global irreducible component. At an ordinary node there are
  exactly two local branches. They belong to R precisely when there is no other global
  component through the point. If the branches belong to different components, this
  test excludes the node; if both belong to R, it includes the node once. This is also
  the branch characterization in the landed `nodal_normalization_adjunction`. No
  normalization preimages or simplified graph edges are counted.
- The invariant b: `incidences P s R` is the intersection of R with the set union of
  the image of `P.markingBaseChange s` and the nonsmooth locus of the ambient curve.
  A set union counts distinct points. In particular a self-node counts once in b,
  independently of the separate a entry.
- Numerical finiteness and finiteness of the contracted list: the first part of the
  conclusion is for every t and every algebraic closure, not only over the generic open.
  It asserts `(contracted f s).Finite`, the `Module.Finite` statement just described,
  and `.Finite` for both `selfNodes` and `incidences`. The triple uses their `ncard`s.
- The nonempty generic open is `U : T.Opens` with `(U : Set T).Nonempty`.
- The fixed finite multiset is expressed by `n : ℕ` and `w : Fin n → ℕ × ℕ × ℕ`.
  For every t in U and every algebraic closure, `e : Fin n ≃ contracted f s` enumerates
  all and only the contracted components, each exactly once, and
  `triple P k s (e i).1 = w i` gives all three entries. Existence of a separate such
  bijection in each fibre is precisely equality of the finite multisets, including
  multiplicities of repeated triples. It does not claim that labelled components descend
  to T or compare them by a chosen labelling between fibres.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`,
  imported through the owning morphism module.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and `Scheme.Hom.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (via ordinary-double-point).
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` (via nodeRing).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`,
  `isClosed_of_mem_irreducibleComponents`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, specifying the actual
  `vanishingIdeal`, `subscheme` and `subschemeι` used here.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `Sheaf.H'`, the recorded
  object-cohomology interface; the existing arithmetic genus uses its global RΓ form
  `Sheaf.H` on the same Zariski site as explained above.
- The three additional statement dependencies are already landed nodes, not new notions:
  `def-trf-multipointed-curve-modification`, using `MultipointedCurve.Hom`, its
  `curveBaseChange`, and `MultipointedCurve.markingBaseChange` in
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`;
  `def-trf-orgogozo-induction-data`, using `Orgogozo.IsOrdinaryDoublePoint`, `nodeRing`
  and `geometricPoint` in `Sheaf.Paper.OrgogozoInductionData`;
  and `def-pc-genus`, using `Scheme.arithmeticGenus` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`. Each full declaration and
  source docstring was read. Their general interfaces apply directly here.

Proof dependency imports: `SemistableMarkedBaseChange`, `EventuallyProper`, and
`LimitAffineTransition` are imported without public visibility. The proper permanence,
finite-proper, proper-closed-image and Noetherian tools are supplied by the corresponding
Mathlib imports. `lem-trf-contracted-component-generic-spread` and
`lem-trf-contracted-component-no-extra-generic` have no recorded Lean declarations in the
read base, so there is no module for those proof dependencies to import yet. They are not
needed to type the statement. No proof dependency is replaced by a new axiom or hypothesis.

Edge cases checked: the integral base is nonempty; the marking may be empty; curve fibres
may be empty by the existing pure-dimension definition. If no component is contracted,
`n = 0` and `Fin 0` represent the empty multiset. A smooth contracted component has a = 0.
A self-node is counted once in each of a and b, whereas a node shared with another component
is excluded from a and included once in b. Repeated triples are retained because the
bijection counts components rather than distinct triples. No characteristic is excluded.
All schemes and residue-field closures use the same universe u, with no smaller independent
field universe that could make the tests vacuous. All binders are explicit.

Searches (all commands used group Q84 and this item):

- `msearch.py leanfinder`: "The multiset of arithmetic genera self nodes and distinct
  special points of contracted components of a nodal marked curve is generically constant".
  Eight hits, all Weierstrass-coordinate or minimal-model results; no statement match.
- `msearch.py loogle`: `irreducibleComponents, Multiset`. Zero hits.
- `msearch.py grep`: `contracted|selfNode|self_node|nodal` in `AlgebraicGeometry`.
  Zero Mathlib hits.
- `msearch.py leansearch`: "Generic constancy of contracted nodal curve component genus
  and special point counts". Eight hits, principally generic points of irreducible
  components, with no statement match.
- `rg` over the upstream `WeilConjectures` tree for contraction, self-node, special-point
  and the proposed declaration names found the abelian-variety rigidity lemma and no
  matching numerical generic-constancy theorem. `grep -rn` of the item id there had no hits.
- `rg` over shared `lean/Sheaf` found the existing morphism/marking helpers and the
  normalization branch characterization, which were read and reused conceptually. It
  found references in `StableModificationConstructibility` but no declaration of this
  theorem or these numerical helpers. Searches for `ContractedComponentData`, `closurePoint`,
  and definitions of `selfNodes` and `incidences` found no conflicting names.
- DAG searches for contracted-component numerical data and self-nodes located this item,
  its two proof lemmas and its constructibility consumer, not an existing definition of
  its triple. Helpers here only spell out this item's own canonical data.

No statement correction, dependency repair, new definition node or STATEMENT-DISPUTED flag
is needed. The node copy changes only lean and adds the three already landed statement
interfaces described above.

## Second reading by Q84

This is the author's second pass, not a claim of an independent agent review; the dispatcher
brief reserves independent review to the maintainer. I reopened the node and the complete
Lean module and checked the correspondence above. In particular, P and Q have the correct
source/target order, both morphisms are proper, the marking assumption is on ordinary
fibres, and the output tests every algebraic closure. The reduced component uses the
vanishing ideal, and genus is taken before normalization. The self-node predicate excludes
nodes on two distinct components, while the incidence union counts a loop only once.
The finite-list bijection preserves repeated triples and allows n = 0. The finiteness
conjunct is outside the generic-open quantifier. No mathematical mismatch was found;
compiler-driven changes only made the scalar-structure abbreviations reducible, made
`Scheme.Modules.H` explicit and added the category annotation on a pullback carrier.
The final required compile and delivery dry run are recorded by the prescribed wrappers.
