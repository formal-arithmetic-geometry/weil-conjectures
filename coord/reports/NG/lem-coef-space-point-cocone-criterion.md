## Worker report

The module `Sheaf.CategoryTheory.SpacePointCoconeCriterion` states
`CategoryTheory.Spaces.space_point_cocone_criterion`. It does not prove the criterion.
It expresses the displayed natural equivalence as the canonical zigzag

`pointCoconeMappingSpace K Y → pointCoconeArrowSpace K Y ← ULift Fun(K,Y)`.

Both legs have actual inverse simplicial maps and two cylinder homotopies. This is an
equivalence of spaces, not a degreewise isomorphism of the right-pinched and enriched
mapping models. No inverse is chosen in a definition. The existential comparison maps
are specified by formulas, rather than being arbitrary equivalences of the spaces.

Clause-by-clause correspondence:

- The universe W is `u`. The index is `K : SSet.{u}` and the space is `Y : Spaces.Kan.{u}`;
  `Y.property` is exactly Kan fibrancy, without inhabitation. The category of spaces is
  the recorded `Spaces.infinityCategory.{u} : SSet.{u+1}`. `pointCoconeIndex` is the
  canonical degreewise `SSet.uliftFunctor.{u+1,u}`, used for K and for the small internal
  mapping simplicial set. It imposes no equality of the two universes and no size or
  fibrancy restriction on K.
- The point is literally `Δ[0]`, in `pointCoconePoint`. Its Kan proof uses the existing
  terminal-object fibrancy lemma, with the identity map; there is no nonempty-source
  assumption. `pointCoconeVertex` is the constant enriched functor on a Kan complex,
  with its actual identity morphisms. `pointCoconeVertex_laws` postpones only its two
  structure laws, not any data; its docstring supplies the elementary proof.
- The constant diagram `Δ_K Z` is `pointCoconeDiagram K Z`, namely the existing
  `SSet.const (pointCoconeVertex Z)`, in the full internal Hom into infinityCategory.
  `pointCoconeMappingSpace` is exactly the dependency's right-pinched `mappingSpace`
  between the vertices `diagramVertex` of the two constant diagrams.
- The displayed equivalence is the zigzag above. The three `KanComplex` conclusions
  record that its objects are spaces. The two existential inverse-map clauses state
  simplicial homotopy equivalence of both legs, including all parameters. The source
  internal Hom is lifted only to put the comparison maps in the same category of
  simplicial sets. No information is lost by this degreewise universe equivalence.
- The requirement that this is the family-of-points comparison, including every
  simplicial parameter, is `PointCoconeFamilyFormula`. For every parameter degree n,
  simplex t of Fun(K,Y), index degree m, k in K_m, interval simplex a and parameter
  simplex p, uncurrying the image twice gives a coherent-nerve simplex required to
  satisfy `PointCoconeSimplex Y (t.app _ p.op k) a`.
  Its objects are the point before the switch and Y after the switch. Within a block,
  all enriched maps are identities. On every mixed subset path, and on every chain
  of such paths in every degree r, the map is evaluation of the specified Y-simplex
  at the maximum initial-side vertex (`pointCoconeMaximum`). The ordinal α in this
  equation is uniquely specified by these maxima; it exists since inclusions of
  subsets increase their maxima. A mixed path contains its initial endpoint, so the
  empty-finset bottom default is never used in this equation. The formula is precisely
  the maximum comparison of proof steps 2--4. Its uniqueness in each degree makes it
  natural under restriction in K, postcomposition in Y, and all parameter restrictions;
  it is stronger information than a mere assertion of a natural isomorphism class.
  `HEq` here only compares the internal Homs after their two endpoint Kan complexes
  have been fixed by the preceding object equations; it does not discard their maps.
- The left zigzag leg is fixed by `PointCoconePinchFormula`: uncurrying its image in
  each degree is exactly precomposition by `rightPinchPrism`, the recorded canonical
  comparison. Naturality follows from this same prism equation in all degrees. Its
  homotopy inverse is asserted to exist, without asserting a natural choice of inverse.
- A specified coherent cocone is a vertex t of the recorded `coconeCategory` on the
  constant point diagram. `t.1.1 = pointCoconeVertex Y` fixes its apex to Y, so its edge
  is precisely a transformation from Δ_K* to Δ_KY. The theorem first concludes that
  an actual small map `e : K ⟶ Y.obj` representing it exists.
- `PointCoconeRepresents` requires that the actual cocone edge `t.1.2` is the image of
  an arrow-space vertex a, and that a and the image of `diagramVertex e` agree in
  `SSet.π₀` of that fixed-endpoint space. Since the arrow space is Kan, equality here
  means homotopy of coherent transformations with their endpoints fixed. This is
  exactly the node's “corresponding ... up to homotopy”; it is not just a comparison
  of the cocone's individual vertex legs.
- For EVERY representing e, the last equivalence is the dependency's
  `SSet.Enhanced.IsColimiting ... t ↔ SSet.Enhanced.IsWeakHomotopyEquivalence e`.
  The latter uses geometric realization, components and all positive based homotopy
  groups exactly as in the recorded definition. The criterion therefore applies to
  the particular cocone and is independent of the choice of its homotopic representative.

Statement dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `diagramVertex`, `constantDiagrams`, `coconeCategory`, `IsColimiting`, and
  `IsWeakHomotopyEquivalence`; the relevant definitions and their docstrings were read.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `CategoryTheory.Spaces.Kan`,
  `kanEnrichment`, and `infinityCategory`. This is the full coherent nerve of the small
  Kan complexes, with internal-Hom enrichment, not the ordinary nerve. Its full source
  and docstrings were read. Both dependency records give usable interfaces unchanged.

Other imports are the recorded proof plan: EnhancedFunctorConeCalculus,
KanMappingHomotopyInvariance, RealizationWeakEquivalence,
SimplicialHomotopyEquivalenceWeak, InfinityMappingComposition, RightPinchComparison,
KanCoherentNerveQuasicategory, PinchedRigidificationResolution, and Mathlib's Kan
internal-Hom instance in AnodyneExtensions.PushoutProduct. RightPinchComparison is
public because its canonical arrow-space/prism definitions occur in the statement.
PiZero and Finset.Lattice.Fold supply the existing homotopy-class and maximum APIs.
The complete nine-step node proof is retained in the main theorem's docstring.

Edge cases checked before writing:

- K empty: both cocone mapping models and Fun(K,Y) are contractible. A specified
  cocone is colimiting exactly when Y is empty, since ∅ → Y must be a weak equivalence.
- Y empty: if K has vertices, both mapping spaces are empty and there is no cocone
  with this apex. If K is empty, its unique cocone is colimiting. No Kan definition
  or hypothesis excludes the empty complex.
- K a point: the criterion says that its point cocone is universal exactly when Y is
  weakly contractible. The full parameter formula reduces to its family of points.
- K two discrete points: both components are retained; the constant map to a point
  fails the weak-equivalence test.
- K a simplicial circle and Y a point: the unique cocone exists, but is not colimiting;
  the criterion detects the nontrivial fundamental group of K. Thus no ordinary
  connected-category colimit criterion has replaced the statement.
- Degenerate simplices and arbitrary parameter restrictions: monotone maps commute
  with maximum on the nonempty initial subsets; the switch formula therefore respects
  all faces and degeneracies, including collapses of parameter vertices.

Searches for an existing statement and helper constructions:

1. `msearch.py ... leansearch "mapping space of constant diagrams of Kan complexes from
   the point and criterion for colimiting cocones"`: eight ordinary-category colimit
   results, including Limits.isColimitConstCocone and connected-index results. Their
   signatures concern ordinary categories and lose the homotopy type of a circle;
   none states this coherent mapping-space comparison or its criterion.
2. `msearch.py ... leanfinder "mapping spaces in the homotopy coherent nerve of Kan
   complexes equivalent to internal Hom"`: ordinary nerve edge equivalences,
   OneTruncation₂, nerve/homotopy-category adjunctions, prodStdSimplex.isoNerve,
   and SimplicialNerve; none gives the comparison. Read SimplicialNerve in full.
3. `msearch.py ... loogle '"SimplicialNerve"'`: only CategoryTheory.SimplicialNerve,
   the construction already used by the dependency, not this theorem.
4. `msearch.py ... grep 'mappingSpace|SimplicialNerve|constant.*point|point.*cocone'
   AlgebraicTopology`: five hits, all in Mathlib.AlgebraicTopology.SimplicialNerve,
   construction or project comments. No comparison theorem.
5. `msearch.py ... grep 'SimplicialNerve|mappingSpace|copower' CategoryTheory`: ordinary
   well-copowered-category results and monoidal-action terminology; no match.
6. Direct rg in Mathlib, WeilConjectures and lean/Sheaf for pointCocone,
   space_point_cocone_criterion, PointCoconeSimplex and PointCoconeRepresents returned
   no existing declarations. `grep -rn 'lem-coef-space-point-cocone-criterion'` in the
   upstream WeilConjectures source returned no match. Broader project searches found
   downstream point-vertex and edge-reading helpers in InfinityYonedaEvaluation,
   InfinitySpaceValuedPointwiseLan, SpaceYonedaDensity and SpaceTransportClassification;
   their sources were inspected. They do not state this comparison and importing them
   would reverse the DAG route noted in this node's stage-1 review. The vertex helper
   here supplies only the real constant enriched vertex and its structure laws.

Sources opened: [Kerodon 03F8](https://kerodon.net/tag/03F8),
[03F6](https://kerodon.net/tag/03F6), and [06QR](https://kerodon.net/tag/06QR).
They agree with the node; in particular 06QR warns that the nerve mapping comparison
is generally not an isomorphism. No statement correction or disputed statement.
No new nodes and no dependency repairs are required. The only node field changed is lean.

Verification: compilation uses only the prescribed scompile.py wrapper. All delivered
Lean is in this one module. The final scompile.py run compiled both the sandbox
module and its library-path form successfully (about two seconds each), with no
warnings or errors. The required deliver2.py --no-push run printed OK for dry-run commit
`f5d45efd2f`: compilation and server preflight passed, except for the independent
second-reading section which the next worker supplies. Nothing was pushed. There are two postponed named theorems: the constant
vertex's structural laws and the main criterion; all definition data are explicit.

## Second reading by NG

I reread the source statement (Kerodon 03F8, with the copower criterion 03F6 and
mapping-space comparison 06QR), the dependency declarations, and the complete Lean
module.  The node introduces a universe \(\mathcal W\), a \(\mathcal W\)-small
simplicial set \(K\), a \(\mathcal W\)-small Kan complex \(Y\), the point
\(\Delta^0\), and the constant diagram \(\Delta_KY\).  Its first clause is the
natural equivalence of the cocone mapping space with \(\operatorname{Fun}(K,Y)\);
its second clause assigns to each cocone with apex \(Y\) a representing map
\(e_\lambda:K\to Y\), up to homotopy; its final clause is the equivalence between
being colimiting and being a weak homotopy equivalence.  It imposes no nonemptiness,
connectedness, characteristic, or finiteness hypothesis.

The Lean rendering matches these objects item by item.  `pointCoconePoint` is the
literal standard zero-simplex with a Kan proof, `pointCoconeVertex` and
`pointCoconeDiagram` are the constant coherent vertex and diagram,
`pointCoconeMappingSpace` is the dependency's right-pinched mapping space, and
`pointCoconeArrowSpace` is the fixed-endpoint arrow-space intermediary.  The
universe lift in `pointCoconeIndex` puts the internal Hom and arrow models in the
containing universe while leaving `K` and `Y` in universe `u`; no equality of these
universes is assumed.  `PointCoconeFamilyFormula` quantifies every degree, simplex,
index simplex, interval simplex, and parameter simplex and imposes the maximum
initial-vertex formula, which is the stated family-of-points comparison.  The
homotopy-inverse clauses for `b` and the pinch map `j`, together with the three Kan
clauses, unpack the displayed equivalence of spaces through the canonical arrow
model.  `PointCoconeRepresents` fixes the cocone's apex to `Y`, fixes the actual
arrow-space vertex, and compares it with `diagramVertex e` in `SSet.π₀`, exactly the
node's “up to homotopy” representative.  The final quantified biconditional is the
node's colimiting/weak-equivalence criterion for every representing `e`.

I found no mismatch and made no code or node change.  In particular, the apparent
absence of a separate naturality binder is intentional: the family formula's full
simplicial-parameter quantification is the explicit degreewise natural comparison
used by the source, while `PointCoconePinchFormula` fixes the canonical prism leg in
every degree.  No stronger hypothesis is present: `K` need not be Kan or inhabited,
`Y` may be empty, and all Kan conditions are conclusions about the mapping models
or the internal Hom, not assumptions on `K`.

Edge cases checked independently are `K = ∅` (the unique cocone is colimiting
exactly when `Y = ∅`), `Y = ∅` (no cocone when `K` has a simplex), a point index
(the criterion reduces to weak contractibility of `Y`), two discrete points (both
components are retained), a simplicial circle with point target (the fundamental
group obstruction remains), degenerate simplices and parameter restrictions, and
all dimensions including zero.  The zero-simplex construction has no hidden
inhabitation assumption.

For the one-definition-per-notion check I searched the project and Mathlib by the
item and helper names (`rg` for `pointCocone`, `space_point_cocone_criterion`, and
`PointCoconeSimplex`), and by concepts using LeanSearch, LeanFinder, Loogle, and
grep for mapping spaces of constant point diagrams, homotopy-coherent nerves,
and copowers.  The hits were ordinary nerve/cocone or set-valued colimit results;
none has the coherent Kan-space statement.  I also read the recorded declarations
in `EnhancedDiagramsCones`, `InfinityCategoryOfSpaces`, and `RightPinchComparison`:
they supply exactly the mapping, Kan, cocone, weak-equivalence, and prism notions
used here.  There are no new nodes, dependency repairs, statement correction, or
existing declaration to record.
