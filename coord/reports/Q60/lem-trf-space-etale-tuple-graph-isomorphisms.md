## Worker report

Item: lem-trf-space-etale-tuple-graph-isomorphisms. Module:
`Sheaf.AlgebraicGeometry.EtaleTupleGraphIsomorphisms`. Main declaration:
`AlgebraicGeometry.AlgebraicSpace.etale_tuple_graph_isomorphisms`.
The only postponed theorem is this main declaration, whose proof is `sorry` and whose
docstring gives all six steps of the DAG proof. Four explicit helper definitions implement
transition evaluation with canonical projection identifications, the graph arrow, the
coordinate of the tuple equalizer and graph evaluation. They introduce no alternative
module category, site, tuple sheaf or descent datum. All their data are actual constructions.

Source read: `literature/stacks-project/sites.tex`, Tag 04TR, lemma-glue-sheaves,
lines 5847–5888. Stacks explicitly omits the local isomorphisms and overlap diagrams;
this node supplies those computations, with transition orientation L_j to L_i. I also
read the latest blueprint ancestor `lem-trf-local-term-locality` and its proof. This
is an inherited descent input, and does not alter the current contracting-correspondence
route or any blueprint unit statement. No node statement correction is needed.

Hypotheses and clauses, in order:

- A scheme S and algebraic space F over it are `{S : Scheme.{u}}` and
  `(F : AlgebraicSpace S)`, using the recorded definitions verbatim.
- The set-indexed family of étale scheme charts is `{I : Type v}` and
  `(V : I → F.EtaleSite)`. This site's objects already include their schemes, maps to F
  and representable étaleness. Neither a covering nor a nonempty-index hypothesis occurs.
- The size convention is expressed by explicit universes `u v`, with coefficient section
  types in `max (u + 1) v`, exactly as in the tuple-sheaf dependency. It contains the site
  and index universes and supports all the section products. No extra smallness or equality
  of universes is imposed.
- R_ij is the binary product `V i ⨯ V j` in the recorded small étale site, with `prod.fst`
  and `prod.snd`. The dependency's representability theorem and instance supply these
  scheme fibre products. Product order is chart first, test object second, matching
  `tupleChartSheaf`; this merely reverses the displayed W times V_i notation canonically.
- Local module sheaves are `L i : ringedSiteModules (F.structureSheaf.over (V i))`.
  These are precisely modules on the localized sites required by the node. Restrictions
  to overlaps use `F.etalePullbackMap` of the two projections.
- Each `a i j` is an isomorphism from the restriction of L_j to the restriction of L_i.
  `tupleTransitionValue` evaluates its hom at the map to R_ij given by two lifts. Its
  identity underlying arrows in the two over categories implement the canonical
  composition/projection identifications, without an arbitrary comparison map.
- `hdiag` is identity after pullback along the diagonal: for every t:W→V_i it evaluates
  a_ii at (t,t) and says it fixes every section. It does not say that a_ii is identity
  on the whole self-overlap.
- `hcocycle` evaluates a_ik=a_ij a_jk on every test object with three lifts and every
  section of L_k. This is the pullback cocycle with its canonical composition
  identifications, expressed componentwise to avoid any equality-of-functors assumption.
- The node's specified M is `equalizer f g`, where `hf` and `hg` fix exactly the left
  restriction and transition-twisted right restriction coordinate formulas of
  `exists_etale_module_tuple_sheaf`. These parameters name that construction's arrows;
  they impose no further condition on the mathematical datum. The dependency gives
  their existence and identifies this equalizer's sections, restrictions and operations
  with the literal compatible tuples. There is no arbitrary replacement sheaf or choice
  of a nonunique sheaf from a mere existence statement.
- `tupleEqualizerCoordinate` is the product coordinate after the equalizer inclusion.
  `tupleGraphArrow` is `(t,1_W)` into V_i times W as an over-category morphism, and
  `tupleGraphValue` restricts the i coordinate along that arrow. Thus the first
  conclusion conjunct states exactly e_i,W(s)=d_i^*(s_i).
- The existential `e i : (F.etalePullback (V i)).obj (equalizer f g) ≅ L i` gives the
  required module-sheaf isomorphisms. Their hom and inv components are linear maps;
  their naturality is naturality in every morphism of `Over (V i)`. The two identities
  e j=1 and j e=1 are the isomorphisms' hom_inv_id and inv_hom_id, evaluated on sections.
  Consequently both displayed formulas are well-defined linear maps and are mutual
  inverses, rather than merely set bijections with no sheaf structure.
- The second conjunct specifies every coordinate of `(e i).inv` as
  `tupleTransitionValue ... (a k i).hom` applied to y restricted along `prod.snd`.
  The test object is exactly `(Over.star (V k)).obj W`; its second lift is
  `prod.snd ≫ t`, its first lift is its structural projection. This is the displayed
  j_i,W(y) formula, evaluated using (V_k projection, t after W projection).
- The final conjunct is the transition identity on every W with lifts t:W→V_i and
  s:W→V_j. These lifts equivalently specify any W→R_ij by the product universal
  property. The same unconstrained quantification includes i=j and t≠s. It says
  e_i,W=a_ij,W e_j,W, exactly with the node's orientation.
- There is no local freeness, joint surjectivity, scheme hypothesis on F, terminal
  object of F's site, or identity assumption away from the diagonal.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `structurePresheaf`, `structureSheaf`, `etalePullback`,
  `etalePullbackMap`. These provide the exact algebraic-space and localized-site notions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent alias of Mathlib's `SheafOfModules`, including its linear morphisms.
- `Sheaf.AlgebraicGeometry.EtaleModuleTupleSheaf`: `etaleSite_hasBinaryProducts`,
  `etaleSiteBinaryProducts`, `tupleChartSheaf`, `tupleOverlapSheaf`, `tupleProduct`,
  `tupleOverlapProduct`, `tupleProductCoordinates`, `tupleOverlapCoordinates`,
  `tupleLeftSection`, `tupleRightSection`, `moduleTupleSections`, and
  `exists_etale_module_tuple_sheaf`. Read the full module and verified the live server
  source with `scompile.py --source` after the first elaboration attempt.
- `def-weil-size-convention` has a convention-only Lean record; universes implement it.
- The proof-only import is `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`, whose
  `chartwise_etale_permanence` supplies the graph/site permanence used in proof step 1.
  All other proof dependencies are already public statement dependencies.
- Mathlib `Over.homMk`, `Over.star`, `prod.lift`, `equalizer.ι`, and the recorded module
  restrictions are reused. No localized-site transport or tuple construction is copied.

Edge cases checked mathematically: I empty makes the conclusion a vacuous family of
isomorphisms and the compatible module zero. Empty test schemes have zero section modules.
A single chart still has its full self-overlap, so it is not reduced to the diagonal.
For the two-point étale chart of a point with constant rank-one modules and transitions
multiplication by c_r/c_s, diagonal normalization holds but a_aa need not be identity off
its diagonal; the statement retains these different-lift cases. A non-surjective family
still has the graph over each of its own charts, which is all the local calculation uses.
Zero modules, non-locally-free modules and spaces with no chosen terminal scheme object
are allowed. No counterexample or STATEMENT-DISPUTED issue was found.

Searches for an existing declaration (all run through the prescribed wrapper unless rg):

- LeanFinder: “Graph evaluation of compatible tuples of local module sheaves is an
  isomorphism with inverse given by cocycle transition maps”. Eight hits, including
  `CategoryTheory.evalEquiv_symm_apply`, `SheafOfModules.Presentation.map_π_eq`,
  and topological-open equalizer isomorphisms. None treats these algebraic-space tuples.
- Loogle: `SheafOfModules, CategoryTheory.Iso`. Twelve hits, including
  `SheafOfModules.toSheafCompSheafToPresheafIso` and free-sheaf functor comparisons.
  No graph-evaluation or descent result.
- LeanSearch: “Compatible module sheaf tuples restricted to a chart have inverse graph
  evaluation and transition maps”. Eight hits, including `Scheme.Modules.inv_app`,
  `ModuleCat.Tilde.res_apply`, topological-open gluing and smooth-sheaf evaluation.
  None has the required graph and inverse coordinates.
- Mathlib grep: `graph.*[Ee]val|tuple.*[Ii]so|[Cc]ocycle` in
  `Algebra/Category/ModuleCat`: zero hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`, for tuple/graph evaluation and this node id: the torsor
  graph-injectivity/normalized-evaluation lemmas and unrelated graph constructions occur;
  none gives the arbitrary-family module-tuple local isomorphisms. The recorded
  `EtaleModuleTupleSheaf` is the prerequisite construction, not this conclusion.

Validation: prescribed scompile.py completed successfully in sandbox mode (37.6 s) and
library-module mode (16.5 s), with no errors or warnings. The elaboration repair makes
`tupleTransitionValue` accept the actual over-category object, so the inverse formula
uses `Over.star` directly instead of assuming definitional equality of a rebuilt object.
The statement is unchanged by that implementation repair. All variables are explicit
and `autoImplicit` is disabled; all lines are at most 100 characters.

## Second reading by Q60

Author's separate second pass, not an independent review; the dispatcher brief forbids
starting another agent and assigns independent review to the maintainer. I reopened the
node and module and checked each clause against the correspondence above. In particular,
`hdiag` tests identical lifts only, `hcocycle` uses the order a_ij after a_jk, `hf/hg`
are the dependency's precise two arrows, the inverse formula uses k,i rather than i,k,
and the last conjunct has no distinct-index condition. Module isomorphisms include both
naturality directions, linearity and both inverse identities. The graph uses the
chart-first product convention of the dependency. The localized test object in the
inverse was changed from a reconstructed `Over.mk prod.fst` to the actual `Over.star`
object to retain its canonical identifications through module-mode elaboration. No
hypothesis or conclusion was changed, no new node or dependency repair is needed,
and the item's JSON differs from the read clone only in `lean`.
