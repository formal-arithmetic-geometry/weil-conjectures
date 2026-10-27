## Worker report

The module `Sheaf.CategoryTheory.SiteCoherenceDescent` states
`CategoryTheory.WitnessedSiteCoherence.siteCoherenceDescent`. Its single proof is
`sorry`; every helper has real data. The node statement is unchanged. The helper
structures package the data and clauses of this one assertion, rather than
introducing an independent mathematical notion. No new DAG node is needed.

Hypothesis-by-hypothesis correspondence:

- Ordinary categories: `B`, `E X`, `P X`, and `I f` have Mathlib `Category`
  instances, with independent object and morphism universes. The dependency
  `def-nagata-category` matches `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic`; its full signature, data and laws were
  read. Mathlib `Functor`, `NatTrans`, and functor-category `Iso` render precisely
  the introductory definitions. Their signatures and docstrings were read too.
- The supplied N, F^e, F^p, C are fields `N`, `Fe`, `Fp`, `C` of
  `SiteComparisonData`. The orientation of C is Fe followed by N, to N followed
  by Fp. The comparison's inverse is actual isomorphism data.
- Nonempty cofiltered refinement categories: `SiteComparisonLaws.cofiltered`
  uses Mathlib `IsCofiltered`; its definition includes common sources,
  equalization and nonemptiness. There is no smallness equality imposed.
- Witnessed inputs: `atWitness S a A ξ` is U(ξ^-1), a(A), V(ξ) in diagrammatic
  order. There are no components on arbitrary unwitnessed objects. All pro
  transformations `rp` and `ap` are natural transformations from the etale input
  category after N, exactly the naturality in E required by the node. Their
  witness extension is prescribed by this real definition.
- Refinements: `re`, `rp`, `refinement_square`. The `re` iso is contravariant
  in refinement arrows. The square reads N(re); C_d = C_c; rp. The common-source
  etale comparisons are supplied as `te`: `te_id`, `te_comp`, `te_refine`
  express the assumed independence and cocycle, as well as coherent refinement
  comparisons. In particular the comparison for any common source a,b is
  re(a);re(b)^-1 by these equations. No new pro law is assumed here.
- Compatible towers: `Tower`, `first`, `second`, `output`, with
  `tower_nonempty` and `common_tower`. The latter says their three candidate
  projections have simultaneous refining legs from another tower. Every
  arbitrary candidate compares to a tower candidate by the supplied `te` and
  its inverse; all such comparisons are refinement comparisons by the preceding
  common-source equations and cofilteredness.
- Etale tower maps descend to associative unital maps: `ae`,
  `etale_descent`, `etale_assoc`, `etale_left_unit`, `etale_right_unit`.
  Here `ae` is the assumed descended map for every candidate triple; its
  restriction to tower projections is the supplied etale tower map. Thus its
  existence is an etale hypothesis, as in the node, not a pro-side conclusion
  assumed in advance. `w : f ≫ g = k` only names the composite arrow so both
  associations have the same output candidate type. It adds no restriction.
- The computed pro tower map is `ap`, with the displayed equation
  `tower_square`. The source iso `binaryComparison` has components
  C_g(Fe_f A); Fp_g(C_f A), exactly B in the node proof. The given `ap` remains
  arbitrary subject to this square; it is not defined as transport.
- Given identity identifications: `ue` and `up`. `identity_square` is C_id=1
  under these identifications, namely C_id;up = N(ue). It accommodates
  nontrivial chosen identifications and avoids silently strictifying them.
- Moving arbitrary candidates to a tower and back is `towerPaste`, built from
  `inputChange`, the computed `ap`, and the output `change`. The latter has
  actual inverse data from C and the assumed etale comparisons. Using the
  explicit conjugate inverse avoids using an unproved `IsIso` instance to
  define data. Its equality with the inverse refinement map follows from the
  conclusion's refinement formula. `towerAtWitness` performs the specified
  conjugation of this computed paste. `transportedComposition` is a separately
  defined comparison, used only on the right side of the descent conclusion.

Conclusion-by-clause correspondence in `SiteComparisonConclusion`:

- `refinement`: invertibility of each rp on N(A), and precisely
  C_c^-1;N(re);C_d (diagrammatic order).
- `common_refinement`: every literal common-source paste `commonPaste` equals
  `change`, hence is independent of the source and its arrows. Its inverse leg
  is the explicit C-conjugate of the etale inverse; the refinement clause
  identifies it with the actual inverse of rp.
- `change_identity`, `change_cocycle`, `refinement_identity`,
  `refinement_composition`: identities, composition and cocycle. These also
  determine arbitrary finite refinement zigzags by composing their edges.
- `descent`: the computed `towerPaste` equals `transportedComposition` on every
  etale input and for every tower, with arbitrary candidates.
- `tower_independence`: equality for any two towers, including any common
  refining towers. `composition_square` is the exact displayed composition
  equation for arbitrary candidates. `composition_invertible` gives actual
  invertibility of the computed paste, not merely of an unrelated iso.
- `witnessed_descent` states that the computed `towerAtWitness` equals
  `atWitness` of the transport comparison and is invertible.
- `naturality` is the square for any morphism A to A' for each computed paste.
  Refinement/change naturality is already the `NatTrans` data. Inverse and
  composite naturality follows by the component equations.
- `triple_formula` states that D followed by EACH pro triple path equals
  N(the common etale triple map) followed by C_hgf. The right path uses the
  actual intermediate witness C_f(A), as specified by the node.
- `witnessed_associativity` identifies the two paths for arbitrary ξ. In
  `tripleRight` the intermediate witness is explicitly
  `(C_f.app A) ≪≫ Fp_f.mapIso ξ`, as required.
- `witnessed_left_unit`, `witnessed_right_unit` give both unit laws under the
  supplied identifications, including non-strict unit functors.
- `witnessed_change_identity`, `witnessed_change_cocycle`,
  `witnessed_change_invertible`, `witnessed_composition_invertible` give the
  corresponding assertions at arbitrary supplied witnesses.
- `witness_naturality` states naturality for any arrow compatible with the
  specified witness change and an etale input arrow. It deliberately does not
  quantify over unrelated pro-side arrows. It applies to every map after
  descent, since these are natural transformations on the image. Equalities of
  all conjugated component maps follow by substitution into `atWitness`.

The theorem docstring carries all ten proof steps from the node, including the
common-refinement, binary-input change, two triple-path and witness calculations.
The only postponed proof is this theorem, matched to this DAG node.

Edge cases checked before and after writing: empty base category and empty fibre
categories (universal assertions stay valid); singleton refinement categories;
identity refinements; repeated candidates; identity base arrows and both units;
non-strict given unit identifications; arbitrary nonidentity witnesses; N not
full, not faithful and not essentially surjective; site and coefficient categories
with different object/morphism universes; arbitrary tower-index universe. No
existence of a triple tower is assumed. Only binary towers are needed. The target
node is not itself the blueprint unit statement and no correction was needed.

Searches (all performed before adding declarations):

- `msearch.py`, LeanFinder: “Transport associative unital composition between
  functor families through natural isomorphisms on witnessed inputs and common
  refinements”. Eight hits, including `Functor.map_comp_heq`,
  `SmallObject.SuccStruct.Iteration.subsingleton.mapEq_trans`, `Pi.comapComp`,
  and `Functor.mapIso_trans`; none gives this full assertion.
- `msearch.py`, Loogle: `CategoryTheory.Functor.associator`. Twelve hits:
  associator, triangle and whiskering identities. Their interfaces are generic
  components, not witnessed descent. Used Mathlib associators and whiskering
  directly rather than copying them.
- `msearch.py`, LeanSearch: “Natural isomorphisms transport composition unit
  associativity and independence of common refinements between functor families”.
  Eight hits: monoidal transport, pi natural isos, mapMon composition and
  component-iso construction. None matches the supplied refinement/tower lemma.
- `msearch.py`, grep, CategoryTheory:
  `cofiltered.*coheren|refinement.*associat|conjugat.*compos`.
  Five hits: adjunction mate conjugation and hypercover refinements; none matches.
- `rg` in WeilConjectures and Sheaf for site coherence, witnessed coherence,
  witness transport and common-refinement names; `grep -rn` of the exact node
  id in WeilConjectures found nothing. Read the related
  `Sheaf.Paper.FiniteCompactSiteCoherence` interface: it is a geometric
  specialization using concrete etale/pro-etale derived categories, not this
  abstract assertion. The existing CompactSupportSiteCoherence likewise does
  not provide the abstract witnessed assertion. CategoryTheory searches found
  only unrelated Cech transport and triangle refinements.
- DAG search for `site-coherence-descent` and “witnessed comparison”, plus
  `tools/blueprint_refs.py search 'witnessed comparison'`: the latter returned
  none; node references were this node and its geometric consumer. No existing
  declaration of the general assertion was found. No repair note for this item
  was present.

Sources opened: local Stacks `more-etale.tex`, labels
`lemma-shriek-well-defined`, `lemma-shriek-composition`, `lemma-pseudo-functor`
(lines 3081, 3159, 3374), together with this node's complete agent categorical
proof. This is the node's abstract transport version, not a claim that Stacks
states this abstract signature verbatim.

Validation: `scompile.py` compiled the final sandbox and actual module paths
cleanly on the server (7.9 and 6.6 seconds), without errors or warnings.

## Second reading by Q44

No separate worker was started: the dispatcher's explicit instruction prohibits
other agents, and the maintainer performs the independent review. I reread the
node beside the final file. Corrected an associator placement so the transported
map really has source N followed by the composite Fp functor; made the tower
universe explicit; added `towerAtWitness` and `witnessed_descent` so the computed
paste, not just a transported iso, is covered at arbitrary witnesses. Checked
refinement orientation, both triple paths and both unit identifications against
the node equations. The detailed correspondence above covers every hypothesis
and conclusion; no mathematical statement correction or dependency repair was
made.
