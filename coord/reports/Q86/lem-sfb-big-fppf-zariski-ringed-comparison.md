# Stage-1 delivery: lem-sfb-big-fppf-zariski-ringed-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-big-fppf-zariski-ringed-comparison.json`: statement, split into ten proof steps using fifteen existing dependencies; not a Mathlib leaf. Statement and statement dependencies unchanged.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: one entry for every step/dependency pair, quoting the cited statement verbatim.
- `searches.jsonl`: the five actual Q86 Mathlib searches, retained across the launcher pause. The inherited Q62 research is retained in the item; Q86 entries were appended from the actual log.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code, not part of the delivery.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag and by big-fppf, Zariski/ringed, 070R and 070S terminology. The project has the Zariski-covering/fppf inclusion and several small-etale tensor-section lemmas, but no declaration supplying every clause of this item. The small-etale statements do not apply to arbitrary big-site arrows. I also inspected the corresponding `lean/Sheaf/` hits without counting them as attachments.

## WANTED

None. The item and all proof inputs used here have their source texts in the repository.

## Findings and changes

The supplied statement agrees with Stacks Descent 070R, `remark-change-topologies-ringed`, and 070S(1), `lemma-compare-sites`; it does not need a statement correction. The imported node had no proof. Its arbitrary-module scope matters: the section presheaf need not already be an fppf sheaf, and quasi-coherent descent must not be applied to the arbitrary module M.

I supplied a direct universal-property proof. The printed proof of 070S(1) first passes through the big Zariski site, uses the small-site restriction morphism and transitivity, and then sheafifies for the stronger topology. Here the same comparison is checked directly from the scheme-module adjunction: a map on Zariski opens extends by adjunction on each test scheme; its compatibility with every scheme arrow and its uniqueness are written out. Accordingly `proof_origin.by` is `agent`, not `document`.

I read the current `literature/blueprint/latest/` unit and the direct-images proof, as well as the recorded unit/chapter. This is a supporting module-comparison prerequisite on the already recorded alteration branch, not the key node of the six-functor unit. The unit/chapter records were not changed. `blueprint_refs.py ancestor` returns None: the existing created.item chain terminates at `Sheaf.SixFunctors.CtfStabilityDirectImages`, which is a Lean-module item rather than a blueprint node. I retained the null `from.node`, its complete non-unspecified place and its via chain; the server's split check accepts them. This provenance limitation is reported, not concealed by inventing an ancestor. The whole-blueprint searches for “big fppf”, “tensor sections” and 070S found no statement duplicating the item; the big-fppf site definition and Picard-functor statement are different notions.

The generic off-unit statements are declared individually in `split_report.tool_uses`. They are scheme-module, covering, geometric-adjunction and adjoint-uniqueness tools. They do not replace a step of the six-functor unit. No top-level maintainer-owned tool_uses or review fields were set.

## What remains unfinished

No mathematical part of this split remains unfinished. The existing dependency nodes retain their own proof status. The server noted that the enclosing unit has no realization recorded; this supporting item does not own the unit realization fields.

## Mathlib searches

I read the actual Q86 log and search results before reusing them after the pause. The two semantic phrasings distinguish the ringed big-to-small comparison from generic module pullback. LeanFinder returned `SheafOfModules.sheafificationCompPullback` and scheme-module pullback/adjunction declarations on the first phrasing, and tilde, scheme module sheaves and restriction on the second. Loogle returned presheaf module pullbacks, their adjunction and composition. LeanSearch returned sheafification and generic continuous-site pullback adjunctions. The grep found Zariski-to-fppf covering inclusion and `sheafificationCompPullback`.

I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, especially the pullback adjunction and `sheafificationCompPullback` at line 118, and `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, especially scheme pushforward, pullback and their adjunction at lines 169–190. The former compares generic module presheaf pullback and sheafification; it does not identify that presheaf with Γ(T,u*M), construct this site comparison, or give its open-unit formula. The latter is the scheme-module ingredient already represented by existing DAG nodes. These are useful inputs, not an exact or one-line match for the item. All five Q86 queries are recorded exactly as run; none was unavailable.

## Not duplicates

No new nodes were created. I reused the existing general tools. In particular I did not create big-site variants of the small-etale adjunction-extension and open-determination nodes: their actual statements are limited to the small etale site, so I wrote the required arbitrary-arrow argument in the item's proof instead of citing them beyond their hypotheses.

## Review by Q86

I read Stacks `descent.tex` 070R and the entire statement/proof of 070S, including its arbitrary-module hypothesis, and the structure-sheaf discussion 03DT/03DU. I also read the change-of-topologies list in `topologies.tex` and the scheme-module adjunction/composition discussion in `sheaves.tex` 0096/0097, and the inverse-image module adjunction in `sites-modules.tex` 03D3. No SGA source is used. There are no new-node statements requiring a separate source review.

For step 1 I opened the statements of `lem-weil-pbc-spec-tilde-free-module`, `pqf-def-coherent`, `lem-weil-pbc-module-pullback-structure-sheaf`, `lem-trf-fppf-covering-is-fpqc` and `lem-sc-etale-qcoherent-descent-fpqc-sections`. They provide respectively the rank-one affine tilde identification, the affine-local definition of quasi-coherence, the unit-compatible structure-sheaf pullback, inclusion of covering families, and descent of sections for any scheme map and any fpqc covering. Their hypotheses hold with F=O_S. Only this structure module is assumed quasi-coherent in this step; M remains arbitrary.

For step 2 I opened `lem-weil-pbc-open-preimage-fibre-product`, `lem-pc-zariski-coverings-are-fppf`, `lem-weil-pbc-left-exact-site-inverse-image-tensor` and `lem-weil-pbc-continuous-ringed-topos-module-direct-image`. The first two are exactly the geometric checks needed for the inclusion of opens. The third really asserts the geometric adjunction when finite limits and coverings are preserved, and allows site-small presentations in a larger value universe. The fourth constructs the ringed morphism with the continuous-site module direct image. I verified its coefficient map is the sectionwise identity O_S=R(O), so the module functor is actual restriction, not an unrelated equivalent right adjoint.

For step 3 I opened `lem-pc-module-pullback-adjunction`, `def-weil-pbc-composite-adjunction`, `lem-weil-pbc-conjugate-iso-unit-equation` and `lem-weil-pbc-open-immersion-module-pullback-restriction`. The first is for arbitrary scheme morphisms and arbitrary modules. The composite-adjunction node states the precise unit formula used. The uniqueness theorem states existence and invertibility of the comparison normalized by units; I use the statement, not any extra property of its proof. The open-immersion node explicitly includes its unit equation. Thus the pullback compositors and their compatibility with restrictions are fixed before later equations use them.

For step 4 I checked that those normalized units give the identity and composition of restrictions, and that naturality supplies the map P_v. The cited module-presheaf node defines semilinearity on arrows and the functor's codomain. This is a direct verification from the fixed adjunctions, rather than an invocation of the small-etale functoriality theorem for non-etale objects. For step 5, the covering inclusion ensures G_u is a Zariski sheaf and the scheme-module adjunction gives the unique a_u from the explicitly displayed b_u. No descent theorem for M is hidden here.

For step 6 I checked the two maps have the same source h*u*M and target G_uh. The cited composite-adjunction formula sends them to b_uh and u_*gamma_h composed with b_u; these are equal on every source open W by ordinary composition of restrictions in G. The step then uses the adjunction equation for d_h on global sections. This checks all big-site arrows, including nonflat arrows; it does not assume that arrows in the big fppf site themselves are covering maps.

For step 7 I checked that theta on all opens A of a fixed T forms a morphism of Zariski sheaves u*M→G_u, using the open-pullback comparison already fixed. Its adjunct is computed on a source open W by naturality for the actual arrow u^{-1}W→W; the normalized unit identifies the section used in this computation. The adjunction therefore proves equality with a_u, not merely agreement on a subset of global generators. Conversely, at an open test scheme its equation is the prescribed beta. Both inverses of the Hom bijection are proved, without tensor-section generation, a flatness hypothesis, or a quasi-coherence hypothesis.

For step 8 the same scheme-module adjunction has natural Hom bijections, and the explicit b_u formula proves simultaneous naturality in M and G. The statement of `def-weil-presheaf-modules-sheafification` really includes the linear universal property, so it gives exactly the first Hom bijection displayed there. For step 9 I opened `lem-weil-pbc-ringed-topoi-module-adjunction`: it is stated for arbitrary ringed topoi and gives the tensor formula left adjoint to the direct image with the adjunct scalar action. These hypotheses were established in step 2. The uniqueness statement then supplies a natural module-sheaf isomorphism with its unit normalization. For step 10 I traced the identity map through the two Hom bijections, obtaining q_M on presheaves and then q_M(j)Γ(kappa_j) on opens. This verifies the exact final equation of the item, not just existence of an unspecified natural isomorphism.

I checked all fifteen dependency statements and supplied a verbatim quote for each use. I also checked their dependency closures do not return to this item. The proof-dependency list is exactly the union of step uses. No step is longer than 2000 characters (the longest is 1035), and no new node moves an item clause into a black box. The two elementary steps are the presheaf identity/composition bookkeeping after step 3 and the final evaluation of the established Hom bijections; all adjunction and descent inputs themselves are cited.

I tested the zero module, empty scheme and empty open, identity arrows and open arrows, and arbitrary nonflat test morphisms. On the empty scheme all section groups and Hom equations are the forced zero-module ones; no nonempty cover is chosen. For general M no tensor-on-global-sections equality, finite presentation, separation, quasi-compactness or affineness assumption is made. Step 1 uses affines only to verify O_S is quasi-coherent locally, not to intersect affine opens or restrict the allowed test schemes. These checks required no statement correction.

The preliminary server-only `review_split` check passed with zero new nodes. The required full delivery dry run and push follow this report.
