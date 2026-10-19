# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-general/sk-l-dl-general-quasifinite.json`: statement unchanged. Ten proof steps preserve the finite compactification and affine-chart repair, add the explicit framework/PBC comparison, and calculate weights for the original arbitrary embedding.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-framework-pbc-open-exchange-comparison.json`: one new statement-only lemma, status `unsplit`, no proof or proof dependencies. No Mathlib match.
- `dag/units/sk-l-dl-general-quasifinite.json`: retained change to `realized` and `realized_by` only; the item realizes the statement and the unit's one proof paragraph.
- `citations.json`: regenerated for all ten steps, with one verbatim statement excerpt for every citation. Existing valid quotations are retained; obsolete isomorphism-only weight citations are replaced by weight-free statements.
- `report.md`: retains the two-objection repair of `c1dde7e4a9` and adds the F1 repair of returned head `d219aca8d8`, including all audit inputs in the delivered report itself. The valid earlier attachment audit, missing-source request and absolute-separatedness counterexample remain below. `searches.jsonl` retains the original eight item searches and appends only searches actually run for the new comparison lemma.

## Attachments

None. The retained source search found the three item-tagged declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/DeligneLaumon/Reduction/FormalSteps.lean:575,583,593`. I reread lines 563–605, including all hypotheses, docstrings and proof bodies. Each of the three bodies is `sorry`; the subsequent `HasDirectImageWeightBound.of_locallyQuasiFinite` uses them. No completed attachment states all clauses.

The imported audit refers to a different checkout: `QuasiFiniteVanishing.lean`, `QuasiFiniteWeights.lean`, `LowerShriekFunctoriality.lean` and `StalkExtensionByZero.lean` are absent from the supplied source. I retain that metadata, and do not treat the recorded later line numbers or `sorry: false` wrappers as finished proofs here. The actual matching declarations are sorried. The source's shape is consistent with the item: the morphism is separated; the target is quasi-separated and finite type, without absolute separatedness. The open audit entries are represented by the existing finite-adic-image, extension-by-zero and functoriality nodes, whose statements this proof uses directly where applicable. No new unaudited Lean assertion is introduced.


## WANTED

WANTED: `weil_conjectures_complete_notes.pdf`, §12.2, Lemmas 12.2–12.5, for sk-l-dl-general-quasifinite. The chapter names it and `literature/LIST.md` records it as missing. The proof is marked `proof_origin.by: agent`; I do not claim to have read those notes.


## Return repaired: C1/C4/E5 and E1/C4

I compared the retained item with the current shared main snapshot: main still has status `imported`, no reviewed split, and exactly the same statement. The retained returned-head split had seven steps and no new nodes. The required initial dry run exited successfully at `046102f623`; that mechanical pass did not resolve either mathematical objection. I changed the proof and added the comparison node afterwards. The delivery tool rebases this sandbox overlay onto its fetched current main in its temporary worktree; I ran no git command in the read-only shared repository.

C1/C4/E5 (former Step 3): a theorem about PBC functors was applied directly to a framework derived-limit functor. Steps 3-4 now cite the separate comparison lemma `lem-zl-framework-pbc-open-exchange-comparison`, whose statement supplies both the actual functor isomorphisms and the conjugacy equation for the specified exchange. Its `S` and `T` identify the source and target composite functors, not just their objects. The new step applies `thm-cbc-qbar` to `J_XF`, then uses `J(Ex_sf)=T^{-1} Ex_pbc J S`. All quotient transitions, strict-tower mates, and total-limit endpoint maps are part of the comparison assertion. The semilinear naturality clause and explicit pasting argument identify the Weil structures. The comparison lemma asserts no base-change invertibility; the separate PBC theorem still supplies that essential assertion.

E1/C4 (former Step 6): the unit fixes an arbitrary embedding, whereas `def-weil-punctual-weights`, `lem-zl-extension-by-zero-punctual` and hence `lem-zl-finite-pushforward-punctual` used an isomorphism with C. I removed all three from the proof dependencies. The replacement immersion theorem has no embedding hypothesis and supplies exactness and Frobenius-compatible stalks. The finite direct-image theorem supplies the semilinearly natural fibre formula. The finite-Weil-sections decomposition, over the residue finite field, supplies the cyclic blocks and the equality of the e-th power with local Frobenius. Steps 7-9 explicitly compute the absolute values using only multiplicativity of the original embedding. Step 10 pushes forward the original global mixed filtration. No extension of the given embedding to an isomorphism, and no replacement embedding, is chosen. The target statement is unchanged.

## Source error

In `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md`, the first paragraph claims that a scheme finite over the quasi-separated finite-type target is “in particular” a separated finite-type scheme over the field. The implication about absolute separatedness is false. Let (D_0) be the affine line with doubled origin over (k_0) and take (f_0=mathrm{id}_{D_0}). It is a finite, separated, quasi-finite finite-type morphism; (D_0) is quasi-separated and finite type, but is not separated over (k_0). Its identity finite compactification has (T_0=D_0).

The previous delivery only reported this error while relying on the theorem with the defective proof. That was insufficient, as the return states. The present proof retains the nonseparated case and resolves it by restriction along affine opens with the general compact-support exchange, then checks exactness on that covering. The doubled-origin identity now reduces on both affine charts to the identity functor, so it satisfies every hypothesis of the local calculation. The source node is outside my writable files; the report requests maintenance of its proof, but the delivered item's proof no longer depends on it.


## New node, sources and proof plan

`lem-zl-framework-pbc-open-exchange-comparison` is a comparison of two coefficient presentations and their specified transformations for arbitrary compactifiable maps with an open target square. It has no quasi-finite hypothesis and asserts neither vanishing nor weight preservation nor base-change invertibility. It is therefore an auxiliary identification, strictly different from each clause of the item. This is the substantive identification hidden by the old word "here" in Step 3; keeping it inline as an unproved transport would repeat the return. Its statement names all schemes, the compactifications, both integral categories, the coefficient-presentation equivalence, both actual compact-support constructions, both pullbacks, the whole-tower normalization and the equation of transformations. It has empty `proof`, empty `proof_deps`, null `proof_origin`, and all definition dependencies. Its blueprint ancestor is the item and its `from.place` points to the unit's first compact-support-base-change sentence.

I read the local blueprint source `sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md`, in particular its descent of the functors and their exchanges. That text proves the PBC assertion; it does not itself establish the missing comparison. The new source place expressly records this as the auxiliary comparison being made explicit. It is an agent-formulated mathematical lemma, rather than a claim that a Stacks tag states this adic comparison. The complete notes remain WANTED, as above. I read the statements of `def-pur-completed-coefficient-presentation-transport`, `lem-fd-rational-coefficient-category-comparison`, `lem-weil-compact-support-reduction-tower-functor`, `lem-sf-cbc-compact-support-composition-limit`, `lem-cbc-complete-proetale-strict-tower-realization`, `lem-cbc-adic-pullback-presentation-transport`, `lem-cbc-completed-extension-zero-comparison` and `lem-cbc-rational-compact-support-coefficient-coherence` when checking its truth and scope.

Proof plan for its later worker: use the completed-ring presentation equivalence on one common strict quotient diagram. Open completion and its quotient-tensor comparison identify the two open factors; the canonical direct-image/limit comparison identifies the proper factors. The ambient word comparison theorem has no common Tor-interval hypothesis, so none is silently added here. Its one-letter and concatenation normalizations give the endpoint comparisons on entire derived diagrams. The completed strict-tower realization states that the PBC exchange is exactly Rlim of the normalized proper mate followed by the open mate. The coefficient-presentation pullback comparison preserves the specified tensor counits and quotient transitions. Under these identifications the framework exchange is Rlim of this same ordered diagram morphism, giving the displayed S/T equation. This compares the chosen maps before taking their limit; it does not infer equality from equal reductions. Apply raw scalar localization to the integral equation. The rational category comparison and the finite-coefficient-extension coherence descend it to the common-stage categories. Naturality of the diagram maps gives semilinear naturality and iterated restriction compatibility. None of these steps requires absolute separatedness or finite Tor amplitude on every quotient. This plan is in the report, not inserted into the new node's statement as a disguised proof.

## Mathlib and duplicate searches

The original eight item searches were read in `searches.jsonl` and retained unchanged in the item. Their question is unchanged, so I did not repeat them. For the new comparison lemma I ran two distinct plain-language phrasings with LeanFinder and LeanSearch, two Loogle queries and three source greps using only `msearch.py`. All nine actual records are copied into its `mathlib_searches`, with the exact tool and query text. No service was unavailable. Loogle reported unknown identifiers (`CategoryTheory`, `Sheaf`), which is recorded in the results rather than represented as a successful theorem search. Semantic hits concern AdicCompletion of modules, sheaf pushforward adjunctions/compositors, presentations, and condensed profinite functors; none compares these two constructible adic compact-support constructions or their strict-tower exchanges. The first two broad greps reached the command's 25-hit output cap, so I also ran the focused `derivedLowerShriek|completedExchange|compactSupportComparison|compact_support` grep; its 18 hits are analytic compact-support functions only. I read Mathlib `AlgebraicGeometry/Sites/ElladicCohomology.lean`, including its definitions of ell-adic sheaves and cohomology: it has no compact-support/exchange comparison. No returned declaration is an exact match or a one-line specialization. Source searches under the supplied WeilConjectures six-functor directories found no completed declaration stating this comparison; the master is reference material only.

Before creating the new node I searched all DAG statements for framework/PBC and intrinsic/completed compact-support identifications, read each plausible comparison candidate, and ran whole-blueprint searches for `open restriction`, `compact-support exchange`, `coefficient-category comparison`, and `derived inverse limit`, as well as `ancestor sk-l-dl-general-quasifinite`. No blueprint node states this cross-presentation compact-support/exchange comparison. There is no source Stacks tag duplicated by the new node. No changes to any existing comparison node are included.

## Not duplicates

- lem-zl-framework-pbc-open-exchange-comparison vs lem-fd-rational-coefficient-category-comparison: the existing result compares categories, scalar extensions and isomorphism pullbacks; it does not compare compact-support functors or their open exchange maps. The new lemma uses those existing equivalences.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-cbc-complete-proetale-strict-tower-realization: the latter identifies a specified PBC completed exchange with its constant-tower model; it does not identify the framework coefficient category/functor and its common-stage exchange with PBC. The new statement fixes those endpoint functors and the conjugacy equation.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-sf-cbc-compact-support-composition-limit: the existing ambient word theorem compares completed operations with strict towers in constant coordinates, and expressly makes no compactification or exchange-pasting assertion. The new result compares the framework functor and its actual open exchange across coefficient presentations.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-sf-integral-compactification-system-realization: the existing theorem requires common finite cohomological/Tor intervals on every intermediate system and is formulated for semilinear expression realizations. The new comparison is on the stated bounded constructible categories without that extra reduction-Tor hypothesis, explicitly compares PBC, and includes rational/common-stage coefficient coherence.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-sf-integral-compactification-comparison-bridge: that bridge concerns composition of compact-support functors on separated schemes with uniform Tor hypotheses, not open restriction on nonseparated schemes or the specified PBC exchange.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-cbc-global-transport-chart-normalization: that statement transports finite constant coefficients between etale and pro-etale sites; the new lemma compares completed integral/framework presentations and their rational/common-stage operations.
- lem-zl-framework-pbc-open-exchange-comparison vs thm-cbc-qbar: the existing result asserts base-change invertibility for PBC; the new lemma compares constructions and transformations and asserts no invertibility of the exchange.
- lem-zl-framework-pbc-open-exchange-comparison vs lem-pur-compact-support-integral-coefficient-comparison: the existing result compares finite extensions of coefficient fields for framework compact support on a finite-Tor domain, not framework versus PBC presentations and open exchange.

`sk-l-dl-general-quasifinite` and `lem-zl-quasi-finite` remain the already imported same-statement pair recorded in `same_as`; the latter's flawed proof is not used.

## Review by Q03

I read the current chapter and unit, the main-20261015 item, its same-unit quasi-finite proof and the finite-pushforward proof in `sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md`. I also read the current common-stage base-change proof and the statement of every node cited in the ten steps, including the new statement and the definitions it uses. The earlier reading of Stacks More on Morphisms Tag 05K0 (`lemma-quasi-finite-separated-pass-through-finite`), and Etale Cohomology Tags 03QP, 03S5 and 03PU is retained as finite-level background. These finite-level statements are not substituted for the actual adic constructible-category assertions. The WANTED lecture notes are not represented as read. The new comparison is explicitly agent-formulated; its source and future proof plan are discussed above.

Steps 1-2: Zariski main theorem supplies a quasi-compact open followed by a finite map because the given target is qcqs. Finite-proper gives a compactification. Finite base change and affineness put its restriction over an affine target in the absolutely separated domain. Open base change, affine-source separatedness, finite-type Noetherianity, Noetherian open quasi-compactness, base-change preservation of separated finite type, and the affine-open basis say exactly what the retained step takes from them. The closed diagonal restricted to an open is the elementary separatedness argument. Neither the original target nor its global finite compactification is asserted separated over the field. No affine-intersection assertion is made.

Step 3: the new comparison states the actual isomorphisms b and a, the endpoint maps S and T, and the precise equation of exchanges; the quotation includes all these formulas. Noetherianity and finite dimension of every scheme needed in this supplied finite compactification follow from the cited finite-type results. The coefficient prime is invertible. The chart is quasi-compact since the target is Noetherian. This matches every scheme hypothesis of the new comparison; no Tor-amplitude condition is inferred from constructibility. I checked the direction of the equality: S maps J of the framework source to the PBC source and T maps J of the framework target to the PBC target. Thus J(Ex_sf)=T^{-1}Ex_pbc J S has the correct source and target.

Step 4: `thm-cbc-qbar` is now applied to J_XF, in its own PBC category. `thm-cbc-finite-extension` explicitly gives the relative-separatedness, Noetherian finite-dimensional, invertible-prime assumptions and naturality/pasting coherence. Invertibility transfers through the displayed equation because J is an equivalence. The new comparison's semilinear naturality and Weil clause cover the actual framework Frobenius structures. The step spells out why the two Frobenius/open pastings coincide and why composing with F's Weil arrow gives the Weil morphism equation. This repairs the previous uncited functor/map identification rather than renaming it.

Step 5: only the separated affine charts are used in `prop-functor-package` clause (3). Properness gives Rp_*=Rp_!, and the composition law gives the chart factorization. Clause (2) of `lem-zl-immersion-weil-local-behavior` supplies t-exactness and exactness on constructible Weil hearts for the actual framework Rj_!, with no embedding assumption. `lem-zl-finite-adic-direct-image` supplies t-exactness and exactness for the rational/common-stage finite Rp_* on the same separated charts. These give the heart-valued exact local functor.

Step 6: `lem-a1-constructible-pullback-t-exact` gives the exact restriction/cohomology comparison for arbitrary finite-type schemes. The final sentence of `lem-dl-a1-constructible-fibres-exact` explicitly permits checking exactness on a separated finite-type open cover of a locally finite-type ambient scheme. It applies both to 0 -> H^i -> 0 for vanishing and to the three image terms for exactness. The global output's constructible bounded domain is part of the framework compact-support definition/comparison, not obtained by pretending arbitrary pro-etale stalks are conservative. Steps 4-5 are now the local calculation referenced here.

Step 7: `sk-d-dl-general-weights` explicitly allows a field embedding and spells out the pure-quotient eigenvalue equality. `lem-kun-closed-point-field` checks that a closed point of the finite-type open is a closed point of the ambient finite-type scheme. The immersion theorem supplies the same stalk and same local Frobenius with no coefficient embedding at all. It follows directly that extension by zero preserves the input eigenvalue inequalities/equalities for the given embedding. I do not apply any clause of the old isomorphism-only weight lemmas.

Step 8: the finite-direct-image statement explicitly includes semilinear naturality and a natural finite-fibre H^0 formula. On the separated finite fibre the properness law identifies H^0 with H_c^0. `lem-a1-finite-weil-sections-decomposition`, applied over kappa(y), states the cyclic summands and e_z F^e=F_x e_z. The same-residue-field assertion of `lem-fd-weil-pullback-local-frobenius` identifies the stalk operator after inclusion of the finite fibre, which is finite by `lem-weil-pbc-finite-morphism-permanence`. The fibre Weil arrow over kappa(y) is theta^[d_y]. The local-Frobenius definition then states which degree iterates define F_y and F_x; e iterations give theta^[ed_y], and their residue degrees satisfy [kappa(x):k_0]=e[kappa(y):k_0]. A basis gives q_x=q_y^e by a bijection with kappa(y)^e, an elementary finite-vector-space count. Given a beta-eigenvector in a block, a nonzero component proves directly that beta^e is an upstairs eigenvalue; no semisimplicity is assumed. The displayed absolute-value calculation and positive root prove the inequality and its equality variant for arbitrary iota, including negative real weights. These are the unit's actual orbit calculations, not a new node restating the weight clause.

Steps 9-10: a closed point lies in some affine chart with the same residue field and local Frobenius; the chart identification is an isomorphism of Weil sheaves by Step 4. This proves the punctual assertion globally. For mixedness, the global input filtration from `sk-d-dl-general-weights` is pushed forward using the exactness proved in Step 6. The displayed short exact sequences identify successive output quotients with f_!Q_i, which Step 9 makes pure of the same weight. Zero quotients may be deleted. This is elementary filtration algebra; unrelated local mixed filtrations are never asserted to glue.

For the new node I checked B1-B9: it is statement-only, self-contained, uses single-escaped TeX, records all actual searches and blueprint ancestry, and neither duplicates the existing category comparison nor asserts the item's clauses. It explicitly excludes an implicit absolute-separatedness assumption. I tested its endpoint equation on v=id, the empty open, j=id (proper case), p=id (open case), and a nonseparated doubled-origin identity compactification. In the identity/empty cases it is the corresponding unitor/zero map. In the proper/open cases it reduces to the normalized proper/open diagram morphism. No arbitrary lifting from finite-level derived arrows or faithfulness of reductions is assumed.

I tested the item's proof on the empty source/target, zero sheaf, separated identity, doubled-origin nonseparated identity, finite inseparable map and nonreduced finite fibre. The finite-Weil decomposition requires neither reducedness nor semisimplicity. For a degree-e orbit with e>1, beta^e=alpha retains the real weight rather than multiplying it by e. The proof still uses the given embedding even if its image is a proper subfield of C; only its multiplicativity enters. All non-elementary steps have node citations with statements that supply the needed assertions, and no step exceeds 2000 characters. The comparison formerly hidden inside Step 3 is now a genuine separate statement-only node. Each citation quotation was tested as a literal substring, and every delivered proof edge was traversed for a path back to the item; none exists. Off-unit tool citations are declared in split_report.tool_uses, never in the maintainer-owned tool_uses field. No Lean or launcher/shared-project file was edited, no compiler was run, and no agents were started.

## Unfinished work

The stage-1 split is complete. The new comparison lemma is deliberately an unsplit statement for the next DAG level, as required; its proof plan and source limits are above. The separate existing `lem-zl-quasi-finite` proof discrepancy remains for its owner. The initial repair-session dry run passed at `cc537fa6c1`; it preceded the F1 artifact/source-location changes. A final dry run and delivery follow the expanded review below.


## F1 repair of returned head d219aca8d8

The return asks for the route-pivot dropped-node list, repair note, and historical comparison text inside the review snapshot; it reports no further mathematical fault and points out corrected source locations for Steps 7–9. This delivery repairs each part concretely. I have placed the exact audit inputs and historical proof text below in report.md, because the delivery command packages this report but does not package arbitrary sandbox audit files. The independent reviewer needs no Git command, live access, or file outside the delivered snapshot to read these inputs. The raw history was read using Python from the permitted read-only repository's object files, with SHA-1 validation of every object read. No git command was invoked and no repository or launcher file was written.

The retained sandbox was byte-identical as parsed JSON to returned head d219aca8d8 before this repair. I retained all ten proof texts and all their dependency lists, the auxiliary lemma, citations and the seventeen logged searches. The item still has the exact imported statement. The actual node changes are the three source locations and the split-report explanation; the report has substantive new audit evidence. This is not an unchanged re-push.

Steps 7–9 previously named the common-stage PBC proof as their source, although that file proves coefficient descent and contains no orbit-weight argument. Step 7 now cites the open-stalk paragraph (2) of the same-unit quasi-finite proof. Step 8 cites the finite-pushforward proof's explicit orbit calculation, with the arbitrary-embedding and inequality variants written in the step itself. Step 9 cites the unit's own normalized-weight proof paragraph. I read all three actual source places. These location corrections preserve the already checked weight-free lemma citations and the original embedding; they do not restore the flawed absolute-separatedness inference or the isomorphism-only weight lemmas.

## Review by Q03 — F1 supplement

I reopened the item, auxiliary statement, chapter, unit, both weight proofs, and all 24 directly cited proof statements. All 32 entries of citations.json remain literal substrings of the cited statements. The two category presentations remain distinct until the auxiliary lemma supplies the functor and arrow comparison. On each affine target chart, every separated-scheme hypothesis of the immersion, finite-image and functor-package statements holds. The given global target remains merely quasi-separated. The eigenvector-component calculation in Step 8 uses the finite-Weil decomposition's explicit equality of operators, and uses only multiplicativity of the given embedding. Steps 9–10 use the original global filtration and exactness already established, with no gluing of mixed filtrations. The maximum proof-step text length is 1654 characters; none conceals a new long-step lemma.

For the route audit I traversed both statement and proof edges from every direct item dependency and from the new auxiliary node. The full union contains 14134 nodes and has empty intersection with the 1346-entry manifest below. In particular the new comparison's strict quotient diagrams mean ordinary complexes of module systems; Rlim is the ordinary right derived limit, coefficient tensors use K-flat resolutions, and the proper/open transformations are actual ordinary adjunction-mate words before taking Rlim. The new statement neither requires rectification of a homotopy-coherent diagram nor infers equality of arrows from equality of evaluations. It asserts no enhanced right adjoint. The supplied finite compactification meets the repaired finite-level PBC theorem's alternative “compactification given”, and the target also meets its qcqs alternative. Thus no Zariski enhanced-descent extension is used for a non-qcqs base.

There is no item-specific repair note at the audited main ref. The eight resolved ordinary-route notes in its transitive closure are reproduced exactly below, rather than treating absence of an item note as absence of applicable guidance. Their mathematical statement/proof fields at the returned head and the inspected current snapshot are unchanged: the resolved ordinary interfaces had already been installed before this return. The remaining historical notes in the closure have state withdrawn, no active route instruction, and are listed in the audit output for clarity. Their mere existence is not a new return or a reason to change this unit. Historical text and forbidden ids below are audit exhibits only, never additional mathematical dependencies.

I rechecked the empty open, empty scheme, zero sheaf, proper/open/identity comparison cases, and the doubled-origin identity. The doubled-origin case is permitted globally and calculated on its two separated affine charts. Finite inseparable or nonreduced fibres still have the finite stalk decomposition without a semisimplicity hypothesis. No new node or search was needed for this F1 repair. All previous source requests, attachment limits, and the source-error counterexample remain in this report.

## F1 exact audit provenance

The historical refs read for this repair were:

```json
{
 "returned": "d219aca8d82c0187d60abeacc938997f45cecd5f",
 "main": "78c79870a12cdd143a73794dc4fec0fc145ecc7b",
 "earlier-return": "c1dde7e4a9e8d436cf26bec0aa4a5671749a61ec",
 "reader": "read-only Python zlib/pack reader, SHA-1 validated; no git command"
}
```

The current main item is still imported with one unclassified sketch step; its statement agrees byte-for-byte with the returned and repaired item statements. Its proof is quoted below. The main-ref manifest and active repair-note bytes were recovered from that immutable tree. The dependency closure was traversed using the available shared DAG working snapshot plus the sandbox overlay; it is a current-snapshot audit, not a claim to reconstruct every historical DAG node from the sparse local object store. For each resolved interface the actual returned object was available and its six mathematical fields were compared with that snapshot. The delivery tool performs its own fresh-main overlay and server preflight after this review.

Manifest SHA-256: `7dd4fe135c9ca7a82a5cf6e465aed469fb3b6b03726377b603953abee7baeacf`.

## F1 exact dropped-node list

Exact contents of coord/route-pivot-dropped.txt at the main ref named above:

```text
# Route pivot (decision of the human, 2026-10-18): nodes of the dropped infinity/dg/model-category machinery, the nodes
# only it reached, and the Zariski-gluing branch (lem-cbc-etale-local-compact-support-extension, lem-cbc-global-transport-
# chart-normalization). A reachable node must not cite them (svc.py route_pivot_note, postcheck). Not touched by note
# cleanups; one id per line.
def-cbc-bounded-representable-hypercover
def-cbc-derived-hypersheaf-presentation
def-cbc-enhanced-cartesian-fibration
def-cbc-enhanced-diagrams-cones
def-cbc-enhanced-strong-saturation
def-cbc-local-simplicial-presheaf-maps
def-coef-algebroid-graph
def-coef-algebroid-terminal-space-pairing
def-coef-augmented-vertex-diagrams
def-coef-bounded-filtered-subcategory-system
def-coef-brown-reedy-diagrams
def-coef-categorical-pattern-fibrancy
def-coef-coherent-adjunction-data
def-coef-coherent-bar-word-data
def-coef-coherent-localization-interface
def-coef-coherent-monad-modules
def-coef-coherent-nerve-infrastructure
def-coef-coherent-pullback-comparison
def-coef-colored-operator-systems
def-coef-complete-algebroid
def-coef-continuous-space-presheaf
def-coef-cosimplicial-product-total
def-coef-dg-derived-enrichment
def-coef-dg-quillen-diagram
def-coef-discrete-fibration
def-coef-enriched-coend
def-coef-enriched-interval-strings
def-coef-face-cocone-evaluation
def-coef-finite-limits-square-cones
def-coef-good-cellular-tree
def-coef-graded-linear-category
def-coef-homotopy-segal-space
def-coef-infinity-category-of-spaces
def-coef-infinity-fibrations
def-coef-infinity-left-anodyne
def-coef-infinity-marked-coanodyne
def-coef-infinity-presheaf-yoneda
def-coef-infinity-relative-cone
def-coef-infinity-relative-join
def-coef-infinity-right-anodyne
def-coef-injective-homotopy-limit
def-coef-integral-derived-coefficients
def-coef-iterated-span-completion-rule
def-coef-join-slice
def-coef-left-module-operadic-encoding
def-coef-lm-pointed-projection
def-coef-mapping-simplex-functor
def-coef-mixed-grothendieck-construction
def-coef-module-operad-lm-zero
def-coef-monoidal-infinity-category
def-coef-nonsymmetric-monoid-axiom
def-coef-operadic-correspondence
def-coef-operadic-typec-incidence-data
def-coef-operadic-weak-approximation
def-coef-ordered-join
def-coef-oriented-tree-subtree-zigzags
def-coef-presentable-infinity-category
def-coef-quillen-derived-diagram
def-coef-rectified-space-limit
def-coef-relative-symmetric-operadic-algebras
def-coef-segal-interval-cover
def-coef-segal-presheaf-localization
def-coef-segal-space
def-coef-simple-presheaf-inner-anodyne
def-coef-simplicial-groupoid
def-coef-simplicial-hammock-pair
def-coef-simplicial-model-realization
def-coef-simplicial-multicategory
def-coef-simplicial-realization-map
def-coef-simplicial-tensor-cotensor
def-coef-space-base-change
def-coef-space-tower-homotopy-limit
def-coef-strict-quillen-sections
def-coef-symmetric-operadic-approximation
def-coef-symmetric-operadic-family
def-coef-tensored-algebroid-presentation
def-coef-universally-localizing-simplicial-map
def-coef-zigzag-homotopy-calculus
lem-cbc-bounded-below-hypersheaf-model
lem-cbc-cartesian-mapping-simplex-comparison
lem-cbc-cocartesian-section-currying
lem-cbc-cocartesian-sections-limit
lem-cbc-cofiltered-coherent-equivalence-diagrams
lem-cbc-coherent-cartesian-postcomposition
lem-cbc-coherent-square-comparison-data
lem-cbc-cosimplicial-complex-holim
lem-cbc-cw-source-homotopy-lift
lem-cbc-dense-hypercover-set
lem-cbc-dense-hypersheaf-comparison
lem-cbc-dg-presheaf-model-localizations
lem-cbc-disk-lifting-surjective
lem-cbc-dold-kan-homology
lem-cbc-dold-kan-hypercover-quillen
lem-cbc-enhanced-equivalence-square-mates
lem-cbc-enhanced-functor-cone-calculus
lem-cbc-enhanced-relative-exponential
lem-cbc-equivalence-outer-horn-filling
lem-cbc-etale-local-compact-support-extension
lem-cbc-filtered-nerve-weak-contractibility
lem-cbc-framed-horn-criterion
lem-cbc-framed-localizing-cofibrations
lem-cbc-general-bousfield-localization
lem-cbc-global-transport-chart-normalization
lem-cbc-grothendieck-coherent-end
lem-cbc-grothendieck-hyperdescent-local-refinement
lem-cbc-grothendieck-hypersheaf-sections
lem-cbc-grothendieck-presheaf-coherent-straightening
lem-cbc-hom-functor-composition-coherence
lem-cbc-homotopy-local-equivalences-accessible
lem-cbc-hypercover-cotensor-local-acyclic-fibration
lem-cbc-hypercover-localization-generation
lem-cbc-hypercover-relative-lifting
lem-cbc-hyperdescent-local-orthogonality
lem-cbc-initial-prism-horn-filtration
lem-cbc-inner-fibration-equivalence-outer-horn-lift
lem-cbc-internal-hom-fibration-corner-map
lem-cbc-internal-hom-quasicategory
lem-cbc-invertible-prism-extension
lem-cbc-kan-contracted-base-section-extension
lem-cbc-kan-fibration-fiber-criterion
lem-cbc-kan-functor-space-kan
lem-cbc-kan-mapping-homotopy-invariance
lem-cbc-kan-realization-mapping-classes
lem-cbc-kan-relative-realization-lift
lem-cbc-kan-whitehead-inverse
lem-cbc-kinjective-derived-mapping-complex
lem-cbc-left-fibration-equivalence-lift
lem-cbc-left-proper-derived-cell-colimits
lem-cbc-local-acyclic-matching-cover-criterion
lem-cbc-local-acyclic-matching-generalized-cover
lem-cbc-local-weak-equivalence-homotopy-lifting
lem-cbc-mapping-simplex-initial-horn-pushout
lem-cbc-mapping-simplex-universal-equivalence
lem-cbc-marked-homotopy-precomposition
lem-cbc-marked-mapping-simplex-descent
lem-cbc-marked-relative-nerve-quillen
lem-cbc-nonfree-chain-completions
lem-cbc-normalized-horn-disk
lem-cbc-normalized-simplex-chain-diagonal
lem-cbc-opposite-interval-internal-hom
lem-cbc-opposite-sset-lifting-properties
lem-cbc-pinched-cube-augmentation-uniqueness
lem-cbc-presheaf-dg-function-complex
lem-cbc-projective-cochain-dg-compatibility
lem-cbc-projective-cochain-suspension
lem-cbc-realization-compact-finite-support
lem-cbc-realization-cw-subcomplex
lem-cbc-realization-singular-unit-weak
lem-cbc-realization-weak-equivalence
lem-cbc-relative-coslice-left-fibration
lem-cbc-relative-nerve-cone-left-comparison
lem-cbc-relative-nerve-projective-cofibrancy
lem-cbc-right-fibration-morphism-space
lem-cbc-right-fibration-space-fiber
lem-cbc-right-resolution-mapping-criterion
lem-cbc-simplexwise-categorical-base-change
lem-cbc-simplicial-composition-spine
lem-cbc-simplicial-groupoid-localization
lem-cbc-simplicial-homotopy-equivalence-weak
lem-cbc-simplicial-hypercover-fibration-test
lem-cbc-simplicial-module-model
lem-cbc-simplicial-module-moore-homotopy
lem-cbc-spine-inner-anodyne
lem-cbc-standard-simplex-mapping-contractible
lem-cbc-strict-presentation-transport-representation
lem-cbc-terminal-boundary-extension
lem-cbc-weak-equivalence-relative-disk-extension
lem-cbc-whitehead-cw-homotopy-inverse
lem-cbc-zariski-enhanced-derived-descent
lem-coef-accessible-arrow-inverse-image
lem-coef-accessible-compact-cocones
lem-coef-accessible-compact-slice-density
lem-coef-accessible-completeness-characterization
lem-coef-accessible-diagram-presentations
lem-coef-accessible-full-inverse-image
lem-coef-accessible-functor-presentability-ranks
lem-coef-accessible-ind-colimit-extension
lem-coef-accessible-infinity-pullback
lem-coef-accessible-infinity-rank-calculus
lem-coef-accessible-intersection-generators
lem-coef-accessible-localization-small-generators
lem-coef-accessible-monad-presentability
lem-coef-accessible-pie-closure
lem-coef-accessible-pullback-filtered-colimit
lem-coef-accessible-small-object-factorization
lem-coef-accessible-subdiagram-criterion
lem-coef-accessible-system-ranks
lem-coef-active-concatenation-block-projections
lem-coef-active-operad-cocartesian-concatenation
lem-coef-active-operad-envelope-cocartesian
lem-coef-adjunction-block-run-collapse
lem-coef-adjunction-fillable-parent-bijection
lem-coef-adjunction-free-simplicial-resolution
lem-coef-adjunction-nondistinguished-face-rank
lem-coef-adjunction-square-lifts
lem-coef-adjunction-squiggle-normal-form
lem-coef-adjunction-two-block-splicing
lem-coef-algebroid-bilinear-colimits
lem-coef-algebroid-categorical-homotopy
lem-coef-algebroid-cocontinuous-base-change
lem-coef-algebroid-completion
lem-coef-algebroid-cotensor-nerve-exchange
lem-coef-algebroid-equivalence-arrow-descent
lem-coef-algebroid-equivalence-nerve
lem-coef-algebroid-external-product
lem-coef-algebroid-ff-simplicial-realization
lem-coef-algebroid-object-space-fibration
lem-coef-algebroid-presentability
lem-coef-algebroid-segal-localization-model
lem-coef-algebroid-universe-embeddings
lem-coef-all-cofibrant-left-proper
lem-coef-all-cofibrant-mapping-detection
lem-coef-all-cofibrant-simplicial-recognition
lem-coef-arrow-endomorphism-planar-operad
lem-coef-arrow-prism-collage-inner-anodyne
lem-coef-arrow-target-cartesian-pullbacks
lem-coef-associative-algebra-diagram-cell-filtration
lem-coef-associative-algebra-model-transfer
lem-coef-associative-algebra-sifted-localization
lem-coef-associative-reflective-localization
lem-coef-associative-word-filtration
lem-coef-augmented-vertex-cone-recognition
lem-coef-bifibrant-comparison-common-replacement
lem-coef-bimodule-word-path-approximation
lem-coef-bipartite-cocartesian-simplex-extension
lem-coef-bisimplicial-diagonal-equivalence
lem-coef-bisimplicial-diagonal-space-colimit
lem-coef-bisimplicial-reedy-division-calculus
lem-coef-boundary-lifting-quasicategory-equivalence
lem-coef-boundary-proper-face-limit
lem-coef-bousfield-kan-comparison-calculus
lem-coef-bousfield-local-fibrations
lem-coef-bousfield-quillen-descent
lem-coef-bousfield-smith-bounded-generation
lem-coef-brown-cocone-equivalence-transport
lem-coef-brown-fibrant-localization-pullbacks
lem-coef-brown-finite-direct-rectification
lem-coef-brown-left-fractions
lem-coef-brown-localization-products
lem-coef-brown-reedy-fibrant-replacement
lem-coef-brown-right-exact-extension
lem-coef-brown-slice-fraction-calculus
lem-coef-brown-span-coherent-rectification
lem-coef-canonical-hocolim-degree-reduction
lem-coef-cardinal-small-object-factorization
lem-coef-cartesian-associative-segal-comparison
lem-coef-cartesian-base-equivalence-invariance
lem-coef-cartesian-colimit-descent-criterion
lem-coef-cartesian-colimit-localization
lem-coef-cartesian-comma-normalization
lem-coef-cartesian-cone-fiber-comparison
lem-coef-cartesian-core-right-fibration
lem-coef-cartesian-envelope-cocartesian-criterion
lem-coef-cartesian-envelope-product-diagram-recognition
lem-coef-cartesian-grothendieck-colimit-formula
lem-coef-cartesian-left-adjoint-transport
lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence
lem-coef-cartesian-mapping-simplex-presentation
lem-coef-cartesian-mapping-simplex-prism-extension
lem-coef-cartesian-maps-presheaf-extension
lem-coef-cartesian-marked-lift-generation
lem-coef-cartesian-marked-slice-restriction
lem-coef-cartesian-matrix-model
lem-coef-cartesian-monoidal-straightening
lem-coef-cartesian-monoidal-structure-uniqueness
lem-coef-cartesian-operadic-envelope
lem-coef-cartesian-simplex-inverse-extension
lem-coef-cartesian-terminal-twisted-resolution
lem-coef-cat-infinity-colimits-cartesian-closure
lem-coef-cat-infinity-filtered-finite-calculus
lem-coef-cat-infinity-opposite-involution
lem-coef-categorical-algebra-free-monad
lem-coef-categorical-equivalences-small-generation
lem-coef-categorical-pattern-model-calculus
lem-coef-cellular-tree-presentable-approximations
lem-coef-cellular-weight-coherent-transfer
lem-coef-chain-interval-tensor-cylinder
lem-coef-chunk-bifibrant-localization
lem-coef-chunk-localized-evaluation-exponential
lem-coef-closed-self-enrichment-base-change
lem-coef-coarse-nerve-gluing
lem-coef-cocartesian-categorical-base-change
lem-coef-cocartesian-cone-limit-section-test
lem-coef-cocartesian-full-restriction
lem-coef-cocartesian-horn-completion-comparison
lem-coef-cocartesian-joyal-fibration
lem-coef-cocartesian-local-global
lem-coef-cocartesian-prescribed-cone-colimit-lifting
lem-coef-cocartesian-relative-cylinder-extension
lem-coef-cocartesian-relative-right-adjoint
lem-coef-cocartesian-right-kan-extension-simplex-powers
lem-coef-cocartesian-section-colimits
lem-coef-cocartesian-straightening
lem-coef-cocartesian-straightening-universe-change
lem-coef-cocartesian-three-horn-face-conservation
lem-coef-cocomplete-cofibration-localization
lem-coef-cocomplete-monoidal-tensor
lem-coef-cocontinuous-localization-factorization
lem-coef-cofibrant-completion-nerve-equivalence
lem-coef-cofibrant-homotopy-groupoid-completion
lem-coef-cofibrant-inclusion-coherent-localization
lem-coef-cofibrant-localization-diagonal-nerve
lem-coef-cofibrant-simplicial-inversion
lem-coef-cofibrant-subset-colimit-decomposition
lem-coef-cofibration-local-mapping-test
lem-coef-cofinal-natural-equivalence-invariance
lem-coef-cofinal-relative-join-slice-restriction
lem-coef-coherent-diagram-coyoneda
lem-coef-coherent-diagram-universe-naturality
lem-coef-coherent-end-twisted-arrow-formula
lem-coef-coherent-fixed-vertex-cofibrations
lem-coef-coherent-inner-anodyne-equivalences
lem-coef-coherent-module-section-model
lem-coef-coherent-nerve-comparison
lem-coef-coherent-nerve-pinched-adjunction
lem-coef-coherent-nerve-relative-cube-comparison
lem-coef-coherent-prism-pinch-identity
lem-coef-coherent-realization-bead-normal-form
lem-coef-coherent-realization-relative-cells
lem-coef-coherent-row-colimit-comparison
lem-coef-coherent-vertex-equivalence-lifts
lem-coef-coherent-weight-limit-recognition
lem-coef-coinitial-monomorphism-left-anodyne
lem-coef-colimit-cocone-transport-equivalence
lem-coef-colimit-subdiagram-approximation
lem-coef-collage-crossing-transformations
lem-coef-colored-operation-section-reconstruction
lem-coef-combinatorial-bounded-resolutions
lem-coef-combinatorial-cofibrant-density
lem-coef-combinatorial-injective-diagram-model
lem-coef-combinatorial-localization-presentability
lem-coef-combinatorial-presheaf-presentation
lem-coef-common-chunk-filtered-approximation
lem-coef-compact-closed-t1-chain
lem-coef-compact-diagram-cocone-transport
lem-coef-compact-model-pr-duality
lem-coef-compact-presentation-functor-refinement
lem-coef-compact-pushout-retract-descent
lem-coef-compact-relative-cocone-factorization
lem-coef-compact-small-colimits
lem-coef-complete-segal-dk-levelwise
lem-coef-complete-segal-path-fiber-comparison
lem-coef-complete-segal-quasicategory-comparison
lem-coef-complete-segal-walking-isomorphism
lem-coef-composable-bimodule-operad-segal
lem-coef-cone-apex-cocone-space-comparison
lem-coef-cone-boundary-projective-cells
lem-coef-cone-equivalence-saturation
lem-coef-cone-presheaf-adjunction
lem-coef-cone-sorted-theory-identification
lem-coef-cone-straightening-coherent-evaluation
lem-coef-cone-triangle-mapping-square
lem-coef-cone-unit-weighted-evaluation
lem-coef-constant-diagram-mapping-limit
lem-coef-contractible-factor-universal-localization
lem-coef-contractible-join-right-anodyne
lem-coef-contractible-split-inclusion-saturation
lem-coef-contraction-word-bar-faces
lem-coef-contravariant-fibrations-between-right-fibrations
lem-coef-contravariant-slice-model
lem-coef-corepresented-equivalence
lem-coef-cosimplicial-frame-mapping
lem-coef-cosimplicial-presheaf-counit
lem-coef-cotorsion-orthogonality-calculus
lem-coef-counit-cone-boundary-extension
lem-coef-countable-equivalence-witness
lem-coef-countable-sphere-homotopy-classes
lem-coef-covariant-derived-replacement-base-change
lem-coef-cube-relation-realization
lem-coef-cubical-open-box-pair
lem-coef-cut-chain-forest-compatibility
lem-coef-day-cocone-relations-compatible
lem-coef-day-model-yoneda-strong-monoidal
lem-coef-day-relative-exponential-model
lem-coef-decomposition-local-colimit-cocones
lem-coef-decomposition-simplex-attachment
lem-coef-decomposition-simplex-lift-right-anodyne
lem-coef-degreewise-cartesian-pullback-cat-infinity
lem-coef-derived-enriched-yoneda
lem-coef-derived-restriction-bifibrant-nerve-equivalence
lem-coef-derived-restriction-rectification
lem-coef-derived-space-module-coyoneda
lem-coef-dg-bifunctor-cofibrancy-fibrancy
lem-coef-dg-derived-quillen-calculus
lem-coef-dg-enrichment-rectification
lem-coef-dg-filtered-quasi-iso
lem-coef-dg-finite-twisted-extension
lem-coef-dg-free-cell-mapping-fibre
lem-coef-dg-mate-pasting
lem-coef-dg-mate-transpose
lem-coef-dg-model-homotopy-colimits
lem-coef-dg-model-mapping-comparison
lem-coef-dg-model-underlying-localization
lem-coef-dg-module-arrow-category-comparison
lem-coef-dg-module-base-change
lem-coef-dg-module-cone-triangulation
lem-coef-dg-module-diagram-classification
lem-coef-dg-module-projective-resolution
lem-coef-dg-module-semi-free-replacement
lem-coef-dg-module-tensor-currying
lem-coef-dg-monoidal-unit-image
lem-coef-dg-product-localization
lem-coef-dg-quasifunctor-invariance
lem-coef-dg-quillen-enriched-adjunction-descent
lem-coef-dg-quotient-hom-cone
lem-coef-dg-resolution-square-projection
lem-coef-dg-semi-free-cofibrant
lem-coef-dg-semi-free-homotopically-projective
lem-coef-dg-two-sided-bar-derived-tensor
lem-coef-dgcat-bimodule-mapping-space
lem-coef-dgcat-cell-comparison-functors
lem-coef-dgcat-cone-word-normal-form
lem-coef-dgcat-equivalence-cell-calculus
lem-coef-dgcat-finite-limit-sketch-signature
lem-coef-dgcat-formal-cone-enlargement
lem-coef-dgcat-free-cell-calculus
lem-coef-dgcat-model-structure
lem-coef-dgcat-sketch-model-identification
lem-coef-dgfunctor-coherent-transport
lem-coef-dgfunctor-rectified-model-comparison
lem-coef-dgfunctor-small-model
lem-coef-diagonal-coherent-nerve-comparison
lem-coef-diagram-cellular-compatible-slices
lem-coef-diagram-compact-pushout-descent
lem-coef-dinatural-section-evaluation
lem-coef-direct-wfs-extension
lem-coef-directed-algebroid-extreme-hom-pushout
lem-coef-directed-cover-colimit-assembly
lem-coef-directed-cover-mixed-subset-cells
lem-coef-directed-decomposition-right-anodyne
lem-coef-directed-enriched-amalgamation
lem-coef-directed-three-face-mapping-pushout
lem-coef-discrete-base-cocartesian-recognition
lem-coef-discrete-inner-cell-transfer
lem-coef-discrete-weight-coherent-cocones
lem-coef-dk-cofibrant-localization-comparison
lem-coef-dk-normalized-presentation-comparisons
lem-coef-dk-weak-exponential-limit-criterion
lem-coef-double-cylinder-weak-equivalence-gluing
lem-coef-double-mapping-cylinder-space-pushout
lem-coef-dugger-cardinal-choice
lem-coef-dugger-homotopically-surjective-map
lem-coef-dugger-localization-criterion
lem-coef-edge-homotopy-quotient-calculus
lem-coef-edge-inverting-anodyne-extension
lem-coef-endpoint-fixed-inner-horn-refinement
lem-coef-enhanced-localization-universal
lem-coef-enriched-bar-projective-replacement
lem-coef-enriched-category-tensor-calculus
lem-coef-enriched-coend-homotopy-invariance
lem-coef-enriched-coherent-adjunction-extension
lem-coef-enriched-completion-localization
lem-coef-enriched-cotensor-mapping-objects
lem-coef-enriched-diagram-homotopy-descent
lem-coef-enriched-diagram-rectification
lem-coef-enriched-evaluation-replacement-coherence
lem-coef-enriched-exponential-nerve-criterion
lem-coef-enriched-fibre-assembly
lem-coef-enriched-fixed-set-model
lem-coef-enriched-functorial-factorizations
lem-coef-enriched-hom-twisted-arrow-comparison
lem-coef-enriched-homotopy-localization
lem-coef-enriched-kan-diagram-weak-equivalence
lem-coef-enriched-mapping-cylinder-localization
lem-coef-enriched-marked-realization
lem-coef-enriched-nerve-transformation
lem-coef-enriched-presheaf-rectification
lem-coef-enriched-projective-diagram-model
lem-coef-enriched-simplicial-presentation
lem-coef-enriched-small-products
lem-coef-enriched-yoneda-evaluation
lem-coef-enrichment-change-adjunction
lem-coef-equifibered-bisimplicial-diagonal
lem-coef-equivalence-over-gaunt-nerve
lem-coef-ex-comparison-weak-equivalence
lem-coef-ex-infinity-finite-products
lem-coef-exact-flat-complex-set-cogeneration
lem-coef-exponential-dependent-product-representation
lem-coef-extreme-bimodule-attachment
lem-coef-face-cocone-evaluation-simplicial
lem-coef-face-cocone-splitting-refinement
lem-coef-fiberwise-arrow-target-cocartesian
lem-coef-fibrant-localized-comma-final
lem-coef-fibrant-pattern-homotopy-inverse
lem-coef-fibrant-pullback-mapping-invariance
lem-coef-fibrant-subcategory-localization
lem-coef-fibration-straightening-space-restriction
lem-coef-filtered-cocartesian-edge-persistence
lem-coef-filtered-cocartesian-section-cofinality
lem-coef-filtered-colimit-cardinal-regrouping
lem-coef-filtered-colimit-weak-equivalences
lem-coef-filtered-fiber-small-cone-lifting
lem-coef-filtered-finite-relative-cone-persistence
lem-coef-filtered-inner-horn-factorization
lem-coef-filtered-operadic-unstraightening
lem-coef-filtered-poset-cone-test
lem-coef-filtered-presentation-common-refinement
lem-coef-final-face-edge-horn-filtration
lem-coef-final-square-full-faithfulness
lem-coef-finite-colimit-approximation
lem-coef-finite-coproduct-regrouping
lem-coef-finite-core-fiber-contraction
lem-coef-finite-embedded-simplex-resolution
lem-coef-finite-inverse-tetrahedron
lem-coef-finite-limit-model-presentability
lem-coef-finite-limit-sketch-models
lem-coef-finite-marked-fibrancy-criterion
lem-coef-finite-pattern-universe-comparison
lem-coef-finite-reedy-localization
lem-coef-finite-relative-lifting-recognition
lem-coef-finite-simplicial-top-simplex-removal
lem-coef-fixed-cylinder-fibrant-target-detection
lem-coef-fixed-hammock-graph-homotopy-invariance
lem-coef-fixed-object-dg-free-model
lem-coef-fixed-object-enriched-rectification
lem-coef-fixed-object-free-arrow-adjunction
lem-coef-fixed-object-scat-bar-reordering
lem-coef-fixed-object-scat-left-proper
lem-coef-fixed-object-simplicial-free-calculus
lem-coef-fixed-object-simplicial-mapping-calculus
lem-coef-fixed-object-simplicial-sm7-free-cell
lem-coef-flat-complex-cotorsion-pairs
lem-coef-flexible-weight-enriched-lift
lem-coef-frame-bisimplicial-span
lem-coef-frame-hammock-action-naturality
lem-coef-frame-pushout-product
lem-coef-frame-source-kan-fibration
lem-coef-framed-projective-diagram-resolution
lem-coef-free-bar-cell-filtration
lem-coef-free-category-graph-nerve
lem-coef-free-category-groupoid-nerve
lem-coef-free-diagram-homotopy-density
lem-coef-free-enriched-edge-square-presentation
lem-coef-free-factor-category-normal-form
lem-coef-free-factor-hammock-comparison
lem-coef-free-factor-hammock-pushout
lem-coef-free-factor-hammock-universal-cover-reduction
lem-coef-free-module-orbit-cell-filtration
lem-coef-free-operadic-active-slice-formula
lem-coef-free-product-nerve-gluing
lem-coef-free-resolution-coproduct-augmentation
lem-coef-full-subcategory-kan-trivial-restriction
lem-coef-functor-coend-homotopy-prism
lem-coef-functor-spine-tower-mapping-descent
lem-coef-gapped-face-inner-horn-presentation
lem-coef-generalized-active-extension-criterion
lem-coef-generalized-cartesian-product-cones
lem-coef-generalized-operad-pattern-fibered
lem-coef-generalized-operadic-fibration-replacement
lem-coef-generalized-operadic-monadicity
lem-coef-generating-set-cotorsion-smallness
lem-coef-ghn-ind-presheaf-cartesian-realization
lem-coef-good-subset-enlargement
lem-coef-good-tree-idempotent-enlargement
lem-coef-graph-product-model
lem-coef-grothendieck-aspherical-base-change
lem-coef-grothendieck-classifier-localization
lem-coef-grothendieck-fibre-localization
lem-coef-groupoid-active-operation-equivalence
lem-coef-groupoidal-cofibrant-nerve-detection
lem-coef-hammock-components-localization
lem-coef-hammock-graph-colimit-presentation
lem-coef-hammock-infinity-localization
lem-coef-hammock-inverted-arrow-actions
lem-coef-hammock-pair-homotopy-invariance
lem-coef-hammock-reduction-diamond
lem-coef-hereditary-cotorsion-complex-lift
lem-coef-hocolim-reindexing-zigzags
lem-coef-hocolim-value-diagram-naturality
lem-coef-homotopy-adjunction-coherent-witnesses
lem-coef-homotopy-category-binary-products
lem-coef-homotopy-category-nerve-adjunction
lem-coef-homotopy-category-triangle-calculus
lem-coef-homotopy-equivalence-weak
lem-coef-homotopy-fractions-hammock-comparison
lem-coef-homotopy-fractions-square-criterion
lem-coef-homotopy-groups-basepoint-change
lem-coef-horn-boundary-cylinder-homeomorphism
lem-coef-horn-completion-point-colimit
lem-coef-ind-finite-poset-realization
lem-coef-ind-kappa-extension
lem-coef-ind-kappa-presentability
lem-coef-ind-presheaf-fibration-accessibility
lem-coef-ind-presheaf-small-locality-generators
lem-coef-ind-right-adjoint-coherent
lem-coef-inert-color-coslice-components
lem-coef-inert-marked-restriction-fibration
lem-coef-inert-operad-color-reconstruction
lem-coef-inert-output-relative-limit
lem-coef-inert-projection-square-fibres
lem-coef-inert-relative-tuple-cone
lem-coef-infinite-cardinal-square-power
lem-coef-infinite-cardinal-successor-regular
lem-coef-infinity-absolute-terminal-relative-colimit
lem-coef-infinity-adjunction-mapping-equivalence
lem-coef-infinity-anodyne-cocones
lem-coef-infinity-arrow-join-geometry
lem-coef-infinity-arrow-morphism-square
lem-coef-infinity-arrow-source-fibers
lem-coef-infinity-arrow-target-right-fibration
lem-coef-infinity-bicartesian-interval-adjunction
lem-coef-infinity-blunt-join-comparison
lem-coef-infinity-blunt-sharp-join-equivalence
lem-coef-infinity-boundary-extension-small-classes
lem-coef-infinity-bounded-colimit-presentation
lem-coef-infinity-cartesian-edge-transitivity
lem-coef-infinity-cartesian-fibration-pullback
lem-coef-infinity-cartesian-initial-boundary-lift
lem-coef-infinity-cartesian-mapping-criterion
lem-coef-infinity-cartesian-mapping-fiber
lem-coef-infinity-cellular-natural-equivalence
lem-coef-infinity-cocartesian-arrow-projection
lem-coef-infinity-cocartesian-base-restriction
lem-coef-infinity-cocartesian-composition-initiality
lem-coef-infinity-cocartesian-equivalence-lift
lem-coef-infinity-cocartesian-image-criterion
lem-coef-infinity-cocartesian-inner-horn-comparison
lem-coef-infinity-cocartesian-mapping-criterion
lem-coef-infinity-cocartesian-prism-comparison
lem-coef-infinity-cocartesian-transport-square
lem-coef-infinity-cocone-opposite-join-functor
lem-coef-infinity-cocone-restriction-initial
lem-coef-infinity-cofinal-colimit-restriction
lem-coef-infinity-cofinal-comma-criterion
lem-coef-infinity-cofinal-common-image
lem-coef-infinity-cofinal-coslice-calculus
lem-coef-infinity-cofinal-kappa-poset
lem-coef-infinity-cofinal-mono-right-anodyne
lem-coef-infinity-cofinality-space-test
lem-coef-infinity-colimit-gluing
lem-coef-infinity-comma-corepresentable-colimit
lem-coef-infinity-comma-equivalence-invariance
lem-coef-infinity-comma-mapping-pullback
lem-coef-infinity-common-compactness-rank
lem-coef-infinity-compact-approximation
lem-coef-infinity-compact-generated-filtered-hull
lem-coef-infinity-compact-stage-factorization
lem-coef-infinity-cone-mono-right-anodyne
lem-coef-infinity-constant-source-section-comparison
lem-coef-infinity-continuous-presheaf-representability
lem-coef-infinity-core-cylinder-restriction
lem-coef-infinity-core-kan-fibration
lem-coef-infinity-coslice-colimit-formula
lem-coef-infinity-directed-cone-cover
lem-coef-infinity-directed-union-local-colimits
lem-coef-infinity-edge-pullback-mapping-fiber
lem-coef-infinity-equivalence-anodyne-factorization
lem-coef-infinity-equivalence-arrow-path-object
lem-coef-infinity-equivalence-cancellation
lem-coef-infinity-equivalence-of-cospan-limits
lem-coef-infinity-equivalence-preserves-cocartesian-edges
lem-coef-infinity-equivalence-prism-extension
lem-coef-infinity-equivalence-section-restriction
lem-coef-infinity-essentially-small-cocones
lem-coef-infinity-fiber-cocone-simplex-extension
lem-coef-infinity-fiber-colimit-collage
lem-coef-infinity-fiber-relative-colimit-criterion
lem-coef-infinity-fiberwise-relative-join
lem-coef-infinity-filtered-cocone-apex-cofinal
lem-coef-infinity-filtered-cofinal-pullback
lem-coef-infinity-final-index-cocone-criterion
lem-coef-infinity-final-index-colimit
lem-coef-infinity-finite-coproduct-envelope
lem-coef-infinity-finite-poset-kan-extension
lem-coef-infinity-finite-shape-generation
lem-coef-infinity-fixed-boundary-functor-kan
lem-coef-infinity-fixed-cocone-opposite-limit
lem-coef-infinity-fixed-edge-prism-coherence
lem-coef-infinity-free-module-bar
lem-coef-infinity-full-essential-image
lem-coef-infinity-functor-pushout
lem-coef-infinity-grothendieck-limits-colimits
lem-coef-infinity-hom-bifunctor-functoriality
lem-coef-infinity-homotopy-precomp-equivalence
lem-coef-infinity-homotopy-pullback-pasting
lem-coef-infinity-initial-evaluation-trivial-fibration
lem-coef-infinity-inner-fibration-corner
lem-coef-infinity-inner-horn-collapse-filtration
lem-coef-infinity-inner-mapping-fiber
lem-coef-infinity-intermediate-presheaf-kan
lem-coef-infinity-isofibration-base-change
lem-coef-infinity-isofibration-exponentiation
lem-coef-infinity-isofibration-pullback-equivalence
lem-coef-infinity-isofibration-pullback-limit
lem-coef-infinity-iterated-slice-mapping
lem-coef-infinity-join-cocone-associativity
lem-coef-infinity-join-cone-calculus
lem-coef-infinity-kan-homotopy-coherent-cube-invariance
lem-coef-infinity-kan-mapping-restriction
lem-coef-infinity-lax-comma-target-fibration
lem-coef-infinity-left-fibration-initial-equivalence
lem-coef-infinity-left-pinch-comparison
lem-coef-infinity-limits-products-pullbacks
lem-coef-infinity-linear-cofinal-cone-extension
lem-coef-infinity-local-adjoint-criterion
lem-coef-infinity-local-union-cell-attachment
lem-coef-infinity-local-union-transfinite-extension
lem-coef-infinity-mapping-composition
lem-coef-infinity-mapping-excision
lem-coef-infinity-marked-coanodyne-rlp-saturation
lem-coef-infinity-marked-cocartesian-lifting
lem-coef-infinity-marked-initial-vertex
lem-coef-infinity-minimal-retract
lem-coef-infinity-monadic-bar
lem-coef-infinity-monadic-comparison
lem-coef-infinity-monadic-sifted-presentability
lem-coef-infinity-monomorphism-boundary-cells
lem-coef-infinity-normalized-final-cone
lem-coef-infinity-op-mapping-reversal
lem-coef-infinity-opposite-adjunction-data
lem-coef-infinity-opposite-subdivision-kan-zigzag
lem-coef-infinity-ordinary-pointwise-kan-extension
lem-coef-infinity-pair-groupoid-thickening
lem-coef-infinity-parameter-cone-extension
lem-coef-infinity-parameterized-evaluation-naturality
lem-coef-infinity-pinch-comparison
lem-coef-infinity-pointwise-adjoint-criterion
lem-coef-infinity-pointwise-cocartesian-transport
lem-coef-infinity-pointwise-equivalences
lem-coef-infinity-pointwise-yoneda-evaluation
lem-coef-infinity-poset-nerve-cofinal-replacement
lem-coef-infinity-precomposition-cylinder
lem-coef-infinity-presentable-presheaf-presentation
lem-coef-infinity-preserves-essential-small-colimit
lem-coef-infinity-presheaf-colimit-locality
lem-coef-infinity-presheaf-free-cocompletion
lem-coef-infinity-presheaf-ind-criterion
lem-coef-infinity-presheaf-presentability
lem-coef-infinity-presheaf-representable-slice-density
lem-coef-infinity-product-colimit-fubini
lem-coef-infinity-pullback-mapping-space
lem-coef-infinity-pushout-join-saturation
lem-coef-infinity-reflection-assembly
lem-coef-infinity-reflector-accessibility
lem-coef-infinity-relative-cocone-parameters
lem-coef-infinity-relative-colimit-completion
lem-coef-infinity-relative-cone-constant-test
lem-coef-infinity-relative-cone-equivalence
lem-coef-infinity-relative-cone-initial-corner
lem-coef-infinity-relative-exponential-restriction
lem-coef-infinity-relative-hom-evaluation
lem-coef-infinity-relative-initial-boundary
lem-coef-infinity-relative-join-cartesian-realization
lem-coef-infinity-relative-join-cocartesian-projection
lem-coef-infinity-relative-join-simplex-extension
lem-coef-infinity-relative-joyal-factorization
lem-coef-infinity-relative-kan-existence
lem-coef-infinity-relative-limit-join-boundary
lem-coef-infinity-relative-slice-sections
lem-coef-infinity-retract-colimit
lem-coef-infinity-right-adjoint-reindexing
lem-coef-infinity-right-anodyne-product
lem-coef-infinity-right-anodyne-saturation
lem-coef-infinity-right-fibration-exponentiation
lem-coef-infinity-right-fibration-fibers
lem-coef-infinity-right-prism-boundary
lem-coef-infinity-section-cylinder-cocone
lem-coef-infinity-sequential-spine
lem-coef-infinity-sharp-accessibility-enlargement
lem-coef-infinity-sifted-colimit-calculus
lem-coef-infinity-sifted-coproduct-cocompleteness
lem-coef-infinity-slice-arrow-equivalence
lem-coef-infinity-slice-equivalence-final
lem-coef-infinity-slice-right-fibration
lem-coef-infinity-small-cocone-representatives
lem-coef-infinity-small-colimit-generation
lem-coef-infinity-small-full-subcategory
lem-coef-infinity-small-localization-saturation
lem-coef-infinity-source-gluing
lem-coef-infinity-space-valued-pointwise-lan
lem-coef-infinity-split-augmentation-colimit
lem-coef-infinity-terminal-anodyne
lem-coef-infinity-terminal-pullback-criterion
lem-coef-infinity-test-equivalence-by-functor-cores
lem-coef-infinity-transport-uniqueness
lem-coef-infinity-twisted-pullback-boundary-filtration
lem-coef-infinity-twisted-pullback-identity-initial
lem-coef-infinity-universe-colimit-descent
lem-coef-infinity-weakly-contractible-cocone-colimits
lem-coef-infinity-yoneda-evaluation
lem-coef-infinity-yoneda-functor-equivalence-lift
lem-coef-infinity-yoneda-presheaf-limits
lem-coef-initial-poset-slice-restriction
lem-coef-injective-simplex-cocone-restriction
lem-coef-inner-anodyne-pointwise-lan-invariance
lem-coef-inner-anodyne-pushout-product
lem-coef-inner-anodyne-slice-categorical-equivalence
lem-coef-inner-horn-cell-generation
lem-coef-interleaved-tensor-suspension
lem-coef-interval-equivalence-cocartesian
lem-coef-interval-string-inert-extraction
lem-coef-interval-string-segal-fibration
lem-coef-inverse-gadget-categorical-contractibility
lem-coef-invertible-interval-product-projection
lem-coef-iterated-span-endomorphism-naturality
lem-coef-iterated-span-fixed-endomorphism
lem-coef-join-boundary-cubical-extension
lem-coef-join-cone-weight-cofibrancy
lem-coef-join-preserves-categorical-equivalences
lem-coef-join-pullback-simplex-extension
lem-coef-join-pushout-right-anodyne
lem-coef-join-slice-cocone-comparison
lem-coef-join-slice-diagram-isomorphisms
lem-coef-join-translation-resolution
lem-coef-joyal-cartesian-pushout-product
lem-coef-joyal-filtered-equivalences
lem-coef-joyal-fixed-object-rectification
lem-coef-joyal-functor-equivalence-test
lem-coef-joyal-generating-trivial-cofibrations
lem-coef-joyal-homotopy-exponentials
lem-coef-joyal-interval-boundary-tests
lem-coef-joyal-localization-cat-infinity
lem-coef-joyal-model-structure
lem-coef-joyal-presentable-monoidal-localization
lem-coef-joyal-quasicategory-characterizations
lem-coef-joyal-small-test-universe-invariance
lem-coef-joyal-strict-currying
lem-coef-joyal-walking-isomorphism-fibration-test
lem-coef-kan-coherent-nerve-cell-filtration
lem-coef-kan-coherent-nerve-inverse-equivalence
lem-coef-kan-coherent-nerve-quasicategory
lem-coef-kan-component-restriction-fibration
lem-coef-kan-diagram-evaluation-restriction
lem-coef-kan-diagram-localized-evaluation
lem-coef-kan-fiber-path-reversal
lem-coef-kan-fibrant-path-recognition
lem-coef-kan-fibration-arbitrary-base-fibers
lem-coef-kan-fibration-edge-fiber-transport
lem-coef-kan-fibration-slice-nerve-equivalence
lem-coef-kan-fibration-tower-limit
lem-coef-kan-homotopy-cartesian-fibration-criterion
lem-coef-kan-homotopy-cartesian-invariance
lem-coef-kan-homotopy-commuting-pullback-invariance
lem-coef-kan-homotopy-pullback-invariance
lem-coef-kan-iterated-chain-comparison
lem-coef-kan-iterated-pullback-fibrancy
lem-coef-kan-locally-trivial-realization
lem-coef-kan-minimal-factorization
lem-coef-kan-nerve-pullback-recognition
lem-coef-kan-nerve-small-products
lem-coef-kan-path-boundary-bijections
lem-coef-kan-pullback-fibration-invariance
lem-coef-kan-pullback-path-comparison
lem-coef-kan-quillen-cartesian-pushout-product
lem-coef-kan-quillen-model-right-proper-core
lem-coef-kan-quillen-right-proper
lem-coef-kan-realization-serre
lem-coef-kan-relative-nerve-left-fibration
lem-coef-kan-weak-equivalence-space-edge
lem-coef-kinjective-flat-model-fibrant
lem-coef-kspace-exponential-law
lem-coef-labelled-spine-prism-horn-calculus
lem-coef-lax-cartesian-classification
lem-coef-left-cone-restriction-cocartesian
lem-coef-left-fibration-colimit-realization
lem-coef-left-fibration-dependent-sum
lem-coef-left-fibration-relative-cylinder-lifting
lem-coef-left-fibration-right-anodyne-base-change
lem-coef-left-fibration-section-homotopy-pullback
lem-coef-linear-monad-tensor-enrichment
lem-coef-lm-algebra-fibre-reconstruction
lem-coef-lm-module-fibre-reconstruction
lem-coef-lm-prism-approximation
lem-coef-local-fiber-relative-colimit-test
lem-coef-local-transport-section-colimits
lem-coef-localization-cartesian-pullback
lem-coef-localization-cartesian-pullback-pushout
lem-coef-localization-filtered-colimit
lem-coef-localization-homotopy-category
lem-coef-localization-kan-cartesian-fibration
lem-coef-localization-monomorphic-pushout
lem-coef-localized-bifunctor-partial-derived-adjoints
lem-coef-localized-good-homotopy-test
lem-coef-locally-cofibrant-dg-restriction
lem-coef-locally-constant-presheaf-slice
lem-coef-locally-small-infinity-size-calculus
lem-coef-many-object-operad-accessibility
lem-coef-mapping-path-square-rectification
lem-coef-mapping-simplex-cone-fibers
lem-coef-mapping-simplex-final-edge
lem-coef-mapping-simplex-last-fiber-pushout
lem-coef-mapping-simplex-termwise-equivalence
lem-coef-marked-action-edge-comparison
lem-coef-marked-anodyne-lifting-calculus
lem-coef-marked-cone-adjunction-substitution
lem-coef-marked-cone-external-product
lem-coef-marked-cone-generator-calculations
lem-coef-marked-cone-straightening-quillen
lem-coef-marked-endpoint-prism-generation
lem-coef-marked-enriched-colimit-universe
lem-coef-marked-flat-categorical-equivalence-test
lem-coef-marked-internal-hom
lem-coef-marked-operadic-model-structures
lem-coef-marked-opposite-relative-calculus
lem-coef-marked-point-cartesian-model
lem-coef-marked-relative-cartesian-model
lem-coef-marked-saturation-perfect-equivalences
lem-coef-marked-sections-pointwise-limits
lem-coef-marked-sharp-anodyne-restriction
lem-coef-marked-sharp-enrichment
lem-coef-marked-triangle-cancellation
lem-coef-matrix-biclosed-monoidal-structure
lem-coef-mixed-grothendieck-products
lem-coef-mixed-join-incidence-cocones
lem-coef-mixed-mapping-cocartesian-recognition
lem-coef-model-cofibrant-colimit-comparison
lem-coef-model-colimit-localization-comparison
lem-coef-model-cylinder-whitehead
lem-coef-model-equivalence-transport
lem-coef-model-finite-limit-detection
lem-coef-model-infinity-derived-adjunction
lem-coef-model-localization-detects-weak-equivalences
lem-coef-model-localization-homotopy-classes
lem-coef-model-localization-map-surjective
lem-coef-model-over-structure
lem-coef-model-product-weak-equivalence
lem-coef-model-right-homotopy-extension
lem-coef-model-structure-determined-by-fibrant-objects
lem-coef-model-undercategory-mapping-fiber
lem-coef-model-weak-equivalence-homotopy-classes
lem-coef-model-weak-equivalence-nerve
lem-coef-model-weak-equivalences-accessible
lem-coef-module-flat-cotorsion-foundation
lem-coef-module-operad-encoding
lem-coef-module-operadic-colimit-detection
lem-coef-module-scalar-restriction-coherence
lem-coef-module-scalar-restriction-mapping
lem-coef-module-universal-arrow-criterion
lem-coef-monadic-bar-totalization
lem-coef-monoidal-block-projection-coherence
lem-coef-monoidal-compact-generators
lem-coef-monoidal-relative-adjoint-inert
lem-coef-monoidal-yoneda-embedding
lem-coef-multilinear-presheaf-kan-recognition
lem-coef-nerve-natural-homotopy-equivalence
lem-coef-nondegenerate-simplex-comma-initial
lem-coef-nondegenerate-simplex-face-poset
lem-coef-nonsymmetric-operadic-tensor-adjunction
lem-coef-nonsymmetric-operads-presentability
lem-coef-open-cover-singular-excision
lem-coef-open-cover-weak-equivalence
lem-coef-operad-groupoid-operator-map
lem-coef-operadic-active-colimit-extension-criterion
lem-coef-operadic-active-cone-boundary
lem-coef-operadic-active-incidence-comparison
lem-coef-operadic-active-lift-criterion
lem-coef-operadic-algebra-colimit-change
lem-coef-operadic-algebra-presentability
lem-coef-operadic-approximation-marked-equivalence
lem-coef-operadic-approximation-restriction
lem-coef-operadic-block-incidence-lifting
lem-coef-operadic-change-enrichment
lem-coef-operadic-cocomplete-extensions
lem-coef-operadic-colimit-active-join-boundary
lem-coef-operadic-colimit-finite-amalgamation
lem-coef-operadic-collage-comparison
lem-coef-operadic-collage-relative-overbase-equivalence
lem-coef-operadic-collage-segal-mapping-bridge
lem-coef-operadic-colorwise-sifted-colimits
lem-coef-operadic-concatenation-colimits
lem-coef-operadic-correspondence-kan-filling
lem-coef-operadic-day-convolution
lem-coef-operadic-family-cell-presentation
lem-coef-operadic-free-cocone-characterization
lem-coef-operadic-free-cocone-criterion
lem-coef-operadic-free-extension
lem-coef-operadic-inert-active-factorization
lem-coef-operadic-inert-factor-equivalence
lem-coef-operadic-localization-operation-criterion
lem-coef-operadic-minimal-interval-reflection
lem-coef-operadic-operation-lifting-fiber
lem-coef-operadic-operation-segal-product
lem-coef-operadic-typec-incidence-cone
lem-coef-operadic-weak-approximation-algebras
lem-coef-opposite-join-comma-comparison
lem-coef-ordered-simplex-cone-evaluation
lem-coef-ordinal-inverse-diagram-model
lem-coef-ordinal-latching-diagram-lifting
lem-coef-ordinary-bar-evaluation-naturality
lem-coef-ordinary-comma-retraction-naturality
lem-coef-ordinary-nerve-discrete-hom-comparison
lem-coef-ordinary-nerve-functor-comparison
lem-coef-ordinary-presheaf-local-presentability
lem-coef-ordinary-two-sided-bar-comparison
lem-coef-parametric-comma-fiber-comparison
lem-coef-parametric-discrete-yoneda
lem-coef-parametric-straightening-mapping-spaces
lem-coef-parametric-universal-arrows
lem-coef-parametrized-adjunction-corner-lifting
lem-coef-partial-cellular-root-descent-extension
lem-coef-pattern-anodyne-generators
lem-coef-pattern-anodyne-lifting-products
lem-coef-pattern-fibered-edge-detection
lem-coef-pattern-generator-product-cells
lem-coef-pattern-induced-fibration-test
lem-coef-pattern-marked-mapping-components
lem-coef-pattern-marking-cancellation
lem-coef-pattern-section-core-identification
lem-coef-perfect-weak-equivalence-model-recognition
lem-coef-pinched-cube-latching
lem-coef-pinched-rigidification-resolution
lem-coef-planar-multilinear-extension
lem-coef-point-family-q-counit-identification
lem-coef-pointed-model-stability
lem-coef-pointwise-compact-diagrams
lem-coef-pointwise-constant-target-square-assembly
lem-coef-pointwise-lan-mapping-property
lem-coef-polytope-boundary-radial-extension
lem-coef-poset-filtered-cofibrant-resolution
lem-coef-poset-relative-vertex-insertion
lem-coef-presentable-cardinal-enlargement
lem-coef-presentable-cartesian-fibration
lem-coef-presentable-cellular-factorization
lem-coef-presentable-infinity-adjoints
lem-coef-presentable-presentation-comparison
lem-coef-presentable-right-adjoint-accessible
lem-coef-presentable-small-object-factorization
lem-coef-presentation-enlargement-retains-diagram
lem-coef-presheaf-bounded-intersection-replacement
lem-coef-presheaf-cylinder-model-recognition
lem-coef-presheaf-external-product-kan
lem-coef-presheaf-naive-fibration-whitehead
lem-coef-presheaf-simplex-hocolim-resolution
lem-coef-presheaf-weak-mono-bounded-enlargement
lem-coef-projective-chains-monoidal-model
lem-coef-projective-cochain-monoidal-model
lem-coef-projective-diagram-simplicial-descent
lem-coef-projective-diagram-universe-cofibrancy
lem-coef-projective-frame-weighted-coend
lem-coef-proper-word-colimit-invariance
lem-coef-qrep-moduli-pullback
lem-coef-quasicategory-classification-realization
lem-coef-quasicategory-edge-triangle-presentation
lem-coef-quasicategory-full-subcategory-core-equivalence
lem-coef-quasicategory-invertible-interval
lem-coef-quasicategory-labelled-coproduct-equivalences
lem-coef-quasicategory-simplex-join-attachment
lem-coef-quillen-b-comma-homotopy-fiber
lem-coef-quillen-b-discrete-fibration-base-change
lem-coef-quillen-b-path-minmax-homotopy
lem-coef-quillen-derived-counit-criterion
lem-coef-quillen-fibrant-test
lem-coef-quillen-section-rectification
lem-coef-realization-finite-limits
lem-coef-reedy-colimit-comparison
lem-coef-reedy-homotopy-segal-comparison
lem-coef-reedy-left-frame-comparison
lem-coef-reedy-model-structure
lem-coef-reedy-realization-homotopy-invariance
lem-coef-reedy-realization-prism
lem-coef-reedy-simplicial-frame-comparison
lem-coef-reflection-inverting-limit-restriction
lem-coef-relative-cartesian-equivalence-saturation
lem-coef-relative-categorical-cylinder-criterion
lem-coef-relative-comma-coordinate-contraction
lem-coef-relative-cone-presheaf-fibers
lem-coef-relative-coslice-homotopy-pullback-test
lem-coef-relative-cut-nerve-diagrams
lem-coef-relative-final-apex-join-boundary
lem-coef-relative-functor-cocartesian-classifier
lem-coef-relative-grothendieck-localization
lem-coef-relative-join-fixed-source-prism
lem-coef-relative-join-left-kan-reduction
lem-coef-relative-join-prism-comparison
lem-coef-relative-limit-initial-components
lem-coef-relative-limit-join-slice-recognition
lem-coef-relative-marked-anodyne-calculus
lem-coef-relative-marked-anodyne-replacement
lem-coef-relative-nerve-cylinder-contraction
lem-coef-relative-nerve-symmetric-family
lem-coef-relative-operadic-output-mapping
lem-coef-relative-operadic-output-substitution-coherence
lem-coef-relative-operadic-terminal-active-mapping
lem-coef-relative-planar-operation-extension
lem-coef-relative-right-kan-restriction
lem-coef-relative-right-kan-universal-restriction
lem-coef-relative-symmetric-monoidal-localization
lem-coef-relative-triple-mapping-space-pullback
lem-coef-relative-undercategory-limit-creation
lem-coef-representable-right-fibration-classifier
lem-coef-represented-family-slice-fibration
lem-coef-resolution-interval-tensor
lem-coef-rezk-diagonal-sharp
lem-coef-rezk-explicit-completion
lem-coef-rezk-local-model
lem-coef-right-anodyne-lifting-characterization
lem-coef-right-anodyne-mono-cancellation
lem-coef-right-approximation-slice
lem-coef-right-decalage-augmentation-prism
lem-coef-right-decalage-index-calculus
lem-coef-right-fibration-categorical-base-change
lem-coef-right-fibration-cone-section-criterion
lem-coef-right-fibration-constant-right-kan
lem-coef-right-fibration-contractible-fibers
lem-coef-right-fibration-fiberwise-kan
lem-coef-right-fibration-inner-horn-pullback
lem-coef-right-fibration-pushout-mapping-square
lem-coef-right-fibration-section-limit
lem-coef-right-straightening-fiber-comparison
lem-coef-rigidification-boundary-cube
lem-coef-rigidification-component-postcomposition
lem-coef-rigidification-equivalence-detection
lem-coef-rigidification-identity-action
lem-coef-rigidification-postcomposition-comparison
lem-coef-scat-arrow-cell-word-filtration
lem-coef-scat-bergner-left-proper-pushouts
lem-coef-scat-diagram-factorization-uniform-bound
lem-coef-scat-fixed-object-pushout-comparison
lem-coef-scat-framed-diagram-adjunction
lem-coef-scat-injective-universe-generators
lem-coef-scat-uniform-presentability
lem-coef-segal-cartesian-exponent
lem-coef-segal-categorical-constancy
lem-coef-segal-categorical-equivalence-dk
lem-coef-segal-composition-equivalences
lem-coef-segal-cotensor-evaluation-dk
lem-coef-segal-dk-diagonal-equivalence
lem-coef-segal-dk-two-out-of-six
lem-coef-segal-equivalence-classifier
lem-coef-segal-equivalence-outer-horn
lem-coef-segal-equivalence-subspace-filtered
lem-coef-segal-external-local-equivalences
lem-coef-segal-finite-cover-descent
lem-coef-segal-homotopy-category-components
lem-coef-segal-interval-cover
lem-coef-segal-inverse-evaluation
lem-coef-segal-realization-coherent-nerve
lem-coef-segal-space-inner-anodyne-locality
lem-coef-segal-spine-interval-test
lem-coef-segal-vertical-restriction-inner
lem-coef-selectively-marked-terminal-cylinder
lem-coef-serre-disk-lift-boundary-bijection
lem-coef-serre-homotopy-exact-sequence
lem-coef-sharp-filtered-poset-subsets
lem-coef-sharp-pullback-calculus
lem-coef-sharp-pushout-attachment-comparison
lem-coef-sharp-simplex-criterion
lem-coef-sharp-special-colimit-gluing
lem-coef-sheaf-flat-model
lem-coef-sifted-fixed-object-hocolimit
lem-coef-sifted-good-diagram-calculus
lem-coef-sifted-nerve-index-calculus
lem-coef-signed-word-boundary-pushout
lem-coef-simple-inner-anodyne-base-change
lem-coef-simplex-category-last-vertex
lem-coef-simplex-first-vertex-cocone-equivalence
lem-coef-simplex-last-vertex-cocone-equivalence
lem-coef-simplex-nerve-comma-pullback
lem-coef-simplicial-arrow-attachment-localization
lem-coef-simplicial-bar-latching-decomposition
lem-coef-simplicial-bar-projective-resolution
lem-coef-simplicial-bifibrant-localization
lem-coef-simplicial-boundary-collapse-test
lem-coef-simplicial-bousfield-model-structure
lem-coef-simplicial-category-degreewise-colimits
lem-coef-simplicial-derived-exponential
lem-coef-simplicial-derived-hom-adjunction
lem-coef-simplicial-derived-pushout-mapping
lem-coef-simplicial-diagram-equivalence-classes
lem-coef-simplicial-edge-inversion-pushout
lem-coef-simplicial-fixed-object-monic-cofibration
lem-coef-simplicial-fully-faithful-homotopy-image
lem-coef-simplicial-grothendieck-hocolimit
lem-coef-simplicial-groupoid-models
lem-coef-simplicial-interval-cell-stability
lem-coef-simplicial-interval-lifting
lem-coef-simplicial-inversion-product-parameter
lem-coef-simplicial-inversion-universal-property
lem-coef-simplicial-invertible-arrow-pushout
lem-coef-simplicial-latching-degenerate-subset
lem-coef-simplicial-local-bounded-lifting
lem-coef-simplicial-local-equivalences-accessible
lem-coef-simplicial-localization-comparison-calculus
lem-coef-simplicial-localization-essential-image
lem-coef-simplicial-localization-existence
lem-coef-simplicial-mapping-localization
lem-coef-simplicial-marked-cylinder-comparison
lem-coef-simplicial-model-arrow-lifting
lem-coef-simplicial-model-coherent-diagrams
lem-coef-simplicial-model-nerve-localization
lem-coef-simplicial-model-target-test
lem-coef-simplicial-natural-equivalence-homotopy
lem-coef-simplicial-operator-nerve
lem-coef-simplicial-opposite-homotopy-calculus
lem-coef-simplicial-presheaf-localization-comparison
lem-coef-simplicial-presheaf-projective-model
lem-coef-simplicial-projective-model-calculus
lem-coef-simplicial-pullback-equivalence
lem-coef-simplicial-realization-cylinder
lem-coef-simplicial-realization-extra-degeneracy
lem-coef-simplicial-relative-homotopy-invariance
lem-coef-simplicial-right-fibration-presentation
lem-coef-simplicial-shape-categorification
lem-coef-simplicial-simplex-colimit-product
lem-coef-simplicial-sm7-generator-extension
lem-coef-simplicial-small-chunks
lem-coef-simplicial-space-localization-interval-criterion
lem-coef-simplicial-space-reedy-cartesian
lem-coef-simplicial-space-small-subobjects
lem-coef-simplicial-strict-pushout-derived-comparison
lem-coef-simplicial-undercategory-model
lem-coef-simplicial-walking-groupoid-components
lem-coef-single-horn-relative-completion
lem-coef-singular-bar-realization-cylinder
lem-coef-singular-counit-weak-equivalence
lem-coef-singular-span-bar-cylinder-gluing
lem-coef-slice-cartesian-colimit-criterion
lem-coef-slice-cone-prism-simplicial
lem-coef-slice-straightening-counit
lem-coef-small-cellular-tree-descent
lem-coef-small-cocartesian-model
lem-coef-small-cotorsion-model-recognition
lem-coef-small-diagram-model-rectification
lem-coef-small-direct-colimit-lifting
lem-coef-small-family-accessibility-rank
lem-coef-small-inner-horn-completion
lem-coef-small-monoidal-full-subcategory
lem-coef-small-right-adjoint-diagram-compact-model
lem-coef-small-right-lifting-accessibility
lem-coef-small-saturated-arrow-accessibility
lem-coef-small-saturated-coslice-presentability
lem-coef-small-simplicial-diagram-cardinality
lem-coef-small-tree-presentable-vertices
lem-coef-smith-model-recognition
lem-coef-smith-small-saturated-intersection
lem-coef-sorted-simplicial-algebra-model
lem-coef-space-bimodule-collage
lem-coef-space-constant-diagram-limit
lem-coef-space-contractible-fiber-equivalence
lem-coef-space-geometric-descent
lem-coef-space-kan-fibration-fiber-criterion
lem-coef-space-path-fibration-replacement
lem-coef-space-point-cocone-criterion
lem-coef-space-presheaf-cocompletion
lem-coef-space-presheaf-presentability
lem-coef-space-presheaf-right-kan-mapping-formula
lem-coef-space-transport-classification
lem-coef-space-universal-colimits
lem-coef-space-universe-repletion
lem-coef-space-valued-straightening
lem-coef-space-yoneda-density
lem-coef-spaces-homotopy-fiber-detection
lem-coef-spaces-kappa-limit-filtered-colimit
lem-coef-spaces-slice-cartesian-closure
lem-coef-spaces-small-colimits-universe
lem-coef-spatial-mapping-interchange
lem-coef-special-hammock-reduction
lem-coef-special-resolution-zigzag-nerve
lem-coef-special-resolutions-aspherical
lem-coef-sphere-mapping-weak-equivalence
lem-coef-spine-cancellation-inner-horns
lem-coef-split-coproduct-bar-extra-degeneracy
lem-coef-split-functor-coend-filtration
lem-coef-sset-anodyne-pushout-product
lem-coef-sset-cellular-comparison
lem-coef-sset-gluing-filtered-equivalences
lem-coef-standard-simplex-realization-contraction
lem-coef-strict-bimodule-rectification
lem-coef-strict-diagram-evaluation-conservative
lem-coef-strict-intrinsic-right-fibration-slices
lem-coef-strong-monoidal-operation-morphism-lifting
lem-coef-strong-retraction-idem-colimit
lem-coef-subdivision-anodyne
lem-coef-subdivision-ex-homotopy-adjunction
lem-coef-subdivision-face-poset-calculus
lem-coef-subdivision-last-vertex-equivalence
lem-coef-suspension-square-comparison
lem-coef-symmetric-cartesian-cylinder-edge-comparison
lem-coef-symmetric-cartesian-cylinder-slice-comparison
lem-coef-symmetric-family-active-slice-calculus
lem-coef-symmetric-family-block-assembly
lem-coef-symmetric-family-block-restriction
lem-coef-symmetric-family-inert-active-orthogonality
lem-coef-symmetric-family-inert-cone-initiality
lem-coef-symmetric-inert-active-orthogonality
lem-coef-symmetric-inert-projection-detection
lem-coef-symmetric-monoidal-segal-classification
lem-coef-symmetric-operadic-active-seed-attachment
lem-coef-symmetric-operadic-base-matching
lem-coef-symmetric-operadic-extension-boundaries
lem-coef-symmetric-operadic-fibrant-objects
lem-coef-symmetric-operadic-fibration-recognition
lem-coef-symmetric-operadic-left-horn-filling
lem-coef-symmetric-operadic-mapping-cylinder
lem-coef-symmetric-relative-product-comparison
lem-coef-symmetric-weak-approximation-algebras
lem-coef-system-localization-universal
lem-coef-tensor-coend-skeletal-pushouts
lem-coef-terminal-comparison-coherence
lem-coef-terminal-local-kan-corepresentability
lem-coef-thomason-grothendieck-comparison
lem-coef-topological-serre-model
lem-coef-transfinite-isofibration-limit
lem-coef-tree-leaf-zigzag-retraction
lem-coef-tree-zigzag-finite-subtree-colimit
lem-coef-triangular-bar-excision
lem-coef-triangular-cofibrant-resolution
lem-coef-triangular-top-deletion-anodyne
lem-coef-trivial-fibration-fraction-model
lem-coef-truncated-coend-skeleton-image
lem-coef-tuple-operad-incidence
lem-coef-twisted-arrow-equivalence-invariance
lem-coef-twisted-arrow-join-horn
lem-coef-twisted-arrow-left-fibration
lem-coef-two-object-localization-pullback
lem-coef-two-sided-bar-leading-unit-extension
lem-coef-two-sided-bar-regular-word-identification
lem-coef-two-sided-coherent-bar-construction
lem-coef-two-sided-simplicial-grothendieck-invariance
lem-coef-universal-arrow-comparison
lem-coef-universal-cocone-restriction-right-anodyne
lem-coef-universal-left-fibration-identity
lem-coef-universal-localization-degenerate-edges
lem-coef-universal-localization-pushout
lem-coef-unmarked-cone-model-comparison
lem-coef-unmarked-relative-nerve-cone-comparison
lem-coef-unmarked-straightening-quillen
lem-coef-unmarked-straightening-target-change
lem-coef-unstraightening-homotopy-descent
lem-coef-unstraightening-homotopy-descent-gluing
lem-coef-unstraightening-simplex-dk-equivalence
lem-coef-unstraightening-simplex-pointwise
lem-coef-unstraightening-simplex-transport
lem-coef-unstraightening-strict-base-change
lem-coef-walking-adjunction-cell-filtration
lem-coef-walking-isomorphism-alternating-horn-filtration
lem-coef-walking-isomorphism-edge-anodyne
lem-coef-walking-module-weight-cells
lem-coef-weak-cartesian-structure-restriction
lem-coef-weak-equivalence-representable-local-model
lem-coef-weak-retraction-coherent-extension
lem-coef-weak-saturation-tree-presentation
lem-coef-weighted-coend-skeletal-filtration
lem-coef-zigzag-concatenation-invariance
lem-pur-system-section-cone
lem-pur-system-section-suspension
# 2026-10-18 propagation (L): unreachable nodes whose Lean imported the dropped machinery (hammock localization, Kan
# enrichment, infinity-fibrations, dg modules); their modules are deleted with it.
def-weil-pbc-trivial-kan-fibration
lem-coef-acyclic-cycle-orthogonal-splitting
lem-coef-chunk-span-path-object
lem-coef-dg-abc-admissible-flag-quotients
lem-coef-enriched-cellular-compatible-slices
lem-coef-hammock-pi-zero-closure
lem-coef-inert-operadic-algebra-classification
lem-coef-kan-enriched-hammock-comparison
lem-coef-reduced-word-prepend-action
lem-coef-simplicial-interval-localization
```

## F1 applicable repair notes

The main tree has no coord/repair-notes/sk-l-dl-general-quasifinite.json. The applicable resolved notes below are exact JSON bytes from their coord/repair-notes paths. The scope of each is its named dependency, rather than a fresh correction to the target's statement.

### lem-coef-cartesian-section-adjoint-mates

SHA-256: `4aa85ed6dba275c5169752b22d16e4a35eb742399fab4609a8a03455a7367fe0`.

```json
{"state": "resolved", "stage": "1", "item": "lem-coef-cartesian-section-adjoint-mates", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 0: lem-coef-derived-enriched-yoneda, lem-coef-semilinear-derived-sections; step 1: lem-coef-derived-enriched-yoneda; step 2: lem-coef-derived-enriched-yoneda; step 3: lem-coef-derived-enriched-yoneda; step 4: lem-coef-semilinear-derived-sections; step 5: lem-coef-derived-enriched-yoneda; step 6: lem-coef-derived-enriched-yoneda; step 7: lem-coef-derived-enriched-yoneda; step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-dg-mate-pasting, lem-coef-dg-mate-transpose, lem-coef-enhanced-localization-universal; step 10: lem-coef-dg-mate-pasting; step 11: lem-coef-derived-enriched-yoneda, lem-coef-dg-mate-pasting; step 12: lem-coef-semilinear-derived-sections", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-coef-cartesian-section-adjoint-mates):\nRestate without enhanced subcategories: C_n, D_n become full triangulated (thick) subcategories of the ordinary D(B_n), F_n exact functors with the coefficient isomorphisms q_{m,n}, ordinary right adjoints G_n, mates b_{m,n} invertible. Conclusion: on normalized objects of the ordinary derived categories of systems/towers whose levels lie in C_n, D_n, the levelwise F has a right adjoint G with evaluations G_n, transitions given by b_{m,n}, and unit/counit evaluating to eta_n, epsilon_n; mapping statements as RHom then Rlim. The statement's citation of the enhanced categories of lem-coef-semilinear-derived-sections was removed from stmt_deps; cite its restated ordinary D(S(B)) instead. Steps 0-3, 5-7 (derived enriched Yoneda lem-coef-derived-enriched-yoneda) -> Yoneda in the ordinary derived category [lem-galois-yoneda-fully-faithful]; steps 9-11 (dg mate pasting/transpose, enhanced localization universal property) -> Brown + uniqueness of adjoints + ordinary mate pasting, as below. Replace each enhanced/coherent right adjoint on cartesian sections by: the compact-support functor on the ordinary derived category of towers (or of strict semilinear systems) is exact and preserves coproducts on the localizing closure, so Brown representability gives its right adjoint G [lem-grothendieck-derived-brown-right-adjoint, sk-prop-sf-existence]; the level-n evaluation of G is the finite right adjoint G_n by uniqueness of adjoints [det-sp-unique-right-adjoint] applied to F o (left adjoint of evaluation) = (left adjoint of evaluation) o F_n; the transition maps of G are the mates b_{m,n} by [det-sp-unique-adjoint-coefficients]; with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels], invertible mates make G preserve normalized (cartesian) objects. Mapping-complex statements become RHom statements in the ordinary derived categories followed by Rlim. Compatibilities that were 'coherent' are now equalities of maps in ordinary derived categories, proved by transposition (Yoneda [lem-galois-yoneda-fully-faithful]) and ordinary mate pasting.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 0: lem-coef-derived-enriched-yoneda, lem-coef-semilinear-derived-sections; step 1: lem-coef-derived-enriched-yoneda; step 2: lem-coef-derived-enriched-yoneda; step 3: lem-coef-derived-enriched-yoneda; step 4: lem-coef-semilinear-derived-sections; step 5: lem-coef-derived-enriched-yoneda; step 6: lem-coef-derived-enriched-yoneda; step 7: lem-coef-derived-enriched-yoneda; step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-dg-mate-pasting, lem-coef-dg-mate-transpose, lem-coef-enhanced-localization-universal; step 10: lem-coef-dg-mate-pasting; step 11: lem-coef-derived-enriched-yoneda, lem-coef-dg-mate-pasting; step 12: lem-coef-semilinear-derived-sections. Statement citations of the machinery: lem-coef-semilinear-derived-sections.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-weil-abstract-derived-category, def-weil-pbc-adjunction-mate, def-weil-pbc-sites-and-cohomology, lem-pur-derived-change-of-rings.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.", "machinery_cited": ["lem-coef-derived-enriched-yoneda", "lem-coef-dg-mate-pasting", "lem-coef-dg-mate-transpose", "lem-coef-enhanced-localization-universal", "lem-coef-semilinear-derived-sections"], "machinery_steps": [{"step": 0, "cites": ["lem-coef-derived-enriched-yoneda", "lem-coef-semilinear-derived-sections"]}, {"step": 1, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 2, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 3, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 4, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 5, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 6, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 7, "cites": ["lem-coef-derived-enriched-yoneda"]}, {"step": 8, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 9, "cites": ["lem-coef-dg-mate-pasting", "lem-coef-dg-mate-transpose", "lem-coef-enhanced-localization-universal"]}, {"step": 10, "cites": ["lem-coef-dg-mate-pasting"]}, {"step": 11, "cites": ["lem-coef-derived-enriched-yoneda", "lem-coef-dg-mate-pasting"]}, {"step": 12, "cites": ["lem-coef-semilinear-derived-sections"]}], "keep_children": ["def-weil-abstract-derived-category", "def-weil-pbc-adjunction-mate", "def-weil-pbc-sites-and-cohomology", "lem-pur-derived-change-of-rings"], "removed_stmt_deps": ["lem-coef-semilinear-derived-sections"], "statement_restated": true}
```

### lem-coef-finite-adjunction-diagram-realization

SHA-256: `2cbc4ccb2ec97638a1294ed3bab9cdcaf6792ac3a3d2d05e80c5e5a9932a480b`.

```json
{"state": "resolved", "stage": "1", "item": "lem-coef-finite-adjunction-diagram-realization", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; statement unchanged; machinery cited at step 0: lem-coef-semilinear-derived-sections; step 1: lem-coef-semilinear-derived-sections; step 2: lem-coef-cartesian-section-adjoint-mates; step 3: lem-coef-cartesian-section-adjoint-mates; step 4: lem-coef-semilinear-derived-sections; step 5: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 6: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-cartesian-section-adjoint-mates; step 11: lem-coef-semilinear-derived-sections; returned again 2026-10-18 03:18: still cited dropped machinery", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-coef-finite-adjunction-diagram-realization):\nStatement unchanged (it already uses the ordinary D(S_W)). Steps 0, 1, 4, 5, 6, 8, 11 use the 'simultaneous enhanced models' of lem-coef-semilinear-derived-sections: use its restated ordinary levelwise operations on D(S_W) instead. Steps 2, 3, 5, 6, 9 use lem-coef-cartesian-section-adjoint-mates to build E_f and its adjunction on cartesian sections: Replace each enhanced/coherent right adjoint on cartesian sections by: the compact-support functor on the ordinary derived category of towers (or of strict semilinear systems) is exact and preserves coproducts on the localizing closure, so Brown representability gives its right adjoint G [lem-grothendieck-derived-brown-right-adjoint, sk-prop-sf-existence]; the level-n evaluation of G is the finite right adjoint G_n by uniqueness of adjoints [det-sp-unique-right-adjoint] applied to F o (left adjoint of evaluation) = (left adjoint of evaluation) o F_n; the transition maps of G are the mates b_{m,n} by [det-sp-unique-adjoint-coefficients]; with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels], invertible mates make G preserve normalized (cartesian) objects. Mapping-complex statements become RHom statements in the ordinary derived categories followed by Rlim. Compatibilities that were 'coherent' are now equalities of maps in ordinary derived categories, proved by transposition (Yoneda [lem-galois-yoneda-fully-faithful]) and ordinary mate pasting.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 0: lem-coef-semilinear-derived-sections; step 1: lem-coef-semilinear-derived-sections; step 2: lem-coef-cartesian-section-adjoint-mates; step 3: lem-coef-cartesian-section-adjoint-mates; step 4: lem-coef-semilinear-derived-sections; step 5: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 6: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-cartesian-section-adjoint-mates; step 11: lem-coef-semilinear-derived-sections. Statement citations of the machinery: none.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: cor-coef-finite-verdier, cor-sf-direct-image-ctf-proetale, def-coef-normalized-dvr-tower, def-nagata-compactification, def-weil-derived-pullback-tensor-hom, def-weil-exceptional-inverse-image, def-weil-finite-field-fiber, def-weil-finite-tor-amplitude, def-weil-integral-rational-qbar-compact-support, def-weil-l-adic-coefficient-extension, def-weil-pbc-constructible-complexes, def-weil-scheme-morphism-properties, fix-prop-projection-formula, lem-coef-derived-system-evaluation-calculus, lem-coef-finite-dualizing, lem-coef-finite-exceptional, lem-fix-compact-support-coefficient-change, lem-kun-dimension-finite-type, lem-sf-class-compact-support-comparison, lem-sf-compact-support-restriction-of-scalars, lem-sf-proetale-constructible-origin, lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-trf-open-ctf, lem-weil-finite-duality-site-comparison, lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-valued-dvr-finite-quotients, lem-weil-verdier-preservation-strata, prop-asd-internal-adjunction, prop-coef-integral-dualizing, thm-fix-general-biduality, thm-sf-comp-composition, thm-sf-preservation-class, thm-weil-pbc-site-comparison.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; keep the statement unchanged.\n\nRETURNED AGAIN (2026-10-18 03:18 CST): The landed split (Q125) kept 7 of 12 steps verbatim; step 0 still takes the full enhanced subcategories and steps citing lem-coef-cartesian-section-adjoint-mates for E_f remain. The landed version still cites dropped machinery at -. A re-split that keeps these citations will be returned again; follow the node-specific repair above.", "machinery_cited": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"], "machinery_steps": [{"step": 0, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 1, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 2, "cites": ["lem-coef-cartesian-section-adjoint-mates"]}, {"step": 3, "cites": ["lem-coef-cartesian-section-adjoint-mates"]}, {"step": 4, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 5, "cites": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"]}, {"step": 6, "cites": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"]}, {"step": 8, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 9, "cites": ["lem-coef-cartesian-section-adjoint-mates"]}, {"step": 11, "cites": ["lem-coef-semilinear-derived-sections"]}], "keep_children": ["cor-coef-finite-verdier", "cor-sf-direct-image-ctf-proetale", "def-coef-normalized-dvr-tower", "def-nagata-compactification", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-integral-rational-qbar-compact-support", "def-weil-l-adic-coefficient-extension", "def-weil-pbc-constructible-complexes", "def-weil-scheme-morphism-properties", "fix-prop-projection-formula", "lem-coef-derived-system-evaluation-calculus", "lem-coef-finite-dualizing", "lem-coef-finite-exceptional", "lem-fix-compact-support-coefficient-change", "lem-kun-dimension-finite-type", "lem-sf-class-compact-support-comparison", "lem-sf-compact-support-restriction-of-scalars", "lem-sf-proetale-constructible-origin", "lem-sf-pullback-tor-amplitude", "lem-sf-tensor-ctf", "lem-trf-open-ctf", "lem-weil-finite-duality-site-comparison", "lem-weil-l-adic-extension-integers-dvr", "lem-weil-pbc-finite-type-over-noetherian", "lem-weil-pbc-ringed-topoi-derived-pushforward-composition", "lem-weil-valued-dvr-finite-quotients", "lem-weil-verdier-preservation-strata", "prop-asd-internal-adjunction", "prop-coef-integral-dualizing", "thm-fix-general-biduality", "thm-sf-comp-composition", "thm-sf-preservation-class", "thm-weil-pbc-site-comparison"], "removed_stmt_deps": [], "statement_restated": false, "returns_again": [{"date": "2026-10-18T03:18:06", "steps": [], "stmt": []}]}
```

### lem-coef-semilinear-derived-sections

SHA-256: `19bf788b66247d2bc26e3dbd1f9cb7574cf0e8e4e147ee1b97c48238bfea8a21`.

```json
{"state": "resolved", "stage": "1", "item": "lem-coef-semilinear-derived-sections", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 1: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 2: lem-coef-quillen-section-rectification; step 3: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 4: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 5: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant, lem-coef-quillen-section-rectification; step 6: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 7: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 8: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-coef-semilinear-derived-sections):\nRestate on the ORDINARY derived category D(S(B)) of strict semilinear systems with levelwise operations. Drop from the statement: the enhanced derived module categories, homotopy coherent semilinear sections and the enhanced equivalence (clauses citing lem-coef-dg-derived-quillen-calculus and lem-coef-quillen-section-rectification; these stmt_deps were removed). Keep: componentwise exactness, evaluations D(S(B))->D(B_n) computed componentwise, normalized (cartesian) objects defined by M_m (x)^L B_n -> M_n invertible [lem-pur-derived-change-of-rings], detection of isomorphisms by evaluations, and the levelwise derived operations (exact inverse image, Ru_*, j_!, coefficient change, derived tensor, RHom) with their evaluation formulas and the exchange/projection maps as unit-counit words. 48 of the 55 citers use only this ordinary part (checked 2026-10-18). Do NOT promise an enhanced right adjoint on cartesian sections: the five citers needing right adjoints (lem-coef-cartesian-section-adjoint-mates, lem-coef-finite-adjunction-diagram-realization, lem-sf-constructible-exceptional-adjunction-coefficients, lem-pur-finite-coefficient-adjoint-comparisons, lem-pur-condensed-exceptional-reconstruction) are returned separately and get them from Brown representability. Per step: step 1 (derived coefficient extension via the flat model and dg Quillen calculus) -> K-flat resolutions [lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback, lem-pur-derived-change-of-rings, lem-weil-pbc-site-flat-quotient-tensor-ses]; steps 2-3 (section rectification, cartesian criterion) -> cohomology of a complex of systems is computed componentwise, so D(S(B)) and its evaluations need no enhanced comparison; the cartesian criterion is the levelwise statement; steps 4-6 (inverse image, direct image, extension by zero on systems) -> levelwise derived functors on the ringed topos of systems [lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, prop-pur-kinjective-resolutions-exist, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-ringed-slice-extension-tensor]; step 7 (tensor, coefficient change) -> K-flat tensor [lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-pc-tensor-complex-sheaves]; step 8 (RHom) -> K-injective RHom [def-pur-derived-internal-hom, lem-pur-rhom-well-defined]; steps 9-10 (exchange and projection words) -> ordinary unit/counit words of the derived adjunctions [def-weil-pbc-adjunction-mate], whose evaluations are the levelwise maps; step 0 stays.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 1: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 2: lem-coef-quillen-section-rectification; step 3: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 4: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 5: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant, lem-coef-quillen-section-rectification; step 6: lem-coef-dg-derived-quillen-calculus, lem-coef-sheaf-flat-model; step 7: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 8: lem-coef-dg-derived-quillen-calculus, lem-coef-kinjective-flat-model-fibrant; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus. Statement citations of the machinery: none.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-pc-cochain-complex-modules, def-pc-kflat-complex, def-pc-sheaf-restrict-scalars, def-pc-tensor-complex-sheaves, def-pur-derived-internal-hom, def-weil-abstract-derived-category, def-weil-pbc-adjunction-mate, def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category, lem-pur-derived-change-of-rings, lem-pur-rhom-well-defined, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-ringed-slice-extension-tensor, lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-ringed-topos-kflat-pullback, lem-weil-pbc-site-flat-quotient-tensor-ses, prop-pur-kinjective-resolutions-exist.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.", "machinery_cited": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-kinjective-flat-model-fibrant", "lem-coef-quillen-section-rectification", "lem-coef-sheaf-flat-model"], "machinery_steps": [{"step": 1, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-sheaf-flat-model"]}, {"step": 2, "cites": ["lem-coef-quillen-section-rectification"]}, {"step": 3, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification"]}, {"step": 4, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-sheaf-flat-model"]}, {"step": 5, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-kinjective-flat-model-fibrant", "lem-coef-quillen-section-rectification"]}, {"step": 6, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-sheaf-flat-model"]}, {"step": 7, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification", "lem-coef-sheaf-flat-model"]}, {"step": 8, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-kinjective-flat-model-fibrant"]}, {"step": 9, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification"]}, {"step": 10, "cites": ["lem-coef-dg-derived-quillen-calculus"]}], "keep_children": ["def-pc-cochain-complex-modules", "def-pc-kflat-complex", "def-pc-sheaf-restrict-scalars", "def-pc-tensor-complex-sheaves", "def-pur-derived-internal-hom", "def-weil-abstract-derived-category", "def-weil-pbc-adjunction-mate", "def-weil-pbc-sites-and-cohomology", "def-weil-sheaf-of-modules-category", "lem-pur-derived-change-of-rings", "lem-pur-rhom-well-defined", "lem-pur-site-restriction-module-adjunction-exact", "lem-weil-pbc-ringed-slice-extension-tensor", "lem-weil-pbc-ringed-topoi-derived-pullback", "lem-weil-pbc-ringed-topoi-derived-pushforward-composition", "lem-weil-pbc-ringed-topoi-derived-tensor-pullback", "lem-weil-pbc-ringed-topoi-module-adjunction", "lem-weil-pbc-ringed-topos-kflat-pullback", "lem-weil-pbc-site-flat-quotient-tensor-ses", "prop-pur-kinjective-resolutions-exist"], "removed_stmt_deps": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification"], "statement_restated": true}
```

### lem-pur-exceptional-mate-site-comparison

SHA-256: `06e6521896a4c09189917036f4fae5d0b2b1875378b2aeb1dd77ccba11ff5956`.

```json
{"state": "resolved", "stage": "1", "item": "lem-pur-exceptional-mate-site-comparison", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 3: lem-cbc-global-transport-chart-normalization; step 4: lem-cbc-global-transport-chart-normalization; Lean statement invalidated for stage-2 rework", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-pur-exceptional-mate-site-comparison):\nStatement clause 'B^p_{C_X G} is the chart transport Phi^c_G of [lem-cbc-global-transport-chart-normalization] for the exchange of [thm-cbc-finite-level-proetale]' becomes: B^p is the transported compactification exchange of the restated [thm-cbc-finite-level-proetale] for the chosen compactification c, i.e. F_L = T_L A(E^c_L) S_L^{-1} (stmt_dep on the chart normalization removed; that node belongs to the dropped Zariski-gluing branch). Steps 3 and 4 then cite thm-cbc-finite-level-proetale (and thm-cbc-finite-torsion for naturality of E^c) directly instead of the chart normalization; the rest keeps its route. The node already fixes a compactification, so the qcqs restatement covers it.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 3: lem-cbc-global-transport-chart-normalization; step 4: lem-cbc-global-transport-chart-normalization. Statement citations of the machinery: lem-cbc-global-transport-chart-normalization.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-amb-etale-compact-support, def-cbc-compact-support-square, def-cbc-exchange-map, def-compact-support-direct-image-detailed, def-kun-topological-krull-dimension, def-pur-conventions, def-sf-comparison-derived-pullback, def-weil-compactifications-refinements, def-weil-exceptional-inverse-image, def-weil-pbc-adjunction-mate, def-weil-pbc-derived-categories, def-weil-pbc-proetale-modules, def-weil-scheme-morphism-properties, lem-sf-class-compact-support-comparison, lem-weil-pbc-comparison-pullback, thm-amb-etale-exceptional-adjoint, thm-cbc-finite-level-proetale, thm-cbc-finite-torsion, thm-sf-ambient-adjoint-class, thm-weil-pbc-site-comparison.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.\n\n STAGE 2: the Lean statement is invalidated (see invalidated_lean). It is stated with the transport functors A, B, He, Hp, Cc of Sheaf.Paper.GlobalTransportChartNormalization, a module of the dropped Zariski-gluing branch that imports Sheaf.Paper.EtaleLocalCompactSupportExtension; restate it without that module (define or import those comparison functors from a module of the ordinary route, e.g. next to Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit) so that the import of GlobalTransportChartNormalization can be removed.", "machinery_cited": ["lem-cbc-global-transport-chart-normalization"], "machinery_steps": [{"step": 3, "cites": ["lem-cbc-global-transport-chart-normalization"]}, {"step": 4, "cites": ["lem-cbc-global-transport-chart-normalization"]}], "keep_children": ["def-amb-etale-compact-support", "def-cbc-compact-support-square", "def-cbc-exchange-map", "def-compact-support-direct-image-detailed", "def-kun-topological-krull-dimension", "def-pur-conventions", "def-sf-comparison-derived-pullback", "def-weil-compactifications-refinements", "def-weil-exceptional-inverse-image", "def-weil-pbc-adjunction-mate", "def-weil-pbc-derived-categories", "def-weil-pbc-proetale-modules", "def-weil-scheme-morphism-properties", "lem-sf-class-compact-support-comparison", "lem-weil-pbc-comparison-pullback", "thm-amb-etale-exceptional-adjoint", "thm-cbc-finite-level-proetale", "thm-cbc-finite-torsion", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"], "removed_stmt_deps": ["lem-cbc-global-transport-chart-normalization"], "statement_restated": true, "invalidated_lean": {"module": "Sheaf.Paper.ExceptionalMateSiteComparison", "declaration": "AlgebraicGeometry.ProEtale.exceptionalMateSiteComparison", "declarations": ["AlgebraicGeometry.ProEtale.exceptionalMateRingFinite", "AlgebraicGeometry.ProEtale.exceptionalMateCoeffFinite", "AlgebraicGeometry.ProEtale.exceptionalMateH", "AlgebraicGeometry.ProEtale.exceptionalMateUnit", "AlgebraicGeometry.ProEtale.exceptionalMateTranspose", "AlgebraicGeometry.ProEtale.exceptionalMateCounit", "AlgebraicGeometry.ProEtale.exceptionalMateEtaleExchange", "AlgebraicGeometry.ProEtale.exceptionalMateProExchange", "AlgebraicGeometry.ProEtale.exceptionalMateEtale", "AlgebraicGeometry.ProEtale.exceptionalMatePro", "AlgebraicGeometry.ProEtale.exceptionalMateV", "AlgebraicGeometry.ProEtale.exceptionalMateW", "AlgebraicGeometry.ProEtale.exceptionalMateSiteComparison"], "file": "lean/Sheaf/Paper/ExceptionalMateSiteComparison.lean", "statement": "theorem exceptionalMateSiteComparison (D : WeilConjectures.PurityFiniteSetting.{u}) {X X' Y Y' : Scheme.{u}} (aX : X ⟶ Spec (.of D.field.k)) (aY : Y ⟶ Spec (.of D.field.k)) (aY' : Y' ⟶ Spec (.of D.field.k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY'] {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (_hf : f ≫ aY = aX) (_hg : g ≫ aY = aY') (sq : IsPullback g' f' f g) (c : Compactification f) [LocallyOfFiniteType (c.g ≫ aY)] [QuasiCompact (c.g ≫ aY)] [LocallyOfFiniteType ((c.ofIsPullback sq).g ≫ aY')] [QuasiCompact ((c.ofIsPullback sq).g ≫ aY')] (d d' : ℕ) (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) (_hd' : topologicalKrullDim (c.ofIsPullback sq).Z ≤ (d' : WithBot ℕ∞)) (R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)) ⥤ DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (R' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)) ⥤ DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (adj : He D.Coefficient c ⊣ R) (adj' : He D.Coefficient (c.ofIsPullback sq) ⊣ R') : (∀ L, exceptionalMatePro D.Coefficient sq c adj adj' ((A D.Coefficient Y).obj L) ≫ (exceptionalMateW D.Coefficient g R' L).hom = (exceptionalMateV D.Coefficient g' R L).hom ≫ (A D.Coefficient X').map (exceptionalMateEtale D.Coefficient sq c adj adj' L)) ∧ (∀ (L M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (b : L ⟶ M), (p D.Coefficient g').map ((exceptionalMateH D.Coefficient R).map ((A D.Coefficient Y).map b)) ≫ exceptionalMatePro D.Coefficient sq c adj adj' ((A D.Coefficient Y).obj M) = exceptionalMatePro D.Coefficient sq c adj adj' ((A D.Coefficient Y).obj L) ≫ (exceptionalMateH D.Coefficient R').map ((p D.Coefficient g).map ((A D.Coefficient Y).map b))) ∧ (∀ (L M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (b : L ⟶ M), (l D.Coefficient g').map (R.map b) ≫ exceptionalMateEtale D.Coefficient sq c adj adj' M = exceptionalMateEtale D.Coefficient sq c adj adj' L ≫ R'.map ((l D.Coefficient g).map b)) ∧ (∀ (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} D.Coefficient))) (α : (A D.Coefficient Y).obj L ≅ N), exceptionalMatePro D.Coefficient sq c adj adj' N ≫ (exceptionalMateH D.Coefficient R').map ((p D.Coefficient g).map α.inv) ≫ (exceptionalMateW D.Coefficient g R' L).hom = (p D.Coefficient g').map ((exceptionalMateH D.Coefficient R).map α.inv) ≫ (exceptionalMateV D.Coefficient g' R L).hom ≫ (A D.Coefficient X').map (exceptionalMateEtale D.Coefficient sq c adj adj' L))", "branch": "newtargets-dag", "by": "Q95", "date": "2026-10-17", "existing": false}, "invalidated_lean_reason": "the Lean statement uses the transport functors of the dropped GlobalTransportChartNormalization module"}
```

### lem-pur-finite-coefficient-adjoint-comparisons

SHA-256: `c4b5f51dd062899ced59f958e647cd562b6c35e72396da57ec8a4180570c2cac`.

```json
{"state": "resolved", "stage": "1", "item": "lem-pur-finite-coefficient-adjoint-comparisons", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-semilinear-derived-sections; step 11: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; returned again 2026-10-18 03:18: still cited dropped machinery", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-pur-finite-coefficient-adjoint-comparisons):\nRestate one clause: 'D^b_ctf(T,A) means the full stable enhanced subcategory ... [lem-coef-semilinear-derived-sections]' becomes the full triangulated subcategory of the ordinary derived category D(T_proet, A) (stmt_dep removed). Step 8 used 'the canonical enhanced support triangle' and 'the canonical map of fibres in the enhanced stable category': instead form the support triangle functorially at chain level, i_*i^x I -> I -> j_*j^*I for K-injective representatives I (an exact sequence of complexes), so the comparison of triangles is a map of short exact sequences and its third map is canonical; then two-out-of-three as before. Step 9 cites the semilinear models only for the projection composites: plain derived functors suffice. Step 11 (enhanced geometric models and lem-coef-cartesian-section-adjoint-mates for enhanced right-adjoint realizations): delete the enhancement; what remains is levelwise invertibility and ordinary coherence equalities. Replace each enhanced/coherent right adjoint on cartesian sections by: the compact-support functor on the ordinary derived category of towers (or of strict semilinear systems) is exact and preserves coproducts on the localizing closure, so Brown representability gives its right adjoint G [lem-grothendieck-derived-brown-right-adjoint, sk-prop-sf-existence]; the level-n evaluation of G is the finite right adjoint G_n by uniqueness of adjoints [det-sp-unique-right-adjoint] applied to F o (left adjoint of evaluation) = (left adjoint of evaluation) o F_n; the transition maps of G are the mates b_{m,n} by [det-sp-unique-adjoint-coefficients]; with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels], invertible mates make G preserve normalized (cartesian) objects. Mapping-complex statements become RHom statements in the ordinary derived categories followed by Rlim. Compatibilities that were 'coherent' are now equalities of maps in ordinary derived categories, proved by transposition (Yoneda [lem-galois-yoneda-fully-faithful]) and ordinary mate pasting.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 8: lem-coef-semilinear-derived-sections; step 9: lem-coef-semilinear-derived-sections; step 11: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections. Statement citations of the machinery: lem-coef-semilinear-derived-sections.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-compact-support-direct-image-detailed, def-kun-cd, def-weil-compactifications-refinements, def-weil-l-adic-coefficient-extension, def-weil-pbc-etale-origin-witness, def-weil-pbc-scheme-conventions, def-weil-pbc-site-comparison-morphism, def-weil-proetale-constructible-sheaf, def-weil-proetale-tor-amplitude, det-sp-et-proet-adjunction-transfer, det-sp-reduction-exceptional, det-sp-unique-right-adjoint, lem-amb-etale-adjoint-locality, lem-amb-unbounded-compact-support-comparisons, lem-asd-etale-finite-twist-pullback, lem-exc-closed-support-triangle, lem-exc-residue-tor-test, lem-kun-04ca, lem-kun-0f10, lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-sc-dvr-fg-torsionfree-free, lem-sf-class-compact-support-comparison, lem-sf-comparison-pullback-exact, lem-sf-derived-homology-long-exact, lem-sf-etale-flat-constructible, lem-sf-projection-finite-constant, lem-sf-triangle-morphism-iso, lem-sp-et-proet-coefficient-compatibility, lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-complete, lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-extension-by-zero-stalks, lem-weil-pbc-finite-ring-constructible-derived-origin, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-mate-pasting, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-valued-dvr-finite-quotients, lemma-weil-pbc-geometric-stalk-conservative, prop-exc-closed-tor, prop-weil-pbc-inverse-image-modules-exact, thm-amb-etale-exceptional-adjoint, thm-amb-vector-bundle-purity, thm-dg-finite-type-constructibility, thm-nagata-compactification, thm-weil-pbc-site-comparison.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.\n\nRETURNED AGAIN (2026-10-18 03:18 CST): The FIX by Q23 (landed 03:12) kept the statement and all 13 steps of the pre-pivot version: the enhanced D^b_ctf clause, the enhanced support triangle of step 8 and the enhanced models and lem-coef-cartesian-section-adjoint-mates of step 11 are still there. The landed version still cites dropped machinery at -. A re-split that keeps these citations will be returned again; follow the node-specific repair above.", "machinery_cited": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"], "machinery_steps": [{"step": 8, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 9, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 11, "cites": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"]}], "keep_children": ["def-compact-support-direct-image-detailed", "def-kun-cd", "def-weil-compactifications-refinements", "def-weil-l-adic-coefficient-extension", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-scheme-conventions", "def-weil-pbc-site-comparison-morphism", "def-weil-proetale-constructible-sheaf", "def-weil-proetale-tor-amplitude", "det-sp-et-proet-adjunction-transfer", "det-sp-reduction-exceptional", "det-sp-unique-right-adjoint", "lem-amb-etale-adjoint-locality", "lem-amb-unbounded-compact-support-comparisons", "lem-asd-etale-finite-twist-pullback", "lem-exc-closed-support-triangle", "lem-exc-residue-tor-test", "lem-kun-04ca", "lem-kun-0f10", "lem-sbc-canonical-restrict-scalars-functor-comparisons", "lem-sc-dvr-fg-torsionfree-free", "lem-sf-class-compact-support-comparison", "lem-sf-comparison-pullback-exact", "lem-sf-derived-homology-long-exact", "lem-sf-etale-flat-constructible", "lem-sf-projection-finite-constant", "lem-sf-triangle-morphism-iso", "lem-sp-et-proet-coefficient-compatibility", "lem-weil-l-adic-extension-absolute-value", "lem-weil-l-adic-extension-complete", "lem-weil-l-adic-extension-integers-dvr", "lem-weil-pbc-extension-by-zero-exact", "lem-weil-pbc-extension-by-zero-stalks", "lem-weil-pbc-finite-ring-constructible-derived-origin", "lem-weil-pbc-finite-type-over-noetherian", "lem-weil-pbc-mate-pasting", "lem-weil-pbc-ringed-topoi-derived-tensor-pullback", "lem-weil-valued-dvr-finite-quotients", "lemma-weil-pbc-geometric-stalk-conservative", "prop-exc-closed-tor", "prop-weil-pbc-inverse-image-modules-exact", "thm-amb-etale-exceptional-adjoint", "thm-amb-vector-bundle-purity", "thm-dg-finite-type-constructibility", "thm-nagata-compactification", "thm-weil-pbc-site-comparison"], "removed_stmt_deps": ["lem-coef-semilinear-derived-sections"], "statement_restated": true, "returns_again": [{"date": "2026-10-18T03:18:06", "steps": [], "stmt": []}]}
```

### lem-pur-system-level-left-extension

SHA-256: `77b27d5e5152208276198c3d71e4ba9ada907663182b7654a1a81618cd5b5230`.

```json
{"state": "resolved", "stage": "1", "item": "lem-pur-system-level-left-extension", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; statement unchanged; machinery cited at step 4: lem-coef-sheaf-flat-model; step 5: lem-coef-quillen-section-rectification, lem-coef-semilinear-derived-sections; step 6: lem-coef-quillen-section-rectification; step 7: lem-coef-pointed-model-stability, lem-pur-system-section-cone; step 8: lem-coef-pointed-model-stability, lem-pur-system-section-suspension; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 11: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-semilinear-derived-sections; step 12: lem-coef-dg-derived-quillen-calculus; returned again 2026-10-18 03:15: still cited dropped machinery", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-pur-system-level-left-extension):\nStatement unchanged. Steps 4-12 used the flat model, projective section model structures, pointed model stability and the dg Quillen calculus (lem-coef-sheaf-flat-model, lem-coef-quillen-section-rectification, lem-coef-pointed-model-stability, lem-pur-system-section-cone, lem-pur-system-section-suspension, lem-coef-dg-derived-quillen-calculus). Replace: the level left extension E_m (free system (E_m P)_n = P (x)_{B_m} B_n for n <= m) is left adjoint to the exact evaluation; derive it with K-flat resolutions [lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback] to get LE_m left adjoint to evaluation on ordinary derived categories (compare lem-sc-mixed-global-extension-adjunction for the same pattern); cones and shifts (steps 7-8) are preserved because LE_m is an exact functor [lem-pur-left-derived-exact-when-defined, lem-pur-derived-functor-shift-05su, lem-sf-exact-functor-derived-triangulated]; steps 9-12 (coherent units, counits, comparisons) become ordinary adjunction transposes and mate pasting.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 4: lem-coef-sheaf-flat-model; step 5: lem-coef-quillen-section-rectification, lem-coef-semilinear-derived-sections; step 6: lem-coef-quillen-section-rectification; step 7: lem-coef-pointed-model-stability, lem-pur-system-section-cone; step 8: lem-coef-pointed-model-stability, lem-pur-system-section-suspension; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 11: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-semilinear-derived-sections; step 12: lem-coef-dg-derived-quillen-calculus. Statement citations of the machinery: lem-coef-semilinear-derived-sections.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-pc-sheaf-restrict-scalars, def-sp-grothendieck-abelian, def-weil-abstract-derived-category, def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category, lem-pur-derived-change-of-rings, lem-pur-ringed-site-grothendieck-abelian, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-ringed-pullback-preserves-kflat, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-site-flat-quotient-tensor-ses, prop-pur-kinjective-resolutions-exist.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; keep the statement unchanged.\n\nRETURNED AGAIN (2026-10-18 03:15 CST): The delivery of NK landed about 03:2x still carrying the old model-category steps. The landed version still cites dropped machinery at step 4: lem-coef-sheaf-flat-model; step 5: lem-coef-quillen-section-rectification; step 6: lem-coef-quillen-section-rectification; step 7: lem-coef-pointed-model-stability, lem-pur-system-section-cone; step 8: lem-coef-pointed-model-stability, lem-pur-system-section-suspension; step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 10: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model; step 11: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification; step 12: lem-coef-dg-derived-quillen-calculus. A re-split that keeps these citations will be returned again; follow the node-specific repair above.", "machinery_cited": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-pointed-model-stability", "lem-coef-quillen-section-rectification", "lem-coef-semilinear-derived-sections", "lem-coef-sheaf-flat-model", "lem-pur-system-section-cone", "lem-pur-system-section-suspension"], "machinery_steps": [{"step": 4, "cites": ["lem-coef-sheaf-flat-model"]}, {"step": 5, "cites": ["lem-coef-quillen-section-rectification", "lem-coef-semilinear-derived-sections"]}, {"step": 6, "cites": ["lem-coef-quillen-section-rectification"]}, {"step": 7, "cites": ["lem-coef-pointed-model-stability", "lem-pur-system-section-cone"]}, {"step": 8, "cites": ["lem-coef-pointed-model-stability", "lem-pur-system-section-suspension"]}, {"step": 9, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification"]}, {"step": 10, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification", "lem-coef-sheaf-flat-model"]}, {"step": 11, "cites": ["lem-coef-dg-derived-quillen-calculus", "lem-coef-quillen-section-rectification", "lem-coef-semilinear-derived-sections"]}, {"step": 12, "cites": ["lem-coef-dg-derived-quillen-calculus"]}], "keep_children": ["def-pc-sheaf-restrict-scalars", "def-sp-grothendieck-abelian", "def-weil-abstract-derived-category", "def-weil-pbc-sites-and-cohomology", "def-weil-sheaf-of-modules-category", "lem-pur-derived-change-of-rings", "lem-pur-ringed-site-grothendieck-abelian", "lem-weil-pbc-exact-functor-derived-factorization", "lem-weil-pbc-kinjective-hom-derived", "lem-weil-pbc-module-sheaves-colimits-forgetful", "lem-weil-pbc-ringed-pullback-preserves-kflat", "lem-weil-pbc-ringed-topoi-module-adjunction", "lem-weil-pbc-site-flat-quotient-tensor-ses", "prop-pur-kinjective-resolutions-exist"], "removed_stmt_deps": [], "statement_restated": false, "returns_again": [{"date": "2026-10-18T03:15:56", "steps": ["step 4: lem-coef-sheaf-flat-model", "step 5: lem-coef-quillen-section-rectification", "step 6: lem-coef-quillen-section-rectification", "step 7: lem-coef-pointed-model-stability, lem-pur-system-section-cone", "step 8: lem-coef-pointed-model-stability, lem-pur-system-section-suspension", "step 9: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification", "step 10: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification, lem-coef-sheaf-flat-model", "step 11: lem-coef-dg-derived-quillen-calculus, lem-coef-quillen-section-rectification", "step 12: lem-coef-dg-derived-quillen-calculus"], "stmt": []}]}
```

### lem-sf-constructible-exceptional-adjunction-coefficients

SHA-256: `ccef6f2774a8c15f13f53581a73f044b0ff6a50403fdb2fd1d5f1b34d4372126`.

```json
{"state": "resolved", "stage": "1", "item": "lem-sf-constructible-exceptional-adjunction-coefficients", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; statement unchanged; machinery cited at step 4: lem-coef-semilinear-derived-sections; step 6: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 12: lem-coef-semilinear-derived-sections; returned again 2026-10-18 03:18: still cited dropped machinery", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (lem-sf-constructible-exceptional-adjunction-coefficients):\nStatement unchanged. Steps 4, 6, 12 use the simultaneous enhanced section models of lem-coef-semilinear-derived-sections and (step 6) lem-coef-cartesian-section-adjoint-mates to produce 'enhanced right-adjoint realizations and an adjunction on cartesian sections'. Use the restated ordinary D(S(B)) operations for steps 4 and 12, and for step 6: Replace each enhanced/coherent right adjoint on cartesian sections by: the compact-support functor on the ordinary derived category of towers (or of strict semilinear systems) is exact and preserves coproducts on the localizing closure, so Brown representability gives its right adjoint G [lem-grothendieck-derived-brown-right-adjoint, sk-prop-sf-existence]; the level-n evaluation of G is the finite right adjoint G_n by uniqueness of adjoints [det-sp-unique-right-adjoint] applied to F o (left adjoint of evaluation) = (left adjoint of evaluation) o F_n; the transition maps of G are the mates b_{m,n} by [det-sp-unique-adjoint-coefficients]; with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels], invertible mates make G preserve normalized (cartesian) objects. Mapping-complex statements become RHom statements in the ordinary derived categories followed by Rlim. Compatibilities that were 'coherent' are now equalities of maps in ordinary derived categories, proved by transposition (Yoneda [lem-galois-yoneda-fully-faithful]) and ordinary mate pasting. The step-6 identification with def-weil-exceptional-inverse-image via uniqueness of the right adjoint stays.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 4: lem-coef-semilinear-derived-sections; step 6: lem-coef-cartesian-section-adjoint-mates, lem-coef-semilinear-derived-sections; step 12: lem-coef-semilinear-derived-sections. Statement citations of the machinery: none.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: cor-pur-general-admissibility-datum, cor-sf-direct-image-ctf-proetale, def-compact-support-direct-image-detailed, def-weil-algebraically-closed-coefficients, def-weil-derived-complete-integral-detailed, def-weil-exceptional-inverse-image, def-weil-finite-field-fiber, def-weil-finite-tor-amplitude, def-weil-integral-derived-reduction, def-weil-integral-rational-qbar-compact-support, def-weil-integral-scalar-extension, def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-modules, def-weil-rationalization-karoubi, def-weil-scheme-morphism-properties, det-sp-unique-right-adjoint, lem-coef-derived-system-evaluation-calculus, lem-coef-integral-compact-support, lem-coef-integral-residue-tor, lem-coef-normalized-dvr-effectivity, lem-galois-yoneda-hom-bijection, lem-kun-dimension-finite-type, lem-pur-coefficient-system-derived-comparison, lem-pur-derived-change-of-rings, lem-pur-etale-coefficient-system-adjoint, lem-pur-etale-exceptional-constant-tensor, lem-pur-finite-tensor-constructible-cohomology, lem-sc-derived-adjunction-from-underived, lem-sf-class-compact-support-comparison, lem-sf-comparison-tor-amplitude, lem-sf-exact-functor-derived-triangulated, lem-sf-flat-model, lem-sf-proetale-constructible-origin, lem-sf-triangulated-right-adjoint, lem-trf-open-ctf, lem-weil-finite-ctf-triangulated, lem-weil-finite-free-completed-scalar-comparison, lem-weil-integral-ctf-triangulated, lem-weil-integral-scalar-extension-constructible, lem-weil-linear-scalar-localization-triangulated, lem-weil-pbc-adjunction-of-natural-bijection, lem-weil-pbc-derived-direct-image-triangulated, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-mate-pasting, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-ringed-topoi-module-adjunction, prop-compactification-coherence-detailed, thm-amb-etale-exceptional-adjoint, thm-sf-ambient-adjoint-class, thm-weil-pbc-site-comparison.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; keep the statement unchanged.\n\nRETURNED AGAIN (2026-10-18 03:18 CST): The landed split (Q148) is the pre-pivot text verbatim (all 13 steps); step 6 still takes the enhanced F_n of lem-coef-semilinear-derived-sections and applies lem-coef-cartesian-section-adjoint-mates. The landed version still cites dropped machinery at -. A re-split that keeps these citations will be returned again; follow the node-specific repair above.", "machinery_cited": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"], "machinery_steps": [{"step": 4, "cites": ["lem-coef-semilinear-derived-sections"]}, {"step": 6, "cites": ["lem-coef-cartesian-section-adjoint-mates", "lem-coef-semilinear-derived-sections"]}, {"step": 12, "cites": ["lem-coef-semilinear-derived-sections"]}], "keep_children": ["cor-pur-general-admissibility-datum", "cor-sf-direct-image-ctf-proetale", "def-compact-support-direct-image-detailed", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-integral-derived-reduction", "def-weil-integral-rational-qbar-compact-support", "def-weil-integral-scalar-extension", "def-weil-l-adic-coefficient-extension", "def-weil-pbc-proetale-modules", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "det-sp-unique-right-adjoint", "lem-coef-derived-system-evaluation-calculus", "lem-coef-integral-compact-support", "lem-coef-integral-residue-tor", "lem-coef-normalized-dvr-effectivity", "lem-galois-yoneda-hom-bijection", "lem-kun-dimension-finite-type", "lem-pur-coefficient-system-derived-comparison", "lem-pur-derived-change-of-rings", "lem-pur-etale-coefficient-system-adjoint", "lem-pur-etale-exceptional-constant-tensor", "lem-pur-finite-tensor-constructible-cohomology", "lem-sc-derived-adjunction-from-underived", "lem-sf-class-compact-support-comparison", "lem-sf-comparison-tor-amplitude", "lem-sf-exact-functor-derived-triangulated", "lem-sf-flat-model", "lem-sf-proetale-constructible-origin", "lem-sf-triangulated-right-adjoint", "lem-trf-open-ctf", "lem-weil-finite-ctf-triangulated", "lem-weil-finite-free-completed-scalar-comparison", "lem-weil-integral-ctf-triangulated", "lem-weil-integral-scalar-extension-constructible", "lem-weil-linear-scalar-localization-triangulated", "lem-weil-pbc-adjunction-of-natural-bijection", "lem-weil-pbc-derived-direct-image-triangulated", "lem-weil-pbc-finite-type-over-noetherian", "lem-weil-pbc-mate-pasting", "lem-weil-pbc-ringed-strict-tower-homotopy-limit", "lem-weil-pbc-ringed-topoi-derived-pushforward-composition", "lem-weil-pbc-ringed-topoi-module-adjunction", "prop-compactification-coherence-detailed", "thm-amb-etale-exceptional-adjoint", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"], "removed_stmt_deps": [], "statement_restated": false, "returns_again": [{"date": "2026-10-18T03:18:06", "steps": [], "stmt": []}]}
```

### thm-cbc-finite-level-proetale

SHA-256: `5ae8448f7aa964b21811e5b043930200f95fae5e24e3c9a095e78d80e503a463`.

```json
{"state": "resolved", "stage": "1", "item": "thm-cbc-finite-level-proetale", "by": "L (route pivot, decision of the human 2026-10-18)", "date": "2026-10-18", "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)", "note": "route pivot (the human, 2026-10-18): re-split on the ordinary derived route; restate the statement; machinery cited at step 0: lem-cbc-etale-local-compact-support-extension; step 2: lem-cbc-etale-local-compact-support-extension; step 6: lem-cbc-global-transport-chart-normalization; step 7: lem-cbc-global-transport-chart-normalization; step 8: lem-cbc-global-transport-chart-normalization; step 9: lem-cbc-global-transport-chart-normalization", "reason": "Route decision (the human, 2026-10-18): the infinity-categorical / dg / model-category route that stage-1 workers built for the l-adic coefficient work (about 1300 nodes below the cone hubs def-cbc-enhanced-diagrams-cones, lem-cbc-enhanced-functor-cone-calculus and the enhanced part of lem-coef-semilinear-derived-sections, mostly absent from Mathlib) was judged far larger than the ordinary derived route, and is no longer reached from the targets. Use the ordinary derived route: the coefficient category is the ordinary derived category D(Tow) of the ringed topos of towers [det-sp-coefficient-towers-abelian, sk-def-sp-coefficient-towers], Rlim is a right derived functor; right adjoints of compact-support functors come from Brown representability [lem-grothendieck-derived-brown-right-adjoint, lem-pc-brown-representability-right-adjoint, sk-prop-sf-existence]; their levels and coefficient maps come from uniqueness of adjoints [det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients] together with red o Rf_! = Rf_! o red [det-sp-tower-shriek-levels]; gluing goes by uniqueness of representing pairs [det-sp-tower-gluing]; flat models are replaced by K-flat resolutions (Stacks 06YS) [lem-pc-kflat-resolution, lem-pc-kflat-closure, lem-pc-kflat-total-tensor-associativity, lem-kun-derived-tensor-well-defined]; filtered work uses the ordinary filtered derived category (Stacks 09QJ) [lem-coef-dg-abc-homotopy-category-triangulated]. Exactness/shift facts for ordinary derived functors: [lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-sf-triangulated-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism]; ordinary mates [def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting]. This note is guidance with its evidence, not a lock: another route is acceptable if it avoids that machinery and the split report justifies it. Do not cite any node of the machinery listed under 'machinery_cited'.\n\nNODE-SPECIFIC REPAIR (thm-cbc-finite-level-proetale):\nRestate (qcqs restriction, the human 2026-10-18): 'Let Lambda be finite, let the square be a compact-support base-change square [def-cbc-compact-support-square] with f separated of finite type and g arbitrary, and assume that Y is qcqs or that a compactification c of f is given. Let K in D^+(X_proet, Lambda) carry an etale-origin witness (L, alpha). Then the pro-etale exchange g^{-1}Rf_!K -> Rf'_!g'^{-1}K, i.e. the compactification formula of [def-cbc-exchange-map] for c (for a Nagata compactification when only qcqs is assumed) transported to etale-origin objects, is an isomorphism, independent of c and of the witness.' Drop the clause 'For arbitrary bases ... Zariski-local extension [lem-cbc-etale-local-compact-support-extension] ...; no compactification datum or quasi-compact-open hypothesis is imposed' (stmt_dep removed). Proof: for qcqs Y the present step-1 argument works globally: Nagata [thm-nagata-compactification] gives c with quasi-compact open part [lemma-nagata-open-immersion-qc-over-separated-target]; then [thm-cbc-finite-torsion] (including its independence of the compactification) gives the etale isomorphism; keep the transport steps 3-4 and the witness steps 7-9 (their uses of lem-cbc-global-transport-chart-normalization become direct: the transported map is F_L = T_L A(E^c_L) S_L^{-1}). Steps 0, 2 (its localization clause), 5 and 6 belonged to the Zariski-gluing branch (lem-cbc-etale-local-compact-support-extension, lem-cbc-global-transport-chart-normalization, and below them lem-cbc-zariski-enhanced-derived-descent and the hypersheaf machinery) and are dropped. Consumers checked 2026-10-18: all 29 citers work over separated finite-type k-schemes (qcqs) or supply a compactification; the two that cited the chart normalization are lem-pur-smb-extraordinary (citation swapped in place) and lem-pur-exceptional-mate-site-comparison (returned). Upstream Lean also uses HasCompactification. The Lean statement (it takes D : Etale.LocalCompactSupportExtension) is invalidated for stage-2 rework: see invalidated_lean.\n\nLocations that cite the machinery (0-based proof steps as in the node file): step 0: lem-cbc-etale-local-compact-support-extension; step 2: lem-cbc-etale-local-compact-support-extension; step 6: lem-cbc-global-transport-chart-normalization; step 7: lem-cbc-global-transport-chart-normalization; step 8: lem-cbc-global-transport-chart-normalization; step 9: lem-cbc-global-transport-chart-normalization. Statement citations of the machinery: lem-cbc-etale-local-compact-support-extension.\n\nNon-machinery children of the old split, to reuse in the re-split where they still fit: def-cbc-compact-support-square, def-cbc-exchange-map, def-weil-pbc-derived-categories, def-weil-pbc-etale-origin-witness, def-weil-pbc-proetale-modules, def-weil-pbc-proetale-operations, def-weil-pbc-scheme-conventions, lem-cbc-fully-faithful-isomorphism-lift, lem-cbc-proetale-extension-zero, lem-cbc-proetale-extension-zero-base-change, lem-cbc-proetale-extension-zero-comparison, lem-pc-separated-quasi-separated, lem-pod-separated-finite-type-base-change, lem-weil-pbc-comparison-pullback, lem-weil-pbc-derived-plus-iso-on-cohomology, lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-qcqs-over-affine, lem-weil-pbc-transport-identifies-exchange, lemma-nagata-open-immersion-qc-over-separated-target, lemma-weil-pbc-geometric-stalk-conservative, prop-weil-pbc-comparison-direct-image, prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-site-comparison-finite-level, thm-cbc-finite-torsion, thm-nagata-compactification, thm-weil-pbc-site-comparison.\n\nReturned WITHOUT keep_plan: the old plan's children are not reached until the new split cites them. The old proof text stays in the node file as a starting point; the statement is to be restated as described above.", "machinery_cited": ["lem-cbc-etale-local-compact-support-extension", "lem-cbc-global-transport-chart-normalization"], "machinery_steps": [{"step": 0, "cites": ["lem-cbc-etale-local-compact-support-extension"]}, {"step": 2, "cites": ["lem-cbc-etale-local-compact-support-extension"]}, {"step": 6, "cites": ["lem-cbc-global-transport-chart-normalization"]}, {"step": 7, "cites": ["lem-cbc-global-transport-chart-normalization"]}, {"step": 8, "cites": ["lem-cbc-global-transport-chart-normalization"]}, {"step": 9, "cites": ["lem-cbc-global-transport-chart-normalization"]}], "keep_children": ["def-cbc-compact-support-square", "def-cbc-exchange-map", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-operations", "def-weil-pbc-scheme-conventions", "lem-cbc-fully-faithful-isomorphism-lift", "lem-cbc-proetale-extension-zero", "lem-cbc-proetale-extension-zero-base-change", "lem-cbc-proetale-extension-zero-comparison", "lem-pc-separated-quasi-separated", "lem-pod-separated-finite-type-base-change", "lem-weil-pbc-comparison-pullback", "lem-weil-pbc-derived-plus-iso-on-cohomology", "lem-weil-pbc-extension-by-zero-exact", "lem-weil-pbc-qcqs-over-affine", "lem-weil-pbc-transport-identifies-exchange", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-comparison-direct-image", "prop-weil-pbc-inverse-image-modules-exact", "prop-weil-pbc-site-comparison-finite-level", "thm-cbc-finite-torsion", "thm-nagata-compactification", "thm-weil-pbc-site-comparison"], "removed_stmt_deps": ["lem-cbc-etale-local-compact-support-extension"], "statement_restated": true, "invalidated_lean": {"module": "Sheaf.Paper.FiniteLevelProEtaleCompactSupportBaseChange", "declaration": "AlgebraicGeometry.ProEtale.finiteLevelCompactSupportExchange_isIso", "declarations": ["AlgebraicGeometry.ProEtale.cbcCoefficientPullbackComparison", "AlgebraicGeometry.ProEtale.cbcDerivedPullbackComparison", "AlgebraicGeometry.ProEtale.cbcComparisonUnitIso", "AlgebraicGeometry.ProEtale.cbcTransportedCompactSupport", "AlgebraicGeometry.ProEtale.cbcCompactSupportComparison", "AlgebraicGeometry.ProEtale.finiteLevelCompactSupportExchange", "AlgebraicGeometry.ProEtale.finiteLevelCompactSupportExchange_isIso"], "file": "lean/Sheaf/Paper/FiniteLevelProEtaleCompactSupportBaseChange.lean", "statement": "theorem finiteLevelCompactSupportExchange_isIso (D : Etale.LocalCompactSupportExtension Λ) {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (sq : IsPullback g' f' f g) (K : FiniteCoefficientDerivedCategoryPlus X Λ) (W : EtaleOriginWitness X Λ K) : IsIso (finiteLevelCompactSupportExchange Λ D sq K W) ∧ ∀ (W' : EtaleOriginWitness X Λ K) (e : W.L ≅ W'.L), (finiteCoefficientComparison X Λ).mapDerivedCategoryPlus.mapIso e ≪≫ W'.alpha = W.alpha → finiteLevelCompactSupportExchange Λ D sq K W = finiteLevelCompactSupportExchange Λ D sq K W'", "branch": "newtargets-dag", "by": "Q24", "date": "2026-10-16", "existing": false, "note": "The coherent extension data are supplied by the prerequisite existence theorem; the statement holds for every such simultaneously normalized system. Endpoints are A H Rnu, independent of the retained witness. The arrow is the prescribed conjugate of the specified etale exchange."}, "invalidated_lean_reason": "statement restated (qcqs or given compactification); the Lean statement takes the Zariski-local extension data"}
```

## F1 historical comparison text

The exact historical proofs are exhibited below. They are comparison material, not dependencies or proposed current proofs.

The imported main sketch has one unclassified paragraph, no used-node citations, and already gives the unit's intended route: finite geometric fibre, Frobenius orbits, normalized weights, then exact transport of a mixed filtration. The repaired ten-step split realizes that same route using a finite compactification, affine restriction and the specified coefficient-presentation comparison. No chapter or unit route is replaced.

The earlier returned head c1dde7e4a9 had seven steps. Its Step 3 applied PBC directly to a framework functor by saying “Here Rf_! is ...”, without a functor/arrow comparison. Its Step 6 used the isomorphism-only punctual-weight lemmas. The retained d219aca8d8 proof repaired these by Steps 3–4 and the auxiliary comparison, and by the explicit arbitrary-embedding calculation in Steps 7–9. Earlier Steps 1–2 remain the finite compactification/affine restriction, Step 4 is now Step 5 with a weight-free immersion citation, Step 5 is now Step 6, and Step 7 is now Step 10 with updated step references. The statements are identical across all three heads.

Against d219aca8d8, all ten repaired step texts, uses lists, and elementary flags are identical, as is the new auxiliary statement. Only Steps 7–9 source locations and the split_report were changed in the item. The missing substantive change required by F1 is the evidence now inside this report: exact manifest, applicable notes, historical text and the per-root closure computation. The return expressly accepted the current mathematics, so I did not invent a mathematical route change merely to make the diff larger.

### Exact main mathematical record

```json
{
 "id": "sk-l-dl-general-quasifinite",
 "statement": "Let $f_0:X_0\\to Y_0$ be a separated, quasi-finite morphism of finite\ntype of $k_0$-schemes, with $Y_0$ quasi-separated of finite type over\n$k_0$. Then $R^if_{0!}F=0$ for every Weil sheaf $F$ and every $i>0$;\nand if $F$ is $\\iota$-mixed of weights at most $w$ (resp. has all local\nFrobenius eigenvalues of weight at most $w$), then so is (resp. has)\n$f_{0!}F=R^0f_{0!}F$.",
 "stmt_deps": [
  "sk-d-dl-general-weights"
 ],
 "proof": [
  {
   "text": "Compact-support base change identifies the stalks with cohomology of a\nfinite geometric fiber, concentrated in degree zero. Thus $f_{0!}$ is\nexact. At a closed point $y$, Frobenius permutes the stalk summands.\nFor an orbit of length $e$, an eigenvalue $\\alpha$ upstairs gives\neigenvalues $\\beta$ downstairs with $\\beta^e=\\alpha$; since\n$q_x=q_y^e$, their normalized weights agree. Hence an upper bound $w$\non the weights of all local Frobenius eigenvalues of $F$ passes to\n$f_{0!}F$, pure sheaves stay pure, and exactness transports a mixed\nfiltration.",
   "uses": [],
   "elementary": null
  }
 ],
 "proof_deps": [],
 "proof_origin": {
  "by": "agent",
  "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/_section.md",
  "place": "## Proof"
 }
}
```

### Exact earlier-return mathematical record

```json
{
 "id": "sk-l-dl-general-quasifinite",
 "statement": "Let $f_0:X_0\\to Y_0$ be a separated, quasi-finite morphism of finite\ntype of $k_0$-schemes, with $Y_0$ quasi-separated of finite type over\n$k_0$. Then $R^if_{0!}F=0$ for every Weil sheaf $F$ and every $i>0$;\nand if $F$ is $\\iota$-mixed of weights at most $w$ (resp. has all local\nFrobenius eigenvalues of weight at most $w$), then so is (resp. has)\n$f_{0!}F=R^0f_{0!}F$.",
 "stmt_deps": [
  "sk-d-dl-general-weights",
  "def-weil-weil-sheaf-complex",
  "pqf-def-quasifinite",
  "def-weil-pbc-scheme-conventions",
  "def-weil-integral-rational-qbar-compact-support"
 ],
 "proof": [
  {
   "text": "The target $Y_0$ is quasi-compact because it is of finite type over a field, and is quasi-separated by hypothesis. Apply [thm-pqf-zmt-factorization] to obtain $X_0\\xrightarrow{j_0}T_0\\xrightarrow{p_0}Y_0$, with $j_0$ quasi-compact open, $p_0$ finite, and $f_0=p_0j_0$. This is a compactification since a finite morphism is proper [lem-weil-pbc-finite-proper]. It is over $k_0$, giving compatible geometric base changes. No absolute separatedness of $Y_0$ or $T_0$ is inferred. The false inference in the blueprint proof of lem-zl-quasi-finite is avoided: the identity of the affine line with doubled origin is a finite morphism whose source is not separated over $k_0$.",
   "uses": [
    "thm-pqf-zmt-factorization",
    "lem-weil-pbc-finite-proper"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "first paragraph, finite compactification; correction of the false absolute-separatedness inference"
   }
  },
  {
   "text": "For each affine open $V_0\\subseteq Y_0$, put $T_{V_0}=T_0\\times_{Y_0}V_0$ and $X_{V_0}=X_0\\times_{Y_0}V_0$. By [lem-weil-pbc-finite-morphism-permanence], $p_{V_0}:T_{V_0}\\to V_0$ is finite and $T_{V_0}$ is affine. By [lem-weil-pbc-open-immersion-base-change], $j_{V_0}:X_{V_0}\\hookrightarrow T_{V_0}$ is open. Both $V_0$ and $T_{V_0}$ are separated over $k_0$ by [lem-weil-pbc-affine-source-morphism-separated]; $X_{V_0}$ is separated over $k_0$ because its diagonal is the restriction of the closed diagonal of $T_{V_0}$. These schemes are finite type over $k_0$: $Y_0$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], its open $V_0$ is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian] and locally finite type, $T_{V_0}$ is finite over $V_0$, and $X_{V_0}$ is a quasi-compact open of $T_{V_0}$. Their geometric base changes remain separated and finite type by [lem-pod-separated-finite-type-base-change]. The affine opens cover $Y_0$ by [lem-weil-pbc-affine-opens-basis].",
   "uses": [
    "lem-weil-pbc-finite-morphism-permanence",
    "lem-weil-pbc-open-immersion-base-change",
    "lem-weil-pbc-affine-source-morphism-separated",
    "lem-weil-pbc-finite-type-over-noetherian",
    "lem-weil-pbc-noetherian-open-subscheme-noetherian",
    "lem-pod-separated-finite-type-base-change",
    "lem-weil-pbc-affine-opens-basis"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "finite factorization, restricted to affine target opens before applying separated-scheme results"
   }
  },
  {
   "text": "Write $V=V_0\\times_{k_0}k$ and $X_V=X_{V_0}\\times_{k_0}k$. Apply [thm-cbc-qbar] to the open base-change square for $f:X\\to Y$ and $v:V\\hookrightarrow Y$. Its finite-stage hypotheses are those stated in [thm-cbc-finite-extension]: all four schemes are Noetherian and finite-dimensional, by [lem-weil-pbc-finite-type-over-noetherian] and [lem-kun-dimension-finite-type], and $\\ell$ is invertible because $\\ell\\ne\\operatorname{char}k_0$. Hence there is a natural isomorphism $v^*Rf_!F\\simeq Rf_{V!}(F|_{X_V})$. Here $Rf_!$ is the compactification/common-stage construction of [def-weil-integral-rational-qbar-compact-support], using Step 1. Crucially the two base-change statements impose relative separatedness of $f$, not absolute separatedness of $X$ or $Y$. Since $V_0$ is defined over $k_0$, the Frobenius square preserves this open. Naturality and pasted-square coherence in [thm-cbc-finite-extension], followed by the common-stage descent in [thm-cbc-qbar], identify the two composites with the Frobenius isomorphism of $F$. Thus this restriction comparison is an isomorphism of Weil complexes, with Weil structures as in [def-weil-weil-sheaf-complex].",
   "uses": [
    "thm-cbc-qbar",
    "thm-cbc-finite-extension",
    "lem-weil-pbc-finite-type-over-noetherian",
    "lem-kun-dimension-finite-type",
    "def-weil-integral-rational-qbar-compact-support",
    "def-weil-weil-sheaf-complex"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "common-stage descent of the natural coherent compact-support exchange, applied to open restriction"
   }
  },
  {
   "text": "On the separated finite-type schemes of Step 2, the composition and properness laws of [prop-functor-package] give $Rf_{V!}\\simeq Rp_{V*}j_{V!}$. The exact constructible extension-by-zero functor in [lem-zl-extension-by-zero-punctual] identifies the open compact-support operation with $j_{V!}$ on sheaves. The finite direct image is standard-$t$-exact and exact on the constructible heart by [lem-zl-finite-adic-direct-image]. Consequently for every constructible Weil sheaf $A$ on $X_{V_0}$, $Rf_{V!}A\\simeq p_{V*}j_{V!}A$ is a sheaf in degree zero, and $A\\mapsto p_{V*}j_{V!}A$ is exact. Every invocation of these three statements is now on absolutely separated finite-type schemes, including $T_{V_0}$ and its geometric base change.",
   "uses": [
    "prop-functor-package",
    "lem-zl-extension-by-zero-punctual",
    "lem-zl-finite-adic-direct-image"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "proof of (1), exactness after affine target restriction"
   }
  },
  {
   "text": "Restriction to $V$ commutes with cohomology and is exact on constructible hearts by [lem-a1-constructible-pullback-t-exact]. Steps 3 and 4 therefore show that every cohomology sheaf $\\mathcal H^i(Rf_!F)$ with $i\\ne0$ restricts to zero on each $V$. The open-cover exactness criterion in [lem-dl-a1-constructible-fibres-exact] detects its vanishing: apply it to the short complex $0\\to\\mathcal H^i(Rf_!F)\\to0$, which is exact on each member of this separated open cover. Thus $Rf_!F$ lies in the constructible heart, and in particular $R^if_{0!}F=0$ for $i>0$. For any short exact sequence of constructible Weil sheaves on $X_0$, restriction to $X_V$ is exact by the pullback statement. By Step 4 its direct-image sequence is exact over each $V$. Applying the same open-cover criterion to that sequence proves that $f_{0!}=R^0f_{0!}$ is an exact functor globally. These checks are on constructible adic sheaves, not arbitrary pro-etale sheaves.",
   "uses": [
    "lem-a1-constructible-pullback-t-exact",
    "lem-dl-a1-constructible-fibres-exact"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "proof of (1), local detection of vanishing and exactness on a possibly nonseparated target"
   }
  },
  {
   "text": "Suppose $F$ has punctual upper weight bound $w$, or is punctually pure of weight $w$. Its restriction to $X_{V_0}$ has the same property: a point of this open is closed in $X_{V_0}$ exactly when it is closed in $X_0$, since both are finite type over $k_0$ and closedness is equivalent to finiteness of the residue field over $k_0$ by [lem-kun-closed-point-field]. Restriction leaves that residue field, the coefficient fibre, and its local Frobenius unchanged. On the separated chart, [lem-zl-extension-by-zero-punctual] preserves the chosen bound or purity under $j_{V!}$, and [lem-zl-finite-pushforward-punctual] preserves it under $p_{V*}$. By the Weil-compatible comparison in Step 3 and the degree-zero identification in Step 4, this is exactly the restriction of $f_{0!}F$ to $V_0$. Every closed $y\\in Y_0$ lies in some affine $V_0$, where its residue field and Frobenius are the same as on $Y_0$. Thus $f_{0!}$ globally preserves punctual upper bounds and punctual purity, with exactly the same real weight $w$. The definitions of these two predicates are [def-weil-punctual-weights].",
   "uses": [
    "lem-kun-closed-point-field",
    "lem-zl-extension-by-zero-punctual",
    "lem-zl-finite-pushforward-punctual",
    "def-weil-punctual-weights"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "proof of (2), punctual upper bound and purity on affine charts, then all closed points"
   }
  },
  {
   "text": "If $F$ is mixed of weights at most $w$, choose its global finite filtration $0=G_0\\subset\\cdots\\subset G_n=F$ with punctually pure quotients $Q_i$ of weights $u_i\\le w$, as in [sk-d-dl-general-weights]. Exactness from Step 5 sends each $0\\to G_{i-1}\\to G_i\\to Q_i\\to0$ to $0\\to f_{0!}G_{i-1}\\to f_{0!}G_i\\to f_{0!}Q_i\\to0$. Thus the inclusions give a finite filtration of $f_{0!}F$ with quotients $f_{0!}Q_i$. Step 6 shows that these quotients are punctually pure of the same $u_i$. This is exactly the mixed upper bound $w$ of [sk-d-dl-general-weights]. A zero quotient can be omitted. In particular this argument applies one global input filtration; it does not assume descent or uniqueness of independently chosen local mixed filtrations.",
   "uses": [
    "sk-d-dl-general-weights"
   ],
   "elementary": true,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "final mixed-filtration paragraph, using global exactness and purity established above"
   }
  }
 ],
 "proof_deps": [
  "def-weil-integral-rational-qbar-compact-support",
  "def-weil-punctual-weights",
  "def-weil-weil-sheaf-complex",
  "lem-a1-constructible-pullback-t-exact",
  "lem-dl-a1-constructible-fibres-exact",
  "lem-kun-closed-point-field",
  "lem-kun-dimension-finite-type",
  "lem-pod-separated-finite-type-base-change",
  "lem-weil-pbc-affine-opens-basis",
  "lem-weil-pbc-affine-source-morphism-separated",
  "lem-weil-pbc-finite-morphism-permanence",
  "lem-weil-pbc-finite-proper",
  "lem-weil-pbc-finite-type-over-noetherian",
  "lem-weil-pbc-noetherian-open-subscheme-noetherian",
  "lem-weil-pbc-open-immersion-base-change",
  "lem-zl-extension-by-zero-punctual",
  "lem-zl-finite-adic-direct-image",
  "lem-zl-finite-pushforward-punctual",
  "prop-functor-package",
  "sk-d-dl-general-weights",
  "thm-cbc-finite-extension",
  "thm-cbc-qbar",
  "thm-pqf-zmt-factorization"
 ],
 "proof_origin": {
  "by": "agent",
  "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/_section.md",
  "place": "Unit finite-fibre/base-change argument, expanded using its finite compactification proof and affine target restriction to repair absolute separatedness; no use of the disputed proof of lem-zl-quasi-finite"
 }
}
```

### Exact returned mathematical record

```json
{
 "id": "sk-l-dl-general-quasifinite",
 "statement": "Let $f_0:X_0\\to Y_0$ be a separated, quasi-finite morphism of finite\ntype of $k_0$-schemes, with $Y_0$ quasi-separated of finite type over\n$k_0$. Then $R^if_{0!}F=0$ for every Weil sheaf $F$ and every $i>0$;\nand if $F$ is $\\iota$-mixed of weights at most $w$ (resp. has all local\nFrobenius eigenvalues of weight at most $w$), then so is (resp. has)\n$f_{0!}F=R^0f_{0!}F$.",
 "stmt_deps": [
  "sk-d-dl-general-weights",
  "def-weil-weil-sheaf-complex",
  "pqf-def-quasifinite",
  "def-weil-pbc-scheme-conventions",
  "def-weil-integral-rational-qbar-compact-support"
 ],
 "proof": [
  {
   "text": "The target $Y_0$ is quasi-compact because it is of finite type over a field, and is quasi-separated by hypothesis. Apply [thm-pqf-zmt-factorization] to obtain $X_0\\xrightarrow{j_0}T_0\\xrightarrow{p_0}Y_0$, with $j_0$ quasi-compact open, $p_0$ finite, and $f_0=p_0j_0$. This is a compactification since a finite morphism is proper [lem-weil-pbc-finite-proper]. It is over $k_0$, giving compatible geometric base changes. No absolute separatedness of $Y_0$ or $T_0$ is inferred. The false inference in the blueprint proof of lem-zl-quasi-finite is avoided: the identity of the affine line with doubled origin is a finite morphism whose source is not separated over $k_0$.",
   "uses": [
    "thm-pqf-zmt-factorization",
    "lem-weil-pbc-finite-proper"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "first paragraph, finite compactification; correction of the false absolute-separatedness inference"
   }
  },
  {
   "text": "For each affine open $V_0\\subseteq Y_0$, put $T_{V_0}=T_0\\times_{Y_0}V_0$ and $X_{V_0}=X_0\\times_{Y_0}V_0$. By [lem-weil-pbc-finite-morphism-permanence], $p_{V_0}:T_{V_0}\\to V_0$ is finite and $T_{V_0}$ is affine. By [lem-weil-pbc-open-immersion-base-change], $j_{V_0}:X_{V_0}\\hookrightarrow T_{V_0}$ is open. Both $V_0$ and $T_{V_0}$ are separated over $k_0$ by [lem-weil-pbc-affine-source-morphism-separated]; $X_{V_0}$ is separated over $k_0$ because its diagonal is the restriction of the closed diagonal of $T_{V_0}$. These schemes are finite type over $k_0$: $Y_0$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], its open $V_0$ is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian] and locally finite type, $T_{V_0}$ is finite over $V_0$, and $X_{V_0}$ is a quasi-compact open of $T_{V_0}$. Their geometric base changes remain separated and finite type by [lem-pod-separated-finite-type-base-change]. The affine opens cover $Y_0$ by [lem-weil-pbc-affine-opens-basis].",
   "uses": [
    "lem-weil-pbc-finite-morphism-permanence",
    "lem-weil-pbc-open-immersion-base-change",
    "lem-weil-pbc-affine-source-morphism-separated",
    "lem-weil-pbc-finite-type-over-noetherian",
    "lem-weil-pbc-noetherian-open-subscheme-noetherian",
    "lem-pod-separated-finite-type-base-change",
    "lem-weil-pbc-affine-opens-basis"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "finite factorization, restricted to affine target opens before applying separated-scheme results"
   }
  },
  {
   "text": "For $V=V_0\\times_{k_0}k$, put $u:X_V\\hookrightarrow X$ and $v:V\\hookrightarrow Y$. The four schemes and the finite compactification scheme $T$ are Noetherian and finite-dimensional by [lem-weil-pbc-finite-type-over-noetherian] and [lem-kun-dimension-finite-type]; $\\ell$ is invertible. Apply [lem-zl-framework-pbc-open-exchange-comparison] to the supplied finite compactification. It identifies the actual framework functor $R\\lim_n\\operatorname{Res}_n Rp_{*,n}j_!K_n$ with the completed PBC $Rp_*j_!$ under the coefficient-presentation equivalences $J$. For the two composite functors it supplies the specified endpoint isomorphisms $S,T$ and the equation $\\operatorname{Ex}^{\\mathrm{pbc}}J\\circ S=T\\circ J(\\operatorname{Ex}^{\\mathrm{sf}})$. Thus the exchange comparison includes the strict quotient transitions and the proper/open mates before taking the derived limit. This is the comparison of functors and arrows needed here; equality of their finite evaluations alone is not used.",
   "uses": [
    "lem-zl-framework-pbc-open-exchange-comparison",
    "lem-weil-pbc-finite-type-over-noetherian",
    "lem-kun-dimension-finite-type"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "Common-stage compact-support exchange, with its previously missing framework/PBC comparison exposed as a separate lemma"
   }
  },
  {
   "text": "Apply [thm-cbc-qbar] to $J_XF$ in the PBC common-stage category. The hypotheses of its finite-stage theorem [thm-cbc-finite-extension] were checked in Step 3; these hypotheses impose relative separatedness of $f$, without absolute separatedness of $X,Y$. Its specified exchange $\\operatorname{Ex}^{\\mathrm{pbc}}$ is invertible. The equation in Step 3 expresses $J(\\operatorname{Ex}^{\\mathrm{sf}})=T^{-1}\\operatorname{Ex}^{\\mathrm{pbc}}J\\,S$, so the equivalence $J$ reflects invertibility and gives $v^*Rf_!F\\simeq Rf_{V!}u^*F$ for the framework functors. The comparison lemma also identifies their Weil structures. Explicitly, the two pastings of the open square with geometric Frobenius are the same square, because $V_0$ and the compactification are over $k_0$. Identity/pasting coherence of the specified exchange in [thm-cbc-finite-extension] makes the composites equal; compose this equation with the image of the Weil arrow of $F$. Naturality of $S,T$ under the semilinear diagram isomorphisms gives the same equality in the framework category. Hence this is an isomorphism of Weil complexes, using [def-weil-weil-sheaf-complex].",
   "uses": [
    "thm-cbc-qbar",
    "thm-cbc-finite-extension",
    "lem-zl-framework-pbc-open-exchange-comparison",
    "def-weil-weil-sheaf-complex"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "Common-stage base change and compatibility with the geometric-Frobenius square"
   }
  },
  {
   "text": "On the separated finite-type schemes of Step 2, the composition and properness laws of [prop-functor-package] give $Rf_{V!}\\simeq Rp_{V*}j_{V!}$. Clause (2) of [lem-zl-immersion-weil-local-behavior] identifies the open compact-support operation with the exact $j_{V!}$ on constructible Weil sheaves, without any assumption on a coefficient embedding. The finite direct image is standard-$t$-exact and exact on the constructible heart by [lem-zl-finite-adic-direct-image]. Consequently for every constructible Weil sheaf $A$ on $X_{V_0}$, $Rf_{V!}A\\simeq p_{V*}j_{V!}A$ is a sheaf in degree zero, and $A\\mapsto p_{V*}j_{V!}A$ is exact. Every invocation of these three statements is now on absolutely separated finite-type schemes, including $T_{V_0}$ and its geometric base change.",
   "uses": [
    "prop-functor-package",
    "lem-zl-immersion-weil-local-behavior",
    "lem-zl-finite-adic-direct-image"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "proof of (1), exactness after affine target restriction"
   }
  },
  {
   "text": "Restriction to $V$ commutes with cohomology and is exact on constructible hearts by [lem-a1-constructible-pullback-t-exact]. Steps 4 and 5 therefore show that every cohomology sheaf $\\mathcal H^i(Rf_!F)$ with $i\\ne0$ restricts to zero on each $V$. The open-cover exactness criterion in [lem-dl-a1-constructible-fibres-exact] detects its vanishing: apply it to the short complex $0\\to\\mathcal H^i(Rf_!F)\\to0$, which is exact on each member of this separated open cover. Thus $Rf_!F$ lies in the constructible heart, and in particular $R^if_{0!}F=0$ for $i>0$. For any short exact sequence of constructible Weil sheaves on $X_0$, restriction to $X_V$ is exact by the pullback statement. By Step 5 its direct-image sequence is exact over each $V$. Applying the same open-cover criterion to that sequence proves that $f_{0!}=R^0f_{0!}$ is an exact functor globally. These checks are on constructible adic sheaves, not arbitrary pro-etale sheaves.",
   "uses": [
    "lem-a1-constructible-pullback-t-exact",
    "lem-dl-a1-constructible-fibres-exact"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "proof of (1), local detection of vanishing and exactness on a possibly nonseparated target"
   }
  },
  {
   "text": "Fix the arbitrary field embedding $\\iota:\\Omega\\hookrightarrow\\mathbf C$ of [sk-d-dl-general-weights]; no surjectivity is assumed. Suppose $F$ has punctual upper bound $w$, or is punctually pure of weight $w$, in the eigenvalue sense spelled out there. Restrict to $X_{V_0}$. A closed point of this open is closed in $X_0$: on both finite-type schemes this means its residue field is finite over $k_0$ by [lem-kun-closed-point-field]. Its stalk and local Frobenius are unchanged. Clause (2) of [lem-zl-immersion-weil-local-behavior] says that $B=j_{V!}(F|_{X_V})$ has that identical stalk and local Frobenius on $X_{V_0}$, and zero stalk elsewhere in $T_{V_0}$. Thus $B$ has the same bound or purity for this very embedding $\\iota$. This uses the weight-free stalk assertion, not a weight-preservation theorem stated only for an isomorphism with $\\mathbf C$.",
   "uses": [
    "sk-d-dl-general-weights",
    "lem-kun-closed-point-field",
    "lem-zl-immersion-weil-local-behavior"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "Unit orbit argument: extension by zero for the given embedding"
   }
  },
  {
   "text": "Fix closed $y\\in V_0$, set $k_y=\\kappa(y)$, and put $Z_0=T_{V_0}\\times_{V_0}\\operatorname{Spec}k_y$. The natural finite-fibre formula of [lem-zl-finite-adic-direct-image] identifies $(p_{V*}B)_{\\bar y}$ with $H^0(Z,B|_Z)$, including its Frobenius action by the stated semilinear naturality. The fibre is finite, hence proper, so this is also $H_c^0$ by the properness law of [prop-functor-package]. Give $B|_Z$ the Weil arrow $\\theta_B^{[d_y]}$, where $d_y=[k_y:k_0]$, and apply [lem-a1-finite-weil-sections-decomposition] over $k_y$, with algebraic closure $k$. For $x\\in|Z_0|$, it gives a block of $e=[\\kappa(x):k_y]$ summands on which $F_y$ acts cyclically and $F_y^e$ on each summand is $F_x$. The same-residue-field case of [lem-fd-weil-pullback-local-frobenius] for $Z_0\\to T_{V_0}$ identifies its stalk operators over $k_0$. Over $k_y$, $e$ iterations of $\\theta_B^{[d_y]}$ give $\\theta_B^{[ed_y]}$, exactly the original $F_x$ of [def-weil-local-frobenius-trace]. The point $x$ is closed in $T_{V_0}$, and $q_x=q_y^e$ because a $k_y$-basis of the degree-$e$ residue extension identifies its underlying set with $k_y^e$. If $\\beta$ is an eigenvalue on this block, choose an eigenvector and a nonzero stalk component. The equation $F_y^ev=\\beta^ev$ on that component shows that $\\alpha=\\beta^e$ is an eigenvalue of $F_x$. For the bound, multiplicativity of the given embedding and the complex absolute value gives $|\\iota(\\beta)|^e=|\\iota(\\alpha)|\\le q_x^{w/2}=(q_y^{w/2})^e$. Taking the positive $e$-th root proves $|\\iota(\\beta)|\\le q_y^{w/2}$. For purity use equality throughout. This works for every real $w$ and uses no surjectivity of $\\iota$.",
   "uses": [
    "lem-zl-finite-adic-direct-image",
    "prop-functor-package",
    "lem-a1-finite-weil-sections-decomposition",
    "def-weil-local-frobenius-trace",
    "lem-weil-pbc-finite-morphism-permanence",
    "lem-fd-weil-pullback-local-frobenius"
   ],
   "elementary": false,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "Unit Frobenius orbit and normalized-weight sentences, computed for an arbitrary embedding"
   }
  },
  {
   "text": "By Steps 4 and 5, $p_{V*}B$ is the restriction of $f_{0!}F$ to $V_0$, as a Weil sheaf. Every closed point of $Y_0$ is in an affine $V_0$, with the same residue field, stalk and local Frobenius as on $Y_0$. Thus Steps 7 and 8 show that $f_{0!}$ preserves punctual upper bounds and punctual purity globally for the original arbitrary embedding. There is no assertion about descent of local mixed filtrations; the punctual predicates are exactly the closed-point eigenvalue inequalities/equalities of [sk-d-dl-general-weights].",
   "uses": [
    "sk-d-dl-general-weights"
   ],
   "elementary": true,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md",
    "place": "Unit purity conclusion after open-cover detection"
   }
  },
  {
   "text": "If $F$ is mixed of weights at most $w$, choose its global finite filtration $0=G_0\\subset\\cdots\\subset G_n=F$ with punctually pure quotients $Q_i$ of weights $u_i\\le w$, as in [sk-d-dl-general-weights]. Exactness from Step 6 sends each $0\\to G_{i-1}\\to G_i\\to Q_i\\to0$ to $0\\to f_{0!}G_{i-1}\\to f_{0!}G_i\\to f_{0!}Q_i\\to0$. Thus the inclusions give a finite filtration of $f_{0!}F$ with quotients $f_{0!}Q_i$. Step 9 shows that these quotients are punctually pure of the same $u_i$. This is exactly the mixed upper bound $w$ of [sk-d-dl-general-weights]. A zero quotient can be omitted. In particular this argument applies one global input filtration; it does not assume descent or uniqueness of independently chosen local mixed filtrations.",
   "uses": [
    "sk-d-dl-general-weights"
   ],
   "elementary": true,
   "source": {
    "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md",
    "place": "final mixed-filtration paragraph, using global exactness and purity established above"
   }
  }
 ],
 "proof_deps": [
  "def-weil-local-frobenius-trace",
  "def-weil-weil-sheaf-complex",
  "lem-a1-constructible-pullback-t-exact",
  "lem-a1-finite-weil-sections-decomposition",
  "lem-dl-a1-constructible-fibres-exact",
  "lem-fd-weil-pullback-local-frobenius",
  "lem-kun-closed-point-field",
  "lem-kun-dimension-finite-type",
  "lem-pod-separated-finite-type-base-change",
  "lem-weil-pbc-affine-opens-basis",
  "lem-weil-pbc-affine-source-morphism-separated",
  "lem-weil-pbc-finite-morphism-permanence",
  "lem-weil-pbc-finite-proper",
  "lem-weil-pbc-finite-type-over-noetherian",
  "lem-weil-pbc-noetherian-open-subscheme-noetherian",
  "lem-weil-pbc-open-immersion-base-change",
  "lem-zl-finite-adic-direct-image",
  "lem-zl-framework-pbc-open-exchange-comparison",
  "lem-zl-immersion-weil-local-behavior",
  "prop-functor-package",
  "sk-d-dl-general-weights",
  "thm-cbc-finite-extension",
  "thm-cbc-qbar",
  "thm-pqf-zmt-factorization"
 ],
 "proof_origin": {
  "by": "agent",
  "document": "literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/_section.md",
  "place": "Unit finite-fibre/base-change argument, expanded using its finite compactification proof and affine target restriction to repair absolute separatedness; no use of the disputed proof of lem-zl-quasi-finite"
 }
}
```

### Resolved-interface historical comparison

For the eight resolved interfaces, the returned immutable object and current shared mathematical record agree in statement, stmt_deps, proof, proof_deps, proof_origin, and source. The comparison is recorded per interface below. The relevant ordinary meanings were read in those statements: componentwise ordinary systems and K-flat coefficient operations (semilinear sections and system left extension); ordinary compact-support right adjoints and units/counits before Rlim (cartesian mates and finite adjunction diagrams); ordinary etale right adjoints transported to etale-origin constructible domains and their specified coefficient mates (finite coefficient adjoints, exceptional site mates and constructible adjunction coefficients); and supplied global compactification/qcqs base for finite-level base change. Their repair notes identify the old enhanced machinery and the replacements explicitly. The current item takes no conclusion from an old enhanced clause, and its new comparison does not require an unrestricted right adjoint on cartesian sections.

The following root-by-root computation records every direct dependency closure and its intersection with the exact manifest. Empty historical_changed_fields means all six mathematical fields above were equal; it does not claim the old pre-pivot proof was itself valid. The human's note supplies that earlier pre-pivot diagnosis.

```json
{
 "item": "sk-l-dl-general-quasifinite",
 "main": "78c79870a12cdd143a73794dc4fec0fc145ecc7b",
 "returned": "d219aca8d82c0187d60abeacc938997f45cecd5f",
 "manifest_sha256": "7dd4fe135c9ca7a82a5cf6e465aed469fb3b6b03726377b603953abee7baeacf",
 "manifest_entries": 1346,
 "roots": [
  {
   "node": "def-weil-integral-rational-qbar-compact-support",
   "closure_size": 10976,
   "dropped": []
  },
  {
   "node": "def-weil-local-frobenius-trace",
   "closure_size": 2486,
   "dropped": []
  },
  {
   "node": "def-weil-pbc-scheme-conventions",
   "closure_size": 57,
   "dropped": []
  },
  {
   "node": "def-weil-weil-sheaf-complex",
   "closure_size": 2442,
   "dropped": []
  },
  {
   "node": "lem-a1-constructible-pullback-t-exact",
   "closure_size": 2530,
   "dropped": []
  },
  {
   "node": "lem-a1-finite-weil-sections-decomposition",
   "closure_size": 12268,
   "dropped": []
  },
  {
   "node": "lem-dl-a1-constructible-fibres-exact",
   "closure_size": 14010,
   "dropped": []
  },
  {
   "node": "lem-fd-weil-pullback-local-frobenius",
   "closure_size": 14026,
   "dropped": []
  },
  {
   "node": "lem-kun-closed-point-field",
   "closure_size": 63,
   "dropped": []
  },
  {
   "node": "lem-kun-dimension-finite-type",
   "closure_size": 190,
   "dropped": []
  },
  {
   "node": "lem-pod-separated-finite-type-base-change",
   "closure_size": 100,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-affine-opens-basis",
   "closure_size": 3,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-affine-source-morphism-separated",
   "closure_size": 39,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-finite-morphism-permanence",
   "closure_size": 41,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-finite-proper",
   "closure_size": 58,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-finite-type-over-noetherian",
   "closure_size": 7,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-noetherian-open-subscheme-noetherian",
   "closure_size": 60,
   "dropped": []
  },
  {
   "node": "lem-weil-pbc-open-immersion-base-change",
   "closure_size": 4,
   "dropped": []
  },
  {
   "node": "lem-zl-finite-adic-direct-image",
   "closure_size": 11144,
   "dropped": []
  },
  {
   "node": "lem-zl-framework-pbc-open-exchange-comparison",
   "closure_size": 11090,
   "dropped": []
  },
  {
   "node": "lem-zl-immersion-weil-local-behavior",
   "closure_size": 11171,
   "dropped": []
  },
  {
   "node": "pqf-def-quasifinite",
   "closure_size": 58,
   "dropped": []
  },
  {
   "node": "prop-functor-package",
   "closure_size": 13999,
   "dropped": []
  },
  {
   "node": "sk-d-dl-general-weights",
   "closure_size": 14006,
   "dropped": []
  },
  {
   "node": "thm-cbc-finite-extension",
   "closure_size": 11439,
   "dropped": []
  },
  {
   "node": "thm-cbc-qbar",
   "closure_size": 11656,
   "dropped": []
  },
  {
   "node": "thm-pqf-zmt-factorization",
   "closure_size": 363,
   "dropped": []
  }
 ],
 "total_closure_size": 14134,
 "total_dropped": [],
 "applicable_notes": [
  {
   "node": "lem-coef-cartesian-section-adjoint-mates",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-coef-finite-adjunction-diagram-realization",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-coef-semilinear-derived-sections",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-kun-0f1f-gen",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-pod-coefficient-dual-perfect",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-pur-exceptional-mate-site-comparison",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-pur-finite-coefficient-adjoint-comparisons",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-pur-relative-regular-equations-base-change",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-pur-supported-product-localization",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-pur-system-level-left-extension",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-sf-constructible-exceptional-adjunction-coefficients",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "lem-trf-compact-frobenius-transport-composition",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-weil-pbc-integral-constructible-bounded-below-compactness",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "lem-weil-pbc-lisse-e-constructible-integral-lattice",
   "state": "withdrawn",
   "route": null
  },
  {
   "node": "thm-cbc-finite-level-proetale",
   "state": "resolved",
   "route": "ordinary derived (Brown / unique adjoints / K-flat / global compactification)",
   "historical_object_available": true,
   "historical_changed_fields": []
  },
  {
   "node": "thm-sf-hom-comparison-constructible",
   "state": "withdrawn",
   "route": null
  }
 ],
 "item_note": false
}
```


## Landing repair: current-DAG rebase, 2026-10-18

The returned delivery was approved mathematically but failed landing because the maintainer invocation named a nonexistent apply-fixes directory. I have not edited the launcher or attempted that maintainer operation. The required initial dry run of the retained sandbox exited successfully at `696364c681`; it fetched a current base and ran server preflight before any repair edits. The delivery command will build the revised overlay on its freshly fetched base again.

I compared the sandbox with returned head `875cbf575e3d0c13aabe1b76fe279a5cd2bd84a5` and the available current-main ref `ff7bd2474d8dd7d3047c2b4ef9c55d6d70f4305c`. The retained item was identical as parsed JSON to that returned head. I compared the current statement, statement dependencies, proof, proof dependencies, source, Mathlib match, status and merge destination of the 43 existing nodes directly cited by the item or the auxiliary statement. Historical objects were available for 32 of these nodes. Two had changed mathematical fields, both only additions to statement dependencies:

- `lem-dl-a1-constructible-fibres-exact` added `def-dl-a1-locally-constructible-adic-heart`, `def-weil-derived-pullback-tensor-hom`, and `def-wf-middle-extension`. I reopened its whole statement and all three added definitions. Its final sentence still permits checking exactness on a covering by separated finite-type opens of a locally finite-type scheme. The local-heart definition spells out cartesian restriction data and cocycles. Step 6 now explicitly verifies that the local objects are restrictions of the same global object and that their transition equations are the identity/pasting equations already supplied in Step 4. The middle-extension definition distinguishes ordinary from derived pushforward; this split uses neither a middle-extension assertion nor a replacement of derived direct image by underived image without the finite-image t-exactness theorem.
- `sk-d-dl-general-weights` added `def-zl-field-weil-shriek-shift-data`, `lem-a1-constructible-pullback-t-exact`, and `prop-constructible-truncations`. I reread its unchanged statement and the added shift-data and pullback statements; the latter explicitly includes its cohomology comparison. The weight definition still expressly allows an arbitrary field embedding and gives a global finite filtration with pure quotients. Steps 7–10 use those degree-zero clauses and require no additional shift or embedding hypothesis. The added shift datum explicitly allows nonseparated structure morphisms and presents the same normalized compact-support operation; it supplies no reason to reinstate the defective global-separatedness inference.

No available historical comparison changed any cited statement, proof, source, merge destination, status, or Mathlib match. For the eleven unavailable historical node objects I cannot assert byte identity against the returned commit: `def-kun-topological-krull-dimension`, `def-weil-compactifications-refinements`, `def-weil-pbc-scheme-conventions`, `def-weil-scheme-morphism-properties`, `lem-pod-separated-finite-type-base-change`, `lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-affine-source-morphism-separated`, `lem-weil-pbc-finite-proper`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lem-weil-pbc-open-immersion-base-change`. I read their current statements instead; they are the scheme conventions, compactification and dimension definitions and the geometric facts applied in Steps 1–3. Their conclusions and hypotheses still match those steps. The finite compactification is supplied, its restriction over an affine target is affine and separated, open base change remains open, and finite-type schemes over the fields in question are Noetherian and finite-dimensional. The current item is still imported and unreviewed, with the exact retained statement. The auxiliary id does not exist on current main. The unit differs from the retained sandbox only in its permitted realization fields.

## Review by Q03 — landing-repair supplement

I reread the current chapter and unit and the main-20261015 unit statement, the same-unit quasi-finite proof, its open-stalk weight paragraph, the finite-pushforward orbit proof, and the common-stage compact-support-exchange proof. These retain the same route and the same explicitly reported source error. I also reread the matching three source declarations in FormalSteps.lean:575–598; each proof is still sorry, so there is no attachment. The seventeen recorded Mathlib searches were reopened and their actual hits inspected in searches.jsonl; the statements and search questions have not changed, so no search was invented or repeated.

For Steps 1–2 I checked the qcqs target, finite compactification and separated affine-chart hypotheses. For Steps 3–4 I checked the coefficient-presentation endpoints and conjugacy equation against the auxiliary statement and the Noetherian, dimension and invertible-prime requirements against the PBC theorems. For Step 5 I checked that composition, properness, exact open extension and finite direct-image t-exactness are applied only on the separated charts. Step 6 has the explicit compatible-local-data check described above before the unchanged cover criterion. For Steps 7–9 I checked unchanged arbitrary-embedding weights, the weight-free stalk assertions, and the finite-Weil decomposition's actual equation relating orbit powers to local Frobenius. For Step 10 I checked that the one global input filtration is pushed through the global exact functor, rather than asserting gluing of independent local filtrations. The identity, empty-open, zero-sheaf, doubled-origin, nonreduced finite-fibre and degree-e Frobenius cases remain valid under these current interfaces.

All 32 citation entries are still literal substrings of current cited statements, and the citation set exactly matches every step's uses. The item has the union of those uses as proof_deps. The auxiliary lemma remains a single statement-only unsplit node with the same nine logged searches and no proof. After the Step 6 clarification, every step remains shorter than 2000 characters. The full current available dependency traversal reaches 13891 ids, with no intersection with the 1346-entry dropped-route manifest and no path from a direct dependency back to the item. The shared snapshot has thirteen unresolved transitive reference ids; the traversal records those as missing terminals, not as proved nodes. They are inherited current-DAG findings outside the delivered files, and the initial fresh-base server preflight passed. The server's final delta checks decide whether this repair introduces a finding. The old immutable F1 audit exhibits above are retained as historical evidence; this supplement gives the current audit rather than silently overwriting their historical counts.

The repair changes the item at Step 6 and in its split report, and adds this current-DAG review evidence. It preserves the exact target statement, previous source-error report, citations, auxiliary node, and all search records. I wrote only inside the designated sandbox, ran no git command in the shared repository, ran no compiler, changed no launcher files, and started no agents. The final dry run and push use only the required delivery command.
