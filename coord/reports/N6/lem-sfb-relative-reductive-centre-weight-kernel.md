# N6 stage-1 delivery: lem-sfb-relative-reductive-centre-weight-kernel

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-reductive-centre-weight-kernel.json`: statement, split into nine proof steps; unchanged statement and statement dependencies; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-diagonalizable-centralizer-smooth.json`: new statement-only supporting theorem; unsplit, no Mathlib match.
- `citations.json`: one verbatim statement quote for every use in the item's steps.
- `searches.jsonl`: actual msearch output records, retained in the sandbox.
- `write_split.py`: sandbox-only drafting script; not part of the delivery.

One new node, zero Mathlib leaves. No Lean written or compiler run. No repository or launcher file changed.

## Attachments

None. I searched the project source under `lean/WeilConjectures/` by the item id, reductive, centre/center, centralizer and maximal torus. The project has characteristic-zero matrix-group centre comparison results, but no declaration states the relative reductive-group result over an arbitrary Noetherian base. Existing abstract Lie-algebra kernel results and the special-linear-group centre are not the required statement. I also searched for the new centralizer statement; no project declaration supplies it.

## Wanted literature

WANTED: Brian Conrad, *Reductive group schemes*, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Theorem 3.3.4 (printed pp.98--100), Corollary 3.3.6(1) (printed p.101), Example 5.1.7 (printed p.138), and Lemma 2.2.4 with its proof (printed pp.64--66), for the item and lem-sfb-split-diagonalizable-centralizer-smooth; desired local filename `literature/conrad-reductive-group-schemes.pdf`.

I read these places in the online PDF. The requested local document is absent from the listed literature, and I did not download it. The item's `proof_origin.by` is therefore `agent`, following the brief's rule for locally unavailable documents. No SGA source was used. No Stacks tag states the reductive-centre or general diagonalizable-centralizer structural theorem; the new node cites Conrad explicitly rather than assigning it a misleading tag.

## What was wrong or incomplete

The item was a new unsplit statement with no proof. Its statement is correct; there is no statement dispute and no weakening. The important missing input is smoothness of the centralizer of a multiplicative-type subgroup that need not itself be smooth. The existing relative centralizer node covers a split torus, which does not include, for example, a characteristic-p kernel with a mu_p factor. The existing Lie-invariants node is only over algebraically closed fields. I have not treated either as though it stated the more general relative fact.

The replacement for the source's fibral isomorphism invocation is explicit: on geometric fibres a tangent isomorphism between smooth schemes is etale, a closed etale immersion is open, and connectedness makes it surjective. Then descend the geometric-fibre isomorphisms to the residue fields, apply the existing fibrewise-flatness criterion, and use the existing surjective flat closed-immersion theorem. This avoids hiding a separate general fibral-isomorphism theorem in the proof.

The ancestry tool prints `blueprint.from.node = None` for a node created for this item. I retained that live metadata, appended the item to `via` for the new node, and specified the precise supporting use in `from.place`. Searches of the whole imported blueprint for reductive, diagonalizable, centralizer, centre and multiplicative type found no statement of this theorem or the new one. The centralizer hits are characteristic-zero algebraic-group material, not the relative theorem. I read the latest `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof, as well as the recorded chapter and unit. The inherited long chain supplies an alteration input to direct images; this delivery works below that route and changes no unit or chapter.

## Mathlib searches

All newly recorded queries were actually run with the prescribed `batch2/msearch.py N6 lem-sfb-relative-reductive-centre-weight-kernel` command. `searches.jsonl` contains the original answers, tools, queries, time stamps and digests. The old searches in the live item were retained; they were not misrepresented as fresh searches.

For the item I ran semantic searches for the maximal-torus adjoint character kernel and, with a second phrasing, faithfulness of the torus action modulo the centre; LeanSearch for the flat multiplicative-type centre with arbitrary base change; Loogle for `AlgebraicGeometry.GroupScheme`; and the grep pattern `reductive|centralizer|multiplicative.type` in AlgebraicGeometry. The semantic hits give `LieDerivation.ad_ker_eq_center`, `LieAlgebra.self_module_ker_eq_center`, abstract centres and `SpecialLinearGroup.centerEquivRootsOfUnity`. Their displayed signatures concern Lie algebras or one matrix group, not this relative theorem. LeanSearch's flat-morphism instances state preservation of flatness rather than representability or identification of the centre. The grep found no hit. Loogle reports an unknown identifier, recorded as a successful request with no relevant match, not an invented theorem.

For the new node I ran LeanFinder for the fixed scheme of a diagonalizable action and its tangent invariants, then a second phrasing using a finite abelian character grading of a smooth algebra; LeanSearch for smooth centralizers of multiplicative-type subgroups; Loogle queries `IsSmooth, Scheme` and `AlgebraicGeometry.IsSmooth`; grep `diagonalizable|fixedPoint|fixed.point|centralizer` in AlgebraicGeometry and `diagonalizable|centralizer|fixed.point` in RepresentationTheory. The semantic hits concern ordinary smooth algebras, abstract representation invariants or abstract subgroup centralizers. They do not give a scheme centralizer, its smoothness, its tangent comparison and arbitrary base change. The Loogle requests returned unknown identifiers, and both grep requests returned no hits. No service was unavailable. The node records the actual queries and the actual returned summaries. None is a Mathlib leaf.

## Not duplicates

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-relative-torus-centralizer-normalizer: the old node assumes the subgroup is a split torus; the new node permits any finitely generated character group, including torsion and nonreduced diagonalizable subgroups. It asserts no normalizer result.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-mu-n-fixed-subgroup-smooth: the old node treats the fixed subgroup of mu_n for an action extended to G_m; the new node treats a general embedded split diagonalizable subgroup, with no such extension hypothesis, and includes the relative Lie-invariants identification.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-lie-normalizer-centralizer-invariants: the old node works over an algebraically closed field and assumes representability; it neither proves relative centralizer representability nor smoothness over a ring.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-torus-fixed-scheme-smooth: the old node is over a field and assumes a torus, excluding torsion character groups and general base rings.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-linearly-reductive-dense-fixed-smooth: the old node assumes an algebraically closed field, a smooth acting group and a dense subgroup of rational points; those hypotheses do not cover mu_p over characteristic p.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-reductive-torus-self-centralizer: the old node assumes reductivity and a maximal torus over a field and identifies that torus centralizer; the new node applies to any smooth affine group over a Noetherian ring and an arbitrary split diagonalizable subgroup, with no claim that the centralizer equals that subgroup.

lem-sfb-split-diagonalizable-centralizer-smooth vs lem-sfb-relative-reductive-centre-weight-kernel: the new node has no reductivity, maximal torus, centre or character-kernel conclusion. The item's construction, proof of centrality, converse containment, descent and constant-support formula are all proved in its own steps.

These comparisons came from the whole-DAG keyword and source-place searches (including Lemma 2.2.4, Theorem 3.3.4, Corollary 3.3.6 and Example 5.1.7), followed by opening the relevant statements. No duplicate Stacks-tag pair is created: the new theorem has no Stacks-tag source.

## Review by N6

I read Conrad's weight-decomposition construction in Theorem 3.3.4, the adjoint-kernel interpretation in Corollary 3.3.6(1), and the character quotient example. I read Lemma 2.2.4 for the new node, including its torsion/non-smooth subgroup case, rather than inferring it from the torus-only node. I also read the local Stacks descent source at `lemma-affine` (0245), `lemma-fpqc-universal-effective-epimorphisms` (023Q), `lemma-descending-property-affine` (02L5), `lemma-descending-property-closed-immersion` (02L6), and `lemma-descending-property-flat` (02L2), and checked the tag mapping. These are the tools used for descent, not sources for the reductive-group assertion.

Step 1 uses the statement of the geometric Borel-pair node only for existence of a geometric maximal torus, the geometric-torus fppf lifting node for its inclusion, and the reductive-torus openness node for preserving maximality near the chosen lift. Flat-lfp openness and affine quasi-compactness yield a finite covering; the coproduct statement supplies its scheme, and the finite-product ring construction shows it is affine. Finite-type algebras over Noetherian rings are Noetherian, and finite type over such a ring is finitely presented, exactly as the two cited algebra statements assert. The cited base-change theorem is used only in its smoothness clause. This checks the Noetherian and finite-presentation hypotheses needed later without adding hypotheses to the item.

Step 2 takes finite projective Lie weight summands and arbitrary base change from the tangent-weight statement, takes local constancy of all finitely many ranks from the torus-bundle-weight statement, and takes local freeness from the finite-projective localization statement. Each of those is stated for rings and full coactions. The argument never replaces a torus character by its differential. Zariski refinements can again be made finite by the stated affine quasi-compactness.

Step 3 applies the existing relative character-duality statement to the explicit homomorphism from the free group on Phi to M. That statement actually gives the kernel as the character cokernel and arbitrary base change. Flatness is proved from the displayed group-algebra basis, so no unproved assertion that all subgroup schemes of a torus are flat is inserted. The affine-flatness dictionary then gives scheme flatness. On locally free positive-rank summands the equation for a scalar identity follows by applying it to a basis vector; it holds over nonreduced test rings as well. The tangent-base-change citation is precisely what identifies these weight modules after extending the ring.

Step 4 uses the new node for smooth representability, arbitrary base change and the Lie-invariants statement for H, not the torus-only theorem. Both schemes in the geometric tangent comparison are smooth and finite type; translating the identity calculation covers every rational point of C. The tangent-etale and closed-etale-open statements have exactly these hypotheses. Connectedness of the target, not of the centralizer, makes its nonempty clopen image the whole fibre. I explicitly corrected the draft to descend the geometric-fibre isomorphism to the residue-field fibre with the existing fpqc isomorphism statement. For the fibrewise-flatness criterion the source is smooth, hence flat and locally finitely presented, and the target is locally finite type. The resulting immersion is flat and fibrewise surjective, so the cited surjective-flat-closed-immersion statement applies. This does not infer scheme equality from a bare equality of geometric points.

Step 5 repeats only the final fibrewise-flatness argument for T inside C_G(T). The new node also applies with N free. The field self-centralizer node asserts equality on nonreduced test algebras, not merely equality of rational points. Its geometric-fibre equality descends by the explicitly cited fpqc isomorphism theorem. The inclusion T into C_G(T) is closed by the stated quotient-ideal argument; smoothness gives the flatness and presentation assumptions for the existing criterion. These facts justify the relative equality and all of its base changes.

Step 6 is elementary assembly of the conclusions already proved in steps 3--5. A central point lies in the torus because it centralizes that torus, and differentiating its identity conjugation automorphism makes it lie in H. Centrality gives the converse. Quantifying over every algebra extension is retained in both directions, so arbitrary base change is established before descent. This step invokes no additional theorem.

Step 7 uses actual affine effectivity, then the separate fpqc descent-of-affineness statement: the effectivity node alone does not assert an affine descended object. It uses the morphism-descent node for the inclusion, group operations and diagram equalities, and the closed-immersion descent node over the base-changed cover of G. The covering-axioms statement supplies that base change. The local overlap identifications are the unique identifications of representatives of the centre subfunctor, which is why their cocycle identity holds; no unproved compatibility is invoked.

Step 8 uses the flatness-descent statement for flatness and the covering-base-change clause for arbitrary S'. Morphism descent glues the local factorizations of a central section uniquely. The property of being of multiplicative type is exactly the fppf-local definition in the item, applied to the constructed D(M/L), so no further structural theorem is hidden there. The local proof already works for arbitrary algebras B over the original Noetherian patches; the new base need not be Noetherian.

Step 9 uses the definition of a torus to trivialize the given maximal torus and the previously proved construction to identify its kernel with the centre. Morphism descent makes these local equalities global. For a globally split torus with the fixed support Phi, the tangent-weight theorem and finite-projective rank statement identify which summands vanish and which have positive rank everywhere. The local-freeness statement and the explicit scalar calculation then give the same character equations globally. The character-duality statement supplies D(M/ZPhi), with its stated arbitrary-base-change compatibility. No trivialization of root lines or connectedness of the base was assumed.

I tested the empty weight set (a torus, with centre T), rank zero (the trivial reductive group), disconnected Noetherian bases (rank refinements taken separately on their open components), and SL_p in characteristic p, whose centre mu_p is nonreduced. The last test is the reason the new centralizer node permits torsion character groups and the argument uses the full coaction. For the new statement, K=1 gives centralizer G and all Lie invariants, and K=mu_p in a torus gives the whole torus; these are consistent. The smoothness assertion applies to the centralizer, not to K or the centre.

Every citation quote in `citations.json` was copied from the cited node's statement. I opened all proof-input statements and checked their hypotheses and conclusions against the uses just described. I checked dependency reachability for cycles through the item before choosing the inputs. Every step is shorter than 2000 characters; the source's centralizer and fibrewise-isomorphism reasoning is distributed among steps 4--6 instead of being hidden in a long sentence. The one new lemma is not a clause of the item and is left statement-only. Off-unit generic tools are declared in `split_report.tool_uses`, not in a maintainer-owned node field.

The server-only `srvcheck.py` invocations of `review_split` and `check_dag` both exited successfully on the draft. The full deliver.py dry run below is still required after this report and any final corrections.

## Supporting proof plan for the new unsplit node

This is planning material for the next worker, not a proof in the unsplit node. Conrad's Lemma 2.2.4 gives the general representability and smoothness theorem. In the split case one can also express conjugation by D_R(N) as an N-grading of the affine coordinate algebra and cut out the fixed scheme by the ideal of all nonzero-degree pieces. Finite homogeneous generators make this ideal finitely generated; no reducedness assumption is used. For a square-zero lifting problem first lift to the smooth original algebra, then take its degree-zero component. The discarded components map into the square-zero ideal, so products of opposite discarded degrees vanish; this proves that the projected lift is multiplicative. The resulting finite-presentation lifting criterion gives smoothness. The defining equations show arbitrary base change, and evaluating them on dual-number points identifies the tangent kernel with full group invariants. This is the arbitrary-character-group version of the calculation already present in the existing mu_n fixed-subgroup proof, but it must be stated and proved with this generality. It is not licensed by that narrower statement alone.

## Unfinished work

No gap is left in the item's split. The new structural theorem is deliberately unsplit for a future stage-1 worker. The maintainer's independent review and the local acquisition of Conrad remain outside this delivery.
