# Stage-1 delivery: lem-pur-composition-model-orientation-descent

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-composition-model-orientation-descent.json: statement split into nine proof steps; no Mathlib match for the geometric statement.
- citations.json: 28 step/node pairs, each with a checked verbatim statement excerpt.
- report.md: this report.

No new DAG nodes and no new Mathlib leaves. The sandbox search log is retained; the scratch Python writer is not delivery material.

## Attachments

None. Searched the project source for the blueprint tag, orientation/descent and dualizing composition. In particular, Basic.lean's nonempty_iso_dualizingComplex_comp asserts existence of an isomorphism, not equality of the specified orientations and the zero-section and descent clauses. OrientationComparisonData.compIso defines a composite, without proving this equality. Neither is an attachment for this item.

## Wanted literature

None required for this split. The proof is marked agent-written: the current blueprint supplies its route, and the cited existing DAG statements supply the precise auxiliary interfaces. I did not claim that the blueprint's short uniqueness discussion itself proves the needed identifications.

## Findings and corrections

The item's statement and all its hypotheses are preserved. Its imported empty proof is replaced by the affine calculation, normal-coordinate substitution and degree-zero descent. No statement dispute was found.

The proof deliberately uses integration-normalized direct sums from cor-pur-vector-bundle-purity rather than assuming equality for arbitrary bundle trivializations. The ordinary-etale/pro-etale passage cites both the actual integration/projection/transpose comparison and the compositor equation, then mate pasting. The all-n extension comes from the already specified ordered integration maps; the restricted original affine-line comparison is not applied outside its divisibility domain.

I read the current blueprint composition proof and model-agreement proof. The latter's opening appeal to composition coherence cannot be reused to prove this item, because the parent coherence theorem depends on this item. Instead I cite the existing model-agreement node, whose current split uses the independent coefficient-counit, affine-diagonal and ordered-integration nodes. I checked dependency reachability: the vector direct-sum theorem, integration comparison, site coherence, mate pasting, degree-zero gluing, ordered-integration and coefficient-normalization nodes have no dependency path back to this item.

## Not duplicates

No new nodes. Whole-blueprint searches for orientation and composition, and DAG searches for affine ordered integration, degree-zero gluing, Tate-line freeness and direct-sum compatibility, found the existing interfaces reused here.

## Review by Q15

I read the current main-20261015 thm-pur-composition-coherence.proof.md, both steps, against the unit's diagonal/DNC and tangent-bundle route. I also read cor-pur-vector-bundle-purity.proof.md and lem-pur-projection-purity-agreement.proof.md. For the descent source I read Stacks derived.tex lemma-negative-exts (Tag 06XS), sites-modules.tex lemma-internal-hom (03EM), and sites.tex lemma-glue-maps (04TQ). These distinguish degree-zero Hom detection from a false unrestricted derived-morphism descent assertion. There are no new nodes requiring separate source verification.

Step 1 uses the actual tensor-power twist definition, finite Tate-line freeness, monoidal pullback comparison, Tate pullback, derived pullback compositor, and eight-factor composition definition. I opened each statement. They give exactly these operations; concatenation and the even sign are written out. The sheaf is finite coefficient, so the ordinary rank-one tensor powers compute derived ones. Exponent zero uses the coefficient unit.

Step 2 uses the ordered-integration theorem's actual equality P=Gamma and coefficient normalization's theta(1 tensor P)=P_K, both stated for arbitrary n>=1. Model agreement identifies these specified maps with the diagonal map. The tensor-mate statement supplies the finite-Tor domain for the intervening exceptional coefficient omega_g. The bases used here are affine finite type, so the separated-scheme hypotheses of the independent model nodes are met. No flatness over Z/ell^r or divisibility of n is assumed.

Step 3 uses the vector theorem's explicit independently normalized direct-sum equation on two trivial bundles. I checked that its q-map is obtained by base change from the first bundle, and that its compactification mate is the one in this item. The integration comparison states equality of the actual traces, projection maps and exceptional transposes; site coherence gives the compositor equation. The generic mate-pasting statement transfers that equation to right mates. It is not enough merely to identify their source and target objects.

Step 4 substitutes theta(1 tensor G)=Gamma into that equation. The tensor-mate node defines sigma with the displayed symmetry; cancellation of the invertible G maps gives the claimed affine identity. The ordered comparison definition fixes Gamma at rank zero, and the identity-mate clause supplies its comparison identity. This is a calculation, not a new lemma disguised as a clause.

Step 5 applies exact monoidal zero-section pullback. The chart statement explicitly defines nu as the pullback of this sigma with the specified base-change comparisons. The vector theorem states base-change compatibility; the integration comparison explicitly says its inverse is the bundle identification in that theorem. These are sufficient to identify beta with b, and not merely to assert existence of some basis for the normal bundle. The monoidal pullback node supplies the tensor identification. Step 6 then uses the chart statement's actual normalized equation delta_gf kappa=nu(delta_f tensor f*delta_g). The three lines of substitution are displayed. I checked its local separatedness hypotheses instead of assuming that the original global schemes are separated over k.

Step 7 uses precisely the two equations theta=beta delta alpha^-1 and alpha_gf kappa=sigma(alpha_f tensor f*alpha_g) from that same chart statement. Cancelling the tensor of alpha maps gives equality on the covering charts. Its statement includes compatibility with further open restrictions, so these are restrictions of the global arrows.

Step 8 uses only finite Tate-line freeness, the twist definition, and degree-zero derived-map gluing. Removing the common shift yields L[0]; the gluing node permits any scheme and a set-indexed Zariski open cover, with no global separatedness requirement. Its concentration hypothesis is automatic for this degree-zero sheaf. Shifting back proves injection on Aut(T_X). Step 9 applies it to AB^-1; the tensor-mate statement supplies isomorphy of sigma. The gluing statement explicitly includes empty schemes and the empty cover, which verifies the final edge case without choosing a geometric point.

I checked delivery-errors B through E: no new statements, no elementary auxiliary nodes, no duplicate or clause-only nodes, no hidden proof dependencies, and one verbatim quote for each cited step/node pair. No proof step exceeds 2000 characters. Edge cases checked are d=0, e=0, d=e=0, n=1 including ramified E where the old divisibility restriction fails, disconnected bases, empty B/X, and non-separated global schemes with separated affine chart restrictions. All off-unit generic tools are declared in split_report.tool_uses with their role; no top-level tool_uses field is added.

## Unfinished work

None in the one-level split. Existing auxiliary nodes may themselves remain unsplit, as the stage-1 protocol permits.
