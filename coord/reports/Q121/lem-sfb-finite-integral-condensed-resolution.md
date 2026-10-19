# Stage-1 worker report: lem-sfb-finite-integral-condensed-resolution

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-integral-condensed-resolution.json`: statement node, split in ten steps; no whole-item Mathlib match. Its statement and statement dependencies are unchanged. Existing searches were retained and five actually executed searches were added.
- `citations.json`: verbatim statement extracts for all four step/node citation pairs.
- No new DAG nodes and no new Mathlib leaves. `write_split.py` is sandbox-only scratch work.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for finite integral/condensed resolution terminology found no declaration stating this item. Master source is reference material only; no master sorry was treated as a proof.

## WANTED

None for this split. The DVR arithmetic is an existing cited node, rather than an unproved fact imported from a new external source.

## Problems found and changes

The item was an unsplit statement with no proof. I retained the original statement, source, ancestry, previous searches, and maintainer metadata, and supplied the missing argument. In particular, algebraic kernel freeness by itself does not give either the equality of the two ranks or the topology on the kernel; steps 3, 5, and 6 prove these points explicitly.

The existing Mathlib leaf `lem-sc-dvr-saturation-line-smith-normal-form` labels its Stacks source as Tag 00PD, "PID structure theorem". Reading `literature/stacks-project/tags/tags` shows 00PD is `algebra-lemma-characterize-dvr`, not the Smith normal form theorem. I did not change this other worker's node. I read the leaf's actual Mathlib declaration, `Submodule.exists_smith_normal_form_of_le`, in `Mathlib/LinearAlgebra/FreeModule/PID.lean:492-510`; it supplies precisely the simultaneous bases and diagonal inclusion used here. The split step cites that exact source instead of repeating the erroneous Stacks description. Stacks `algebra.tex`, Example `example-K0-PID`, mentions the PID module structure theorem but is not being used as a proof of Smith normal form.

No statement dispute, source-route departure, or unit change is needed. This is the elementary-map finite-integral bullet of the parent's proof, and unit `sk-prop-scalar-six`, step 4, exactly as prescribed.

## Unfinished work

None in this one-level split. The one generic non-Mathlib arithmetic tool is declared in `split_report.tool_uses`: `lem-weil-l-adic-extension-integers-dvr`. It states the DVR fact needed for the Smith normal form application; the scalar-comparison unit has no arithmetic replacement for that input.

## Not duplicates

No nodes were created. Whole-DAG searches located the existing Smith normal form and DVR nodes, and these are reused. Blueprint searches for "finite free resolution", "finite integral", "two-term", and "condensed" found no other blueprint statement giving this full assertion for every finite continuous O_E-algebra. In particular `det-pe-derived-nakayama-resolution` concerns the single quotient O_E/pi_E^n after pullback to a scheme, whereas this item treats an arbitrary finite algebra, the kernel's topology, and exactness on every profinite test set. The standard-quotients-perfect node only treats Z_l/l^n. The continuous-finite-free-kernel-model node concerns a different adjunction over a scheme and does not state the present finite quotient result.

## Review by Q121

I read the chapter record `sec-six-functors-basics`, unit `sk-prop-scalar-six`, the item's statement, and the finite-free/finitely-presented coefficient paragraph and second bullet of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`. That bullet first constructs the length-one finite free resolution and then lifts maps into the finite discrete quotient on clopen partitions. The ten steps below carry exactly that route. The extra topological assertions of the item are proved for the valuation topology and the subspace topology that it specifies, rather than for an abstract topology on a free module.

Steps 1-3 are direct constructions. The zero ring is handled separately with rank zero; otherwise taking all elements of A as generators makes the surjection explicit. Each summand defining q is continuous by the assumed continuity of a and discreteness of A. To avoid using an unstated torsion or rank theorem, step 3 uses the pigeonhole argument on 0,b,...,Nb to prove N!A=0. The element N! is nonzero in O because E extends the characteristic-zero field Q_l. Neither finiteness of the residue field nor any flatness hypothesis on A is assumed.

For step 4 I opened and read the complete statements of `lem-weil-l-adic-extension-integers-dvr` and `lem-sc-dvr-saturation-line-smith-normal-form`. The former explicitly gives that this O is a PID domain; its finite-extension and extending-absolute-value hypotheses are exactly the datum in the item. The latter allows every submodule of a finite free module, with no finite-generation hypothesis on the submodule, and supplies bases of both the ambient module and its submodule with a diagonal inclusion and at most r kernel basis vectors. Thus it applies to K=ker(q), not merely to an already-free kernel. I also read the actual Mathlib declaration at lines 492-510 to check the claimed Mathlib interface. This is the only non-elementary proof step. Step 5 does not invoke an unmentioned rank computation: a missing ambient basis coordinate of K contradicts c u_j in K with c nonzero. Its resulting basis gives both exactness and an O-matrix phi.

Step 6 explicitly proves the topological point. The ambient basis map P and its inverse are O-matrices and are continuous by finite sums and products. On K the inverse coordinates are (P^{-1}y)_i/d_i in E. The d_i are nonzero by independence of the kernel basis, so the displayed absolute-value identity proves continuity under multiplication by their inverses. The coordinates take values in O, and continuity into that subspace follows by taking preimages of intersections with open subsets of E. Consequently the inverse really has the requested subspace topology. No compactness-to-homeomorphism theorem, comparison of inequivalent module topologies, or unproved determinant lemma is hidden here.

Steps 7 and 8 prove the two sectionwise assertions directly. The inverse just constructed lifts every kernel section continuously and uniquely. A lift t_b of each element of A yields a piecewise constant lift on the finite clopen partition given by a continuous map f:S to A; the explicit inverse-image formula proves continuity, including empty fibres and S empty. This requires no projectivity of the profinite set and no continuous O-linear splitting of q.

For step 9 I opened `sk-def-sfb-condensed-ring` and `sk-def-sfb-module-objects`. Their statements respectively define the sheaves by C(S,T) and the action-compatible module-object morphisms. Those are exactly what step 9 takes from them, as the copied extracts in citations.json show. Finite direct sums are identified by writing their coordinate injections, projections, and their sum identity; no assertion about arbitrary infinite sums is used. Step 10 supplies kernel and cokernel universal properties explicitly: uniqueness gives naturality of kernel lifts, and two lifts of a quotient section differ by an image section, so factoring an arbitrary morphism annihilating phi is well defined, linear, natural, and unique. This avoids assuming that evaluation is exact for arbitrary condensed short exact sequences; only the sectionwise surjectivity already proved for this particular sequence is used.

I tested the construction for A=0, A=O/pi^n, and a noncyclic finite O-algebra such as F_l[epsilon]/(epsilon^2) with O=Z_l. The construction uses all elements as generators, so no cyclicity or reducedness assumption enters. The finite target can have nilpotents; the proof uses only its additive finiteness and the supplied continuous O-action. The empty profinite test set gives singleton section groups and is covered throughout. In the zero case phi:0 to ker(q)=0 is indeed a homeomorphism.

I checked B-E against the actual files: no new unsplit statements, duplicate nodes, clause restatements, SGA sources, missing definition changes, or new-node search claims occur. Every citation uses the cited node's statement, with verbatim quotes. The proof dependency list is exactly the union of the step uses. The only off-unit non-Mathlib statement is the declared local-field tool; Smith normal form is already a Mathlib leaf. All proof steps are shorter than 2000 characters (the non-elementary step is 516 characters); the explicit elementary arguments introduce no separate hidden lemma. Search results were read: free/torsion-free PID facts supply algebraic ingredients only, Condensed.finFree concerns the free condensed module functor for an ordinary coefficient ring, the AB results concern colimits/limits, and the Nobeling results concern locally constant integer functions. None asserts the topological finite integral resolution in this item. The previous item searches and the new searches are retained without inventing a query or misreporting an unavailable service.
