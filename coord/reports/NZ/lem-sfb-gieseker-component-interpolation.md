# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-gieseker-component-interpolation.json: statement, split; the original statement and inherited metadata are retained. Nine proof steps, no new nodes and no Mathlib leaves.
- citations.json: one verbatim statement quotation for every citation in every proof step.
- searches.jsonl: actual msearch.py invocations and results, including searches for proposed auxiliary nodes that were not created after existing statements were found.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id, Gieseker/gieseker, component interpolation, genus zero, and degree-one curve statements. No declaration states this item. The existing genus-zero projective-line node is reused as a DAG citation, not claimed as a Lean attachment.

## Literature wanted

WANTED: Ian Morrison, GIT Constructions of Moduli Spaces of Stable Curves and Maps, arXiv:0810.2340, Section 3.2 Theorem 8 proof step (9), printed p.14, for lem-sfb-gieseker-component-interpolation. Read https://arxiv.org/pdf/0810.2340 and https://arxiv.org/html/0810.2340 online. Local PDF absent.

WANTED: David Gieseker, Lectures on Moduli of Curves, TIFR 69 (1982), Proposition 1.0.7 printed pp.55--61 and the argument after Proposition 1.0.9 printed pp.64--65, for lem-sfb-gieseker-component-interpolation. Read the primary text reproduced at https://doczz.net/doc/7664568/lectures-on-moduli-of-curves---school-of-mathematics--tifr (transcription lines 3194--3555 and 3699--3832). The publisher PDF links returned 404, hostname certificate mismatch, or cache misses; no literature was downloaded or changed. The proof is explicitly agent-origin because these documents are absent locally and the leading-coefficient adaptation is reconstructed.

## Problems found and repaired

The unsplit item had no proof and Morrison merely lists step (9), referring the reader to Gieseker or Harris--Morrison for details. The existing parent split needs this estimate before its own subcurve inequality, while the existing span-weight statement assumes a degree-versus-boundary condition. Citing the parent or assuming that condition would be circular. I instead used only the first, degree-bounded alternative of the span-weight statement, inside a maximal violating subcurve argument. That proves the subcurve inequality here without assuming the result of this item. It follows Gieseker's printed pp.64--65 argument in a nonspecial, leading-weight setting; its arithmetic is simpler because no finite-m error remains.

No statement dispute is needed: the conclusion is true, and the proof obtains the stronger restriction that a component of insufficient degree must have degree one and two total attachments. This is sufficient for the unchanged rational-normal alternative. The source's original numerical hypothesis d >= 20(g-1) is not silently substituted: the proof explicitly uses epsilon=(g-1)/d<1/9 and verifies all inequalities for that range.

The ancestor command prints blueprint.from.node=None. I retain that inherited value and via list, as the direct-delivery tool preserves maintainer metadata. The current latest direct-images proof has the same det-thm-sf-ctf-stability-direct-images identifier and its step (3) is the inherited route's entry. I read its current proof, the unit and chapter records, and latest chapter/unit files. This supporting algebraic-geometry argument changes none of their routes.

## Not duplicates

No new nodes. DAG and whole-blueprint searches for component interpolation, rational normal, subcurve, genus zero, genus-zero, positive degree, degree one, and tags 0C6T/0C6U found no duplicate statement for the item. Searching the tags exposed lem-trf-pointed-genus-zero-projective-line, which is used rather than creating another characterization. The proposed general positive-degree genus-zero lemma was unnecessary; it was never created. The existing subcurve-span-weight-bound is used as stated, with every complementary component satisfying its first alternative at the point of application.

## Review by NZ

I read Morrison's Theorem 8 hypotheses, its ordered proof list, and Definition 7's subcurve inequality, and Gieseker's Proposition 1.0.7 and the maximal violating subcurve argument on pp.64--65. I also read Stacks curves.tex lemma-genus-zero-positive-degree (Tag 0C6T) and proposition-projective-line (0C6U), coherent.tex lemma-relative-affine-cohomology (089W) and lemma-coherent-abelian-Noetherian (01Y0), cohomology.tex proposition-vanishing-Noetherian (02UZ), and varieties.tex lemma-prepare-delta-invariant (0C1R), lemma-chi-tensor-finite (0AYT), and lemma-ampleness-in-terms-of-degrees-components (0B5Y). There are no new nodes requiring a separate source audit.

For step 1 I opened all six cited statements: projective implies proper; finite type over Noetherian gives Noetherian; reduced proper curve normalization gives finite component list and smooth proper normalizations; the nodal-boundary lemma gives distinct smooth boundary branches; the ample definition applies via standard affine hyperplane opens; the degree criterion gives positive normalized component degrees. All these hypotheses hold for the given nodal embedded curve. No smoothness of the original irreducible component is assumed.

For step 2 I read the closed-immersion cohomology statement, coherent kernel/cokernel statement, dimension vanishing, the long exact cohomology definition, and coherent finiteness. Their actual statements give every fact used. The kernel is coherent on the Noetherian one-dimensional D; H2 is zero, so global H1(L)=0 forces H1 on any reduced union to vanish. The union need not be connected. Finite-dimensionality holds because every union is proper over the field. These are module-sheaf Zariski cohomology statements throughout.

For step 3 I read the full normalization quotient, zero-dimensional Euler invariance, Euler additivity, affine cohomology edge and degree-definition statements. The normalization is finite, so its cohomology comparison applies. Tensoring by an invertible module is locally tensoring by a rank-one free module, an elementary exact operation. The middle term is identified in line-bundle trivializations, and the quotient Euler characteristic is invariant by the cited statement. This proves the relation between normalized and intrinsic degree instead of assuming it. Summing separately over connected components covers disconnected unions.

For step 4 the global-functions statement requires proper, connected, reduced curves; an irreducible reduced component has these properties. Dimension vanishing and the nodal Euler formula give exactly chi(T)=1-p_T and chi(A union T)=chi(A)+1-p_T-ell. The Euler statement explicitly counts self-nodes once. I wrote the boundary-edge count, with u denoting attachments outside the enlarged union. This is elementary arithmetic on the cited formulas.

For step 5 I read the projective Hilbert-polynomial comparison: its statement gives equality with chi for every integer m, not merely large m. Thus m=0,1 and the degree calculation legitimately give total normalized degree d. The empty and full unions have zero defect. Maximality is in a finite set, not an unsupported induction.

For step 6 I reopened lem-sfb-subcurve-span-weight-bound and checked each hypothesis: X=D is connected, reduced, nondegenerate, one-dimensional and nodal; A is nonempty proper and may be disconnected; all boundary preimages are distinct; all component degrees are positive. If every degree bounds its selected boundary count, the first alternative holds on every component. Only then is the statement applied. The resulting flag uses weights zero and one, within the allowed weight set, and its sum of weights is the quotient dimension s. Combining the actual lower and upper bounds proves nonnegative defect. Otherwise some component has e<ell. No conclusion of the current item is invoked.

For step 7 I independently recomputed the defect difference: epsilon*e+1-p-(1-q/2)*ell-q*u/2. With e<=ell-1 it is at most q*(1-(ell+u)/2)-p<=0, whereas maximality makes it strictly positive. This supplies the argument itself; it is not outsourced to a new node restating the item. It proves the inequality for every union without any reference back to the parent potential-stability theorem.

For step 8 I checked b<=kappa, since Y is a union not containing T and its boundary nodes are a subset of all other-component attachments. The component inequality yields (1-3*epsilon)*e<=1+epsilon-2*p. With epsilon<1/9 this forces p=0 and e=1; the unweakened inequality then gives kappa<5/2, hence b=kappa=2. All inequalities use integral e,p,b,kappa at the indicated places. A proper component of degree one with one attachment is already in the first alternative, and cannot arise as the purported exception.

For step 9 I read both cited statements. The pointed genus-zero lemma applies to the proper integral T with global functions k, H1(O_T)=0 and intrinsic degree-one L. It gives T=P1. The normalization statement says its map is an isomorphism over the smooth locus, now all of T. I checked the additional completeness clause directly: ambient coordinates generate L and their image U in the two-dimensional H0 cannot be one-dimensional, since a sole generator would be nowhere zero, trivialize L and contradict degree one. Thus the given embedding in its span is the complete degree-one embedding, as required. This uses the statements of the existing nodes, not constructions hidden in their proofs.

Edge cases checked: Y empty gives b=0; Y=D leaves no E; D irreducible likewise has b=0; self-nodes contribute to arithmetic genus p, not boundary counts; disconnected unions are treated additively; the exceptional bridge line has e=1, b=2 and is permitted with equality. The maximal-union proof permits A union T=D because the full defect is zero. Characteristic never enters these arguments. Every step is below 2000 characters. I checked dependency closures of the span-weight, pointed-genus-zero and normalization-adjunction tools and found no path to the current item. No new node, restatement, elementary wrapper or Mathlib leaf was manufactured. The recorded searches are genuine msearch.py queries; the returned Chevalley, elliptic-curve, Proj, residue-degree and polynomial declarations do not state this item.

The non-definition citations from other units are declared individually in split_report.tool_uses: they are generic algebraic-geometry/coherent-cohomology tools, not replacements of a six-functor unit route.

## Unfinished work

None in the one-level split. Existing unsplit dependencies remain existing queue items. No Lean writing or compiler, Lake or build command was run. Validation and delivery results will be appended after the required remote dry run.
