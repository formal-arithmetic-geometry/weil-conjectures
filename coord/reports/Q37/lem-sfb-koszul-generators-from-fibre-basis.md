# Stage-1 delivery: lem-sfb-koszul-generators-from-fibre-basis

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-generators-from-fibre-basis.json: existing statement split into six steps; no Mathlib match.
- citations.json: verbatim statements for all seven step/node citation pairs.
- searches.jsonl: actual search-command records, retained alongside the earlier searches already in the item.
- report.md: source audit and signed review.

No new nodes and no new Mathlib leaves. No Lean files, compiler commands, repository writes, launcher edits, or worker git commands.

## Attachments

None for the item. Searched the complete lean/WeilConjectures tree for its blueprint id and fibre/fiber-basis wording, and the RingTheory and AlgebraicGeometry files for Koszul generator/basis statements. Existing ExteriorAlgebra.exists_koszul_conormal_basis and RingTheory.Sequence.isKoszulRegular_of_flat supply strictly smaller inputs, not the whole statement. Their corresponding existing DAG nodes are reused.

## Wanted literature

None. All sources used are available locally.

## Corrections and observations

The statement is correct as written and was retained exactly. The source is divisors.tex Tag 067N (lemma-generate-regular-ideal), assertion (3). The prior node had no proof. This split supplies its matrix argument in affine coordinates, including the actual principal-localization element, rather than citing 067N itself as a black box. For the final change of generators it reuses the existing, more general, equal-length theorem 066A(3).

The ancestor command printed None because the inherited created.item chain eventually names the module Sheaf.SixFunctors.CtfStabilityDirectImages rather than an extant DAG id. The node's existing place already identified det-thm-sf-ctf-stability-direct-images, and the existing lem-sfb-admissible-direct-image explicitly carries that blueprint ancestor. I filled the item's null blueprint.from.node with that verified ancestor and retained its place and via history. The current latest blueprint's six-functor unit and direct-images proof (3) were read; the inherited supporting alteration/algebra chain is not a replacement for their route.

Whole-DAG searches for 067N, 062H, 062I, Koszul regular generators, conormal bases, and flat localization identified the reused statements. Whole-blueprint searches for Koszul, conormal, 066A and 067N found no equivalent blueprint statement of this item. No duplicates were created. The existing lem-sfb-koszul-equal-length-generators has no dependency on this item: its proof dependencies are conormal basis, finite-module surjective endomorphism, substitution with unit determinant modulo the ideal, and definitions.

Mathlib was searched through msearch.py only: leanfinder twice with different phrasings, loogle, grep, and leansearch. All services answered. Results include smooth algebra presentations, cotangent bases, ordinary weakly regular sequences, and a Nakayama-based spanning theorem for residue fibres. Those do not give the Koszul-regular conclusion. Mathlib/RingTheory/Regular/RegularSequence.lean line 21 explicitly leaves Koszul regularity as TODO. The two distinct semantic phrasings and all actual results are recorded; inherited searches were retained. The Nakayama hit was not used: the determinant argument proves generation directly.

## Unfinished work

None for this one-level stage-1 split. The independent nodes it uses retain their own statuses; this delivery makes no claim that the full descendant closure is proved in Lean.

## Not duplicates

No new nodes. In particular, I did not create nodes for quotienting a specified coordinate basis, equality of finite vector-space dimensions, invertibility of the coefficient matrix on its determinant open, or preservation of regularity under equal-length generator replacement. The first three are explicit elementary calculations in the item; the last already has a DAG node.

## Review by Q37

I read the item against the full statement and proof of Stacks Tag 067N in divisors.tex. Its prescribed proof first counts conormal generators and then makes a coefficient matrix invertible; these are exactly the steps supplied here. I also read more-algebra.tex Tag 062I, the first paragraph deriving the conormal basis from first Koszul homology; Tag 062H, both flat base-change assertions and their proof; Tag 066A(3) and its proof; and algebra.tex Tag 00HT(1). The source's change-of-basis lemma 0625 was read as well. I chose the already present 066A node for the final regularity inference, avoiding a new duplicate Koszul change-of-basis node. There are no new nodes whose source needs a separate review.

Step 1 cites lem-weil-pbc-localization-flat for precisely the flatness of a localization, lem-sc-koszul-regular-flat-base-change for the image tuple's Koszul regularity, and lem-sc-koszul-conormal-basis for the specified generator classes forming a basis of J/J². I opened each cited JSON statement. The first allows an arbitrary multiplicative set, including A minus a prime. The second requires a flat algebra, which the first supplies. The third requires a Koszul-regular tuple generating the ideal; both are established before it is invoked. Its length may be zero. The elementary expression of fractions in the generated ideal verifies generation over the localization, without presupposing finite presentation or a Noetherian ring.

Step 2 uses the basis already obtained, with no additional cited theorem. I checked the coordinates of the submodule being quotiented: J is contained in the local maximal ideal, hence J² is contained in mJ, and the m-multiple of J/J² corresponds to (m/J)^m under its specified R/J-basis. Its quotient is the residue-field vector space with the generator images as basis. Equality with the assumed finite basis forces the lengths to agree. This does not confuse J/J² with J/mJ and does not assume that minimal generators have constant rank without the conormal-basis theorem.

Step 3 is the explicit square coefficient matrix f=Cg. Its reduction is a change between the two actual fibre bases, so its determinant is nonzero in the residue field. I checked the implication needed here: an element of the prime certainly maps to zero in that field, so this determinant lies outside the prime. Step 4 cites def-weil-ring-localization-away only for its stated fraction algebra with s inverted, not for any theorem about it. The inverse is written as s^(-1) times the adjugate. This gives both inclusions of the generated ideals as identities over A_s. No unsupported phrase about clearing denominators or spreading out remains.

Step 5 again cites the localization-flatness and flat Koszul-base-change statements with their hypotheses satisfied for A to A_s. Its third citation, lem-sfb-koszul-equal-length-generators, states exactly that a second tuple of the same length generating the same ideal is Koszul-regular if the first is. All three requirements have already been proved. I read its entire statement, including its allowance of zero length and non-Noetherian rings. The off-unit conormal and flat-base-change theorems are declared as generic tools in split_report.tool_uses: they supply algebraic inputs, without replacing the unit's route. Localization-flatness is already a Mathlib leaf.

Step 6 checks the potentially troublesome empty tuple explicitly: the residue field is nonzero because the prime is proper, so a zero-dimensional fibre forces the original Koszul tuple also to have length zero, I=0, and s=1. I tested the positive-length model A=k[x], I=(x), prime (x), f=x(1+x), where s=1+x works. At prime (x,x+1) there is no prime over those generators, consistent with the hypotheses. A zero ring has no prime and hence no instance of the statement. I checked that no use of ordinary regular sequences, Noetherian Nakayama, exactness after a non-flat tensor, or an inverse-limit assertion entered the argument.

Against delivery-errors B–E: the single item retains its exact, self-contained statement and definition dependencies; no new statement-only nodes or unsupported notions occur. All non-elementary inputs are existing cited statements, and citations.json copies their full verbatim statements. The elementary steps are short explicit coordinate, determinant, and adjugate calculations; all steps are below 2000 characters. The proof carries the actual argument rather than delegating a clause to a restatement. It uses only prior results and has no circular appeal to this item. The source tags and labels were checked in the local Stacks sources. No source error or statement dispute was found, and nothing was weakened.
