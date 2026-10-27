# Q28 — lem-trf-normal-flat-hilbert-convolution

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normal-flat-hilbert-convolution.json`: statement, split; original statement retained, six proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-adic-degree-zero-regular-strict-powers.json`: statement, unsplit; no Mathlib match. General filtered-module intersection theorem, not a length or Hilbert-function formula.
- `citations.json`: one verbatim statement excerpt for every step/node citation.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, normal flatness, Hilbert–Samuel, and Hilbert convolution found no project declaration proving this item. The conormal flat base-change declarations concern a different statement.

## Literature wanted

WANTED: archival copy of Hironaka, Certain numerical characters of singularities, J. Math. Kyoto Univ. 10 (1970), pp.151–187, especially pp.153,157, for lem-trf-normal-flat-hilbert-convolution. Read the cited public PDF online at https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf; no file was downloaded into the repository.

WANTED: Hironaka, Resolution of singularities (1964), Chapter II, Theorem 2, the original normal-flat tangent-cone comparison referenced there. This is background, not a black box used in the delivered proof.

## What was wrong and what changed

The incoming node was statement-only. Its source points to the numerical consequence of Hironaka's normal-flat tangent/normal-cone product, but its hypotheses allow arbitrary Noetherian local rings. The split supplies a characteristic-independent module argument rather than assuming a coefficient-field section or a regular ambient presentation. No statement correction or added hypothesis was needed.

The current latest blueprint's ancestor lem-trf-local-term-locality uses contracting correspondences. This is an already-created auxiliary local-algebra branch, not a replacement for that unit route; no chapter, unit, or target statement was edited. Blueprint search found no imported node for this strictness theorem or the Hilbert convolution.

During self-review I rejected the stronger intermediate assertion I^j intersect m^N = I^j J^(N-j): it would wrongly omit the higher I-powers (already false when J=0). The delivered proof asserts only the required equality of images modulo I^(j+1). It proves it by eliminating the I-degree a<j terms in increasing order, applying strictness to the shifted modules I^a. The new lemma is applied to every I^a, not just R. The finite generation needed for those applications is explicitly cited.

## What remains

The new strict-power theorem is deliberately statement-only and joins the stage-1 queue. The item itself is completely split at one level. No Lean was written, no compiler or Lake/build command run, no agent started, and no repository or launcher file edited.

## Argument reserved for the new node's worker

The new theorem is a general module lemma, not the original numerical conclusion. Here is a possible proof plan (kept out of its statement and proof fields). For each p, the injectivity condition for the parameter sequence passes from the finite filtration factors I^a M/I^(a+1) M to M/I^p M by the successive-quotient exactness argument of Stacks 0F1T. One can allow zero factors: only the injectivity clause is used. Thus reducing by any prefix of the parameters preserves exactness of this finite filtration. The intersection of all I-powers on the finite modules obtained after those prefix quotients is zero by 00IP; it follows that the same successive multiplications are injective on M and I^p M. For the short exact sequence 0 -> I^p M -> M -> M/I^p M -> 0, the parameter sequence is consequently weakly regular on all three modules, and the sequence remains exact modulo J (apply the elementary snake argument successively). The module version of 00LN identifies their J-associated graded modules with their quotients modulo J tensored with a polynomial ring. Hence the J-graded sequence is exact. Starting with the exact sequence modulo J, induction on q using these graded short exact sequences proves exactness modulo J^q. Its left-hand injectivity says precisely I^p M intersect J^q M = J^q I^p M. The worker should split these supporting claims as needed; this delivery does not present them as an elementary proof of the new node.

## Review by Q28

I read coord/delivery-errors.md B–E in both copies, the three-level contract in SETUP.md, GOAL.md, the stage-1 brief and stage document, and the item's chapter/unit and latest blueprint ancestor. For the original source I read Hironaka (1970), section 2 at printed p.153 and the product/Hilbert discussion after Example (4.2) at printed p.157. I also inspected ILO VIII 2.3.13, which is motivation about resolution algorithms, not a proof of this local-algebra formula. Accordingly proof_origin is agent. The algebraic supporting sources read in the local Stacks text were 00NZ (finite flat local implies finite free), 00NQ (regular local parameters are regular), 00LN and its module version (regular implies quasi-regular), 00IV (additivity of length), 0F1T (regularity and quotient exactness through a short exact sequence), and 00IP (Krull intersection). The last two support the new node's stated generalization, not a claim that Stacks states the full strict-power comparison verbatim.

Step 1 uses lem-trf-flat-graded-fibre-regular-lift exactly for its explicit sentence that every G_j is finite free. Its hypotheses are the item's Noetherian local R, I in m, and flat gr_I R. Its later regular-element clause is not used. The chosen basis gives rank h_j after residue-field tensoring directly. I opened lem-weil-pbc-regular-local-generators-regular-sequence: it applies to A, which is assumed regular local of dimension s, and a minimal generating list of its maximal ideal. It gives the whole regular sequence, so multiplication is injective on each quotient and on its finite direct sums. Zero G_j require no nonzero-quotient condition.

Step 2 uses lem-weil-pbc-noetherian-submodule-finite exactly with R as a one-generated module and I^a as its submodule. The new strictness node is applied to M=I^a; its graded pieces are G_(a+p), so Step 1 supplies every injectivity hypothesis. The y_i lie in m and I is proper; no flatness of R over A is presumed. Its equality is exactly J^q I^a intersect I^(a+p) = J^q I^(a+p). I opened the full statements of both citations and copied their used content into citations.json.

Step 3 is the finite ideal expansion and induction written in the item. At each elimination a<j, N-a-1 is nonnegative. The absorbed term belongs to the next summand, so the process terminates after j steps. Only the degree-j image is retained; higher I-powers are never discarded before quotienting. No non-elementary additional theorem is used.

Step 4 identifies an explicit surjection and its kernel. Here N=n+1 and j<N ensure t=N-j>=1. I^N is contained in m^N, so the filtration really ends in zero. The action of J on G_j is that of n=m/I, proving the stated quotient, and the already-chosen free basis gives its h_j summands. These are R-module isomorphisms through R -> A; an A-action on R itself is never asserted.

Step 5 uses lem-pur-regular-sequence-graded-polynomial for A and its regular parameters, exactly the specified graded polynomial isomorphism in that node's statement. Then each degree has the explicitly given monomial basis. A one-dimensional residue-field factor is simple also as an R-module because the residue map is onto. I checked lem-weil-pbc-length-additive-short-exact says additivity over an arbitrary ring, so it may be applied over R to this A-module filtration. Stars and bars with a slack coordinate counts the monomials of degree <t, including s=0; this is written out, not cited as a hidden theorem.

Step 6 uses the same arbitrary-ring length-additivity statement on the finite filtration. All factors have finite length by Step 5. Summing those factors yields precisely the original formula, with exponent n+1 and binomial lower index s. There is no shift error. Every cited statement was opened, and each citation has a verbatim quote. No non-elementary step exceeds 2000 characters.

For small cases I checked n=0 (both sides 1), I=0 (regular-local length count), I=m (sum of maximal-ideal graded dimensions), and an Artinian base with s=0. A useful mixed-characteristic case is R=Z_p[[x]], I=(x): A=Z_p, s=1, h_j=1, and both sides are (n+1)(n+2)/2. For the new node M=0, the empty parameter list, p=0, q=0, and I=0 give the stated elementary identities. Allowing zero graded factors is necessary, so its assumption was written as successive injectivity rather than incorrectly requiring every factor to be a nonzero regular-sequence module. A test showing the hypothesis matters is R=k[[x,y]]/(xy), I=(x), J=(y): the degree-zero action on G_1 fails injectivity, so the lemma cannot wrongly assert transverse intersections here.

The new node is not elementary: transferring regularity through all finite I-adic quotients, then through separated limits and all powers of J, needs the module/quasi-regular comparison. It is not a clause or restatement of the item: it has no regular-local quotient, flatness, fibre dimension, length or binomial conclusion. Existing same-tag nodes were read and distinguished below. Generic off-unit regular-local and regular-sequence tools are explicitly declared in split_report.tool_uses; they do not replace the trace-formula unit route.

Mathlib searches were run only by msearch.py and the exact queries/results were recorded from searches.jsonl. Both phrasings for the item returned dimension/flatness results, not Hilbert convolution. The new-node searches returned Artin–Rees (only eventual shifted intersection), adic-topology definitions, IsRegular.pow, and the scalar quotient-intersection criterion. I read Mathlib/RingTheory/Filtration.lean:389 and Regular/IsSMulRegular.lean:152,165; neither proves regularity on every adic quotient from the graded hypotheses or strictness for all powers of a multi-generated ideal. Loogle's IsRegular.pow is monoid regularity of one element. No Mathlib leaf is claimed.

## Not duplicates

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-sbc-regular-principal-prime-localization-dvr: the existing statement proves a principal-prime localization is a DVR; the new statement compares two adic submodule powers.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-sbc-complete-local-subideal: the existing statement proves subideal completeness, with no strict-intersection assertion.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-lift-regular-generators-through-fibre: the existing statement lifts ideal generators using an isomorphism of generator spaces; it does not compare adic filtrations.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-regular-ideal-residue-basis-prescribed-generator: the existing statement concerns conormal bases and prescribed generators, not powers intersecting an adic module filtration.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-formal-coefficient-operator-base-change: the existing statement concerns coefficient operators on power series and base change, not regular parameters on adic module factors.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-flat-graded-fibre-regular-lift: the existing statement gives graded freeness and lifts a positive-degree fibre nonzerodivisor; it does not give strict powers of a degree-zero parameter ideal.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-normal-cone-directrix-minimal-primes: the existing statement is a characteristic-zero minimal-prime kernel containment for a polynomial vertex, not this general module intersection theorem.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-completed-conormal-resolutions: the existing statement is a conormal differential resolution comparison for complete intersections, not an adic strictness statement.

- lem-trf-adic-degree-zero-regular-strict-powers vs def-trf-finite-coefficient-expression: the existing node defines formal-series operators; the new node is a theorem about submodules and two ideals.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-sc-principal-ideal-dvr: the existing statement is a DVR criterion, not a two-ideal intersection statement.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-sfb-perfect-derived-bialgebra-exterior-rigidity: the existing statement concerns perfect derived bialgebras with exterior residue cohomology; no adic strict-power theorem is stated.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-weil-pbc-finite-module-complete-over-complete-noetherian: the existing statement gives completeness of finite modules, not exact intersections with powers of a different ideal.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-weil-pbc-krull-intersection-localization: the existing statement makes the infinite intersection vanish after localization; the new statement is a finite two-ideal equality for every pair of exponents.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-weil-pbc-regular-sequence-conormal-free: the existing statement describes J/J^2 for a regular sequence in a ring; it does not concern a filtered finite module.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-weil-pbc-regular-sequence-short-exact-sequence: the existing statement transfers weak regularity across one short exact sequence and reduces by parameter prefixes; the new statement compares all powers J^q with the whole I-adic filtration.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-pur-regular-sequence-graded-polynomial: the existing statement gives a polynomial associated graded ring for a regular sequence; the new statement has a finite module and a second ideal filtration.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-pur-regular-sequence-higher-homogeneous-relations: the existing statement constrains coefficients of homogeneous relations in a ring; it does not assert all strict-power intersections for a module.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-weil-pbc-regular-quotient-ideal-intersection: the existing node gives I intersect J = IJ when parameters are regular modulo I, for rings; the new node works with arbitrary finite M, all I^p, and all J^q under degreewise regularity.

- lem-trf-adic-degree-zero-regular-strict-powers vs lem-trf-normal-flat-double-initial-ideal: the existing node identifies kernels of two graded polynomial presentations and depends on this item; the new node has no polynomial presentation or tangent-cone isomorphism and is not downstream of the item.
