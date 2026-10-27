## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-chevalley-rank-two-straightening.json: item, statement unchanged, four proof steps, status split.
- lem-sfb-chevalley-string-central-parity.json: statement-only unsplit lemma about an oriented root string, central brackets, and integral grouped half-sums; no Mathlib match.
- lem-sfb-formal-class-two-exponential.json: statement-only unsplit identity for formal exponentials with central pairwise brackets in an arbitrary associative rational algebra; no Mathlib match.

citations.json contains a verbatim statement excerpt for each citation in steps 1 and 3. searches.jsonl is the unaltered msearch log. No Lean file, compiler, build, repository write, launcher edit, or agent delegation was used.

Attachments: none. Searched the live WeilConjectures library for the blueprint tag, Chevalley, Kostant, straightening and divided powers; the Chevalley hits concern constructibility or Beck--Chevalley, not this identity. The item has no upstream declaration giving its clauses.

WANTED: Steinberg, Lectures on Chevalley Groups, initial integral-form construction and rank-two divided-power calculations, for lem-sfb-chevalley-rank-two-straightening and lem-sfb-chevalley-string-central-parity.

WANTED: Bourbaki, Lie Groups and Lie Algebras, Chapter II, Campbell--Hausdorff series, central-bracket specialization, for lem-sfb-formal-class-two-exponential. Its source field explicitly identifies this as an agent-stated supporting identity, not a theorem proved in Milne.

The existing item correctly warned that Milne Theorem 23.71 supplies bracket magnitudes, not divided-power straightening. I retained that warning and wrote an agent-origin coefficient proof, with the two non-elementary inputs stated separately. There is no statement dispute and no change of hypotheses, conclusion, chapter or unit route. The library has no relevant sorry-free attachment. The nearest-blueprint ancestor command returns None because the inherited ancestry is broken; the item already has from.node null with an explicit long place/via chain. I preserved it, propagated the command's result to the new nodes, and located its ultimate route in the latest blueprint direct-images proof (3). This is reported rather than silently inventing an imported ancestor.

I read the chapter record, the recorded unit and the latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The latest proof (3) is the direct-image route served by the ancestry. This item is a supporting calculation far below that unit, not its key statement, so no realized fields are edited.

Nothing in the mathematical split is left incomplete: the new nodes are deliberately statement-only obligations for the next DAG level. Delivery checks and push follow this report.

## Not duplicates

lem-sfb-chevalley-string-central-parity vs lem-sfb-chevalley-rank-two-straightening: the new lemma is entirely a Lie-bracket assertion about one finite oriented string and parity; it has no enveloping-algebra product, divided-power commutator, or lower-degree word assertion. The item combines it with formal exponentials and explicit coefficient extraction.

lem-sfb-chevalley-string-central-parity vs lem-sfb-chevalley-root-normalization: the latter constructs a Chevalley basis with prescribed simple vectors. The new lemma assumes that basis and proves root-string centrality and integral grouped half-sums for an oriented pair.

lem-sfb-chevalley-string-central-parity vs lem-sfb-chevalley-adjoint-weyl-signs: the latter concerns a three-exponential Weyl operator and its signs on every root space; it does not state centrality or parity for the one-sided string.

lem-sfb-chevalley-string-central-parity vs lem-sfb-opposition-root-bracket-norm: the latter computes the opposition norm of one bracket of two normalized vectors; it does not give the string or its grouped half-sums.

lem-sfb-formal-class-two-exponential vs lem-sfb-chevalley-rank-two-straightening: the new lemma has no root system, integral basis, or integer coefficients, and works for arbitrary elements of any associative rational algebra. It supplies only a rational formal identity.

lem-sfb-formal-class-two-exponential vs lem-wf-log-exp-formal-identities: that node proves inverse composition identities for scalar log/exp series over a commutative rational algebra, not a factorization for nonzero central commutators.

lem-sfb-formal-class-two-exponential vs lem-weil-power-series-exp-hom: that node is about a homomorphism for commuting formal scalar series, not nonzero central commutators.

Global blueprint_refs.py searches for Chevalley, root string, root-string, root system, rank two, exponential, commutator, divided, class two and nilpotent exponential found no equivalent blueprint statement. Whole-DAG searches and the opened related nodes above rule out reuse, including the unsplit unipotent-coordinate lemma: it assumes an already admissible representation/lattice, whose existence here depends on Kostant PBW, so using it would be circular. Kostant integral PBW itself cites this item and cannot be used as an input.

## Review by Q146

I checked delivery-errors B--E against all three node files. Each new statement introduces its algebra, variables, roots, brackets and operators; the root lemma repeats the Chevalley normalization rather than referring to an unspecified setting. Its only statement dependencies define Lie algebras and semisimplicity, and I opened those definition statements. Formal series, multiplication, exponentials and commutators are defined directly in the generic lemma, and its commutator Lie algebra cites def-wf-lie-algebra; no analytic structure is assumed. Both new files have proof=[] and proof_deps=[], complete blueprint fields, genuine msearch records, and unsplit status; neither is an elementary restatement of an item clause.

For the root lemma I read Milne's printed pp.508--511 (PDF pp.520--523), especially Theorem 23.71 and the definition of admissible lattices, and Appendix C section g, printed pp.621--622 (PDF pp.633--634), including table (180) and all four rank-two diagrams. These support its bracket normalization and rank-two reduction; the centrality/parity consequence is explicitly agent-stated. A way to prove it is to orient the shorter root first in the rank-two subsystem, list all nonopposite pairs in those four diagrams, and use successive bracket magnitudes (p+1)...(p+k)/k!=binom(p+k,k). Sums of two string roots, when roots, commute with all string roots. In G2 a critical grouped coefficient comes from i+j=3 with (i,j)=(0,3),(1,2): the magnitudes are 1 and 3, so their signed sum is even; it is invalid to assert that the individual brackets are all even. I specifically formulated grouped half-sums to avoid that error. This supporting Lie-bracket calculation is separate from coefficient extraction and does not assume an integral enveloping form.

For the formal lemma I read the same source's equation (153) as motivation, and checked the candidate Mathlib statements in their source: IsNilpotent.exp_add_of_commute at RingTheory/Nilpotent/Exp.lean:81 and PowerSeries.exp_mul_exp_eq_exp_add at RingTheory/PowerSeries/Exp.lean:123. The former requires nilpotence and commuting elements, the latter commutative coefficients. Neither permits our nonzero central brackets. The statement is the algebraic class-two identity; a proof can differentiate the ordered product in an extra formal scalar parameter u. Its right logarithmic derivative is sum Z_i + u sum_{i<j}[Z_i,Z_j], canceled by exp(-u^2/2 sum brackets). Equality follows from coefficient recursion and the value 1 at u=0. This reasoning needs no norm or convergence; the statement is valid for r=0 and vanishing brackets. The theorem itself remains a statement-only obligation, as required.

Step 1 uses the root lemma's actual ordering, finite string and named c_k,z_d. It does not assume the original pair is simple or obtuse. The interchange of roots also interchanges exponents and negates the commutator, preserving the required weight and cone. Its cited excerpt contains precisely those assertions. Zero input exponents are handled before invoking any product expansion.

Step 2 uses no non-elementary black box: it writes the induction for repeated commutators using Pascal's identity, compares each coefficient of the two conjugating series, verifies their inverse identity, and uses multiplicativity of conjugation. In U, brackets equal associative commutators by its defining quotient relation. No PBW injectivity, representation, or nilpotence in U is needed.

Step 3 cites the formal lemma for the ordered factorization and the root lemma for vanishing triple brackets and integral c_k,z_d. I opened both exact statements after writing them and copied their verbatim assertions to citations.json. The hypotheses Z_i in the augmentation ideal hold because every term has t. Centrality with respect to the Y_k implies centrality with their pairwise brackets by expanding [C,Y_iY_j], so correction summands commute and the same formal lemma factors their exponential with zero bracket correction. This additional implication is written out, not attributed to a definition node.

Step 4 multiplies explicit exponential coefficients, displaying both index equations, the integer coefficient, the weight identity and the degree-loss identity. Every nonprincipal term has positive loss because k>=1 and d>=1. Finite coefficient sums follow from those index equations; all exponents are nonnegative and all included root labels are roots in the nonnegative pair cone. Exponent-zero factors are removed and the all-zero intermediate choice cancels exactly the reversed product. No hidden rearrangement of noncommuting words is used. The proof has no step over 2000 characters.

I tested the new Lie-bracket statement on all oriented nonopposite pairs in A1xA1, A2, B2 and G2 using the coordinate lists of the four diagrams and their invariant quadratic forms: respectively 8, 24, 32 and 84 ordered pairs with the first root no longer than the second. For each I checked centrality and parity of each grouped coefficient, including arbitrary signs modulo 2. The sole case with two contributions in a group has p=0,q=3,d=3 and magnitudes (1,3), confirming the correction above. I also checked the formal lemma's sign in the two-element case: exp(X+Y)=exp(X)exp(Y)exp(-[X,Y]/2). This is evidence for the statement and a guide for its future split, not a claim of a Lean proof.

The actual searches were run only through msearch.py and their returned hits were read. Besides the exponential candidates, I read RootPairing.GeckConstruction.e_lie_v_ne (Basic.lean:351), chainBotCoeff_add_chainTopCoeff_le_three (Chain.lean:475), and EmbeddedG2.allRoots_eq_map_allCoeffs (Finite/G2.lean:312). They supply fragments of the root lemma but do not give its centrality and integral grouped half-sums by one-line specialization. Two semantic phrasings were tried for every proposed new node and the item. No Stacks tag states these Lie-theoretic calculations; no SGA source was used.

Dry-run repair: the server rejected the generic exponential node because its statement cited no definition node. I made its actual Lie-algebra structure explicit and cited def-wf-lie-algebra, whose statement defines alternating brackets and Jacobi. This is not a citation of the scalar formal-series definitions (which assume commutative coefficients and cannot define our coefficient algebra). I expanded the associativity justification inline. I also corrected the duplicate comparison after opening lem-wf-log-exp-formal-identities: it is formal commutative log/exp composition, not a p-adic matrix statement.
