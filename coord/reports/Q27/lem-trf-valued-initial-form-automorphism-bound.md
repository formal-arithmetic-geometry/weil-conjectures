# Stage-1 delivery: Q27

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valued-initial-form-automorphism-bound.json`: item, split into seven explicit proof steps; original statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-finite-abelian-character-prime-bound.json`: new statement-only lemma, unsplit; no Mathlib match under the actual hypotheses after two semantic phrasings, Loogle, LeanSearch and source grep.
- `dag/nodes/sec-trace-formula/lem-trf-finite-embedding-separability-count.json`: new Mathlib leaf; positivity/nonemptiness and equality iff separability of the embedding count. The existing upper-bound node is reused separately.
- `citations.json`: one entry per cited node per item step, with quotations copied verbatim from the actual statements.
- `searches.jsonl`: records produced by the required msearch command; no hand-written searches.

Two new nodes, one Mathlib leaf. No Lean or unit/chapter file written. All writes are in the authorized sandbox.

## Attachments

None. The exact blueprint tag is absent from `lean/WeilConjectures/`; searches for initial forms, inertia, finSepDegree and the finite-character-count declaration find other topics, not a declaration proving this item. In particular a definition of inertia is not the index bound, and the ideal-theoretic Dedekind formulas do not apply to arbitrary real-valued fields. No sorry declaration is treated as finished.

## WANTED

WANTED: Gabber–Ramero, *Almost Ring Theory*, sixth and final release, sections 6.2.8–6.2.12, PDF pp.209–211 / printed pp.207–209, for this item and lem-trf-finite-abelian-character-prime-bound. The archival path inherited by the item is not present in literature. The author-hosted primary PDF was read online at https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/lorenzo_ramero/releaseLNM.pdf. Nothing was downloaded into or written to the repository. The proof is marked agent-written; this report is the permitted WANTED record.

## Findings and proof route

The statement is retained verbatim and no statement dispute was found. The latest blueprint locality proof and unit were read, together with the inherited chapter/unit records. The latest proof concerns contracting correspondences; it does not contain this auxiliary valued-field theorem. The inherited semistable-modification/Temkin branch is preserved in blueprint.from.via, and from.place now explicitly distinguishes the inherited auxiliary from what the latest locality text itself proves. No unit or chapter route is replaced.

Gabber–Ramero 6.2.8 defines the inertia pairing by reduction of h(x)/x and explains representative independence. Its surrounding situation assumes a henselian base and a finite Galois extension; 6.2.10 additionally assumes separably closed residue field. We do not apply their surjectivity theorem or their wild-kernel theorem under our weaker hypotheses. Instead, Steps 1–4 write all the needed representative, multiplication, and kernel computations using just the isometry and trivial residue action. Completeness, discreteness, henselianity, normality of E/F and perfection of the residue field are never used. The character-count subclaim is the only new unsplit ingredient. This is a split of the argument rather than a transfer of the item's bound into another node.

For the new character-count node, the source paragraph explains factoring out p-torsion, but does not state the full arbitrary-field bound in this form; this general auxiliary statement is agent-extracted. The intended later proof is: decompose the finite abelian A into cyclic factors of positive orders n_i; a character on a cyclic factor is determined by an n_i-th root of unity. In characteristic p write n_i=p^{a_i}m_i with p not dividing m_i; Frobenius gives z^{n_i}=1 iff z^{m_i}=1, and the polynomial root bound gives at most m_i possibilities. In characteristic zero use n_i itself. Their product is the prime-to-p part of the product of the n_i, giving the bound and finiteness. This proof plan is kept here, not inside the statement-only node. It explains precisely the additional content beyond the existing splitting-field character-duality leaf.

For the new embedding leaf, I read Stacks fields.tex, lemma-count-embeddings-explicitly (09H8) and lemma-separable-equality (09HA), including their generator/root-count arguments. The positivity and equality criterion are supplied directly by Mathlib after identifying the count: SeparableDegree.lean:237–238, Field.finSepDegree_eq_of_isAlgClosed; :145–146, Field.instNeZeroFinSepDegree; :774–786, Field.finSepDegree_eq_finrank_iff. The relevant section hypotheses at :127–146 and the surrounding source were read. Finite-dimensional supplies algebraicity; the target needs only algebraic closedness. A nonzero Nat.card also guarantees finiteness because Nat.card of an infinite type is zero. This leaf does not repeat the upper bound already in the DAG.

The search hits were checked, not merely listed: CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (FiniteAbelian/Duality.lean:58–97) requires roots of unity not assumed here. AddChar.card_addChar_le (Orthogonality.lean:59–99) requires RCLike, so cannot handle arbitrary residue fields or positive characteristic. MulChar.finite does not supply the prime-part bound. Both semantic character searches therefore have the same honest no-match verdict. The item's pre-existing search records were read and preserved.

## Not duplicates

lem-trf-finite-embedding-separability-count vs lem-weil-pbc-finite-extension-finitely-many-embeddings: the existing 09H8 leaf gives only finiteness and an upper bound for any target field; the new leaf gives nonemptiness and equality iff separability for an algebraically closed target. We cite the existing node for its upper bound rather than repeating that clause in the new one. This is the only existing node whose source contains either new embedding-node tag, 09HA or 09H8.

lem-trf-finite-embedding-separability-count vs lem-exc-normal-field-degree-factors: the latter assumes normality and positive characteristic and relates automorphisms and a separable subfield; the new leaf assumes neither and supplies a separability equality test for embeddings. It cannot be used backwards to obtain the needed criterion.

lem-trf-finite-abelian-character-prime-bound vs lem-per-finite-character-dual-cardinality: the existing leaf requires enough roots of unity and gives equality and separation; the new statement needs no roots-of-unity hypothesis and gives only the prime-to-characteristic upper bound. Their hypotheses differ substantively, so the existing leaf cannot be directly specialized.

lem-trf-finite-abelian-character-prime-bound vs lem-per-character-prime-part-reduction: ordinary representation-character trace values and reduction modulo p are different from counting group homomorphisms A to k units.

lem-trf-finite-abelian-character-prime-bound vs lem-exc-field-roots-cyclic-bound: the existing leaf counts roots of a single polynomial in a field, not the characters of a general finite abelian group; the finite-abelian structure argument remains needed.

Whole-DAG searches used the tags, separable-degree and embedding terminology, and character/cardinality terminology. Whole-blueprint searches used separable degree, 09HA, embedding separability, inertia, character group, finite abelian group and prime to characteristic. No blueprint node states either new result. Both new ids were searched before creation. No new node restates the valued-field index bound.

## Review by Q27

I checked delivery-errors B–E against the actual statements and source text. The two new statements introduce every object, record their needed field/algebraic-closure notions, have empty proofs and empty proof dependencies, and use single-escaped TeX in the JSON. The Mathlib match names each clause's declaration and its verified pinned-source line. Every recorded Mathlib query was actually run through msearch and its returned hits read; no unavailable service was recorded as a negative result. The existing item statement and inherited searches were retained.

Step 1 cites only def-trf-valuation-ring, whose statement is exactly the x-or-inverse characterization used. It proves the subring, ideal, residue-field, injectivity and residue-action facts directly: norm-one representatives have inverses in the valuation ring, and representatives differing by norm below one have images differing by norm below one. No theorem about the residue action is inferred from a definition node.

Step 2 has no black box: the displayed product, inverse and conjugation norm calculations prove subgroup and normality. In the inverse formula isometry gives the same norm after applying q. For Q contained in I, nonzero integral representatives have norm at most one and zero is fixed. Thus trivial initial-form action implies trivial residue action without needing a uniform strictness constant.

Step 3 gives the complete representative-independence argument with u=y/x of norm one. Only elements of I are used, so their residue action on u is the identity. The product identity proves a character on the value group; fixation of F and the equal-norm calculation give descent to the quotient. Step 4 checks the group homomorphism formula by applying h to the unit t(x)/x and reducing; the same trivial residue-action hypothesis is precisely what is needed. Its displayed equivalence proves the kernel is Q for every nonzero x. These are direct algebraic computations, not a hidden appeal to a Galois/henselian pairing theorem.

Step 5 cites the new finite-abelian-character-prime-bound statement, which explicitly supplies finiteness and the bound for any field, not just a splitting field. A is abelian because the value groups are multiplicative subgroups of positive reals; its order is e by hypothesis. The embedding of residue fields identifies their characteristics, so the node's prime-part convention agrees with e prime including characteristic zero. This statement was read in its final file and quoted verbatim in citations.json.

Step 6 cites the new embedding leaf for positivity and the exact equality iff separability, and the existing finite-extension-finitely-many-embeddings node for s at most f. Both statements were opened; the existing node really applies to an arbitrary target field, and the new node really applies to the specified algebraic closure and the finite residue extension of degree f. Choosing one embedding is justified by positivity/nonemptiness. Postcomposing residue automorphisms with its injection gives an injection into the embedding set, with cancellation explicitly justified. These facts do not assert surjectivity of the residue action.

Step 7 cites no additional fact: it writes the fibre/coset bijections and counts the partitions explicitly for rho, chi, and H/Q. Cancellation is by the positive cardinality of Q, which contains the identity. It uses only the earlier numerical bounds. Each step is below 2000 characters; no long argument conceals a separate lemma. Every non-elementary input is a cited node, and every cited statement supplies exactly what is taken from it. All uses equal the union recorded in proof_deps, and every use has an exact statement quotation.

Small cases checked: E=F and H trivial (Q=H); trivial valuations (I=Q=1, giving the ordinary automorphism-versus-embedding bound); an immediate extension (e=f=s=1 forces Q=H); a purely inseparable residue extension (s=1, without incorrectly replacing it by f); characteristic-zero residue fields (e prime=e); e a p-power (character bound 1); A trivial and cyclic groups of p-power and mixed order. For cyclic order p in characteristic p, X^p-1=(X-1)^p, illustrating the required loss of the p-part; over the reals, a cyclic order three group has only the trivial character, illustrating why enough roots of unity cannot be assumed. The embedding leaf covers K=L, a separable extension, and a purely inseparable degree-p extension with exactly one embedding.

No statement needed repair. I corrected the proof-source attribution to agent-written because the source's stronger hypotheses and the latest blueprint's actual content must not be silently imported. I also kept the existing embedding upper bound separate to avoid creating a duplicate result. The only unfinished proof is the intentionally statement-only character-count child, as required for a one-level stage-1 split.

## Unfinished work and validation

No unfinished assembly argument. The new unsplit child joins the DAG queue. Required remote validation and direct delivery are run after this review; no local checker, compiler or Lake command is used.
