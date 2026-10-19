## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-jacobian-torsion-closed-base-change.json`: statement, split into seven steps; no Mathlib match for the item. The statement, source, original search records, creation record and blueprint ancestry were retained.
- No new nodes, no new Mathlib leaves. `citations.json` contains the verbatim statement used for every step/node citation. `searches.jsonl` contains the four searches run for this item by Q117.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag and for Jacobian/rig-etale terminology, and searched its ring-theory directories for completed conormal and adic-completion declarations. The hits about Jacobians of curves and ordinary square Jacobian presentations do not state this item. This created item has no Lean audit identifying a project declaration. Upstream master is not used as proof evidence.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Findings and changes

The imported statement is correct, including an arbitrary closed base ideal H and a replacement ideal K with the same vanishing locus; it was retained verbatim. The empty proof was replaced by a proof of the closed case of Stacks Tag 0GB2, with the two-term argument behind Tag 0AJU written out explicitly. The main issue to avoid is treating the kernel of a differential as if it commuted with a nonflat quotient. The proof instead constructs maps h with delta h = a² and h delta = a² and then descends those identities through a surjection of conormal modules.

Read `restricted.tex` labels lemma-topologically-finite-type, lemma-topologically-finite-type-Noetherian, remark-base-change, remark-take-bar / equation-base-change-to-closed, equation-NL, lemma-equivalent-with-artin, lemma-zero-after-modding-out, and lemma-base-change-rig-etale-homomorphism. The displayed map in the proof of lemma-zero-after-modding-out has interchanged base-ring subscripts; no such ill-typed expression is used in this split. This is not a defect in our item's statement. The proof is marked agent-written because it gives a direct elementwise closed-case refinement rather than invoking the source's derived-category comparison as an unrecorded lemma.

The existing unit `sk-p-dl-a1-perverse` and chapter records were read. This is a generic commutative-algebra descendant of the Artin–Gabber/local-duality input in the node's existing ancestry, not a key statement realizing the unit. No unit or chapter record is changed. The ancestor lookup returned `lem-per-artin-gabber-affine-curve`; the existing precise `from.place` and `via` were preserved. Whole-blueprint searches for completion, conormal and Jacobian yielded no equivalent blueprint statement; `same_as` stays empty.

## Not duplicates

No new nodes. Existing completion and radical statements were reused rather than repackaged: `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-adic-completion-mod-ideal`, `lem-weil-pbc-completion-finite-module-tensor`, `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, `lem-weil-pbc-fg-ideal-radical-power`, and `lem-weil-pbc-change-ideal-completion`. Searched the whole DAG for the item's Stacks tags and for rig-etale, conormal, completion-tensor, change-ideal-completion, Noetherian-power and polynomial Noetherianity. Narrow local-completion, one-variable-over-a-field, and Z-polynomial nodes are not being misapplied to the arbitrary base A. No more general node stating the completed Jacobian closed-base-change result was found.

## Mathlib searches

Retained all imported search records. Q117 additionally ran the prescribed msearch wrapper with:

- leanfinder: `Kernel and cokernel of completed conormal Jacobian differential killed by an ideal power after quotient base change` (8 ordinary cotangent/derivation hits);
- loogle: `AdicCompletion, Algebra.H1Cotangent` (0 hits);
- grep: `rig.?[Ee]tale|completed.*[Cc]otangent|[Cc]otangent.*completion` (one hit, AdicCompletion/LocalRing.lean:161);
- leansearch: `Scalar null homotopies of a two term complex with finite free term descend under quotient base change` (8 general homotopy hits).

Read the results and the source of the completion hit, the Jacobi–Zariski comparison, and Extension/Cotangent/BaseChange. The latter explicitly imposes flatness for its cotangent/H1 isomorphisms. This item assumes no flatness of A/H over A and uses completed polynomial derivatives, so these are not exact matches or one-line specializations. General homotopy constructors require the actual homotopy data; the split supplies that data in two elementary computations. No unavailable service was recorded as an absence result.

## Review by Q117

I read the item against Stacks restricted.tex Tag 0GB2 and Tag 0AJU condition (3). The hypothesis concerns the kernel and cokernel of the displayed two-term completed conormal differential, not vanishing of all algebraic differentials of the underlying uncompleted algebra. The quotient E/HE is exactly the complete closed base change in remark-take-bar once the two ideal topologies agree. Tags 0AJP and 0AJQ describe the presentation context, but no new node merely restating those clauses was introduced.

For Step 1 I opened all four cited node files. Finite-type Noetherian permanence really covers both a finite-variable polynomial algebra and a quotient (zero variables allowed); completion Noetherianity really covers completion at any ideal. The completion-mod-ideal node explicitly says the completed ring is complete, so this is not inferred from the definition of completion alone. The Noetherian definition gives finite generation of every ideal. These uses match algebra.tex labels lemma-Noetherian-permanence, lemma-completion-Noetherian-Noetherian and lemma-hathat-finitely-generated, all read in the source. E is Noetherian as a quotient of P, not asserted finite over A.

For Step 2 I opened the finite-module completion-tensor node. Its statement supplies the canonical map and its bijectivity for finite modules over any Noetherian ring. E/HE is cyclic over E and R/HR is cyclic over R; they need not be finite over A. E is complete by the item's hypothesis. Consequently the first application proves completeness of E/HE, while the second identifies P/HP with the completion of R/HR. The tensor-quotient inverse and multiplicativity are written explicitly; neither flatness nor an unexplained preservation of a kernel is used. I read algebra.tex Tag 00MA, part (3), and the closed-quotient remark in restricted.tex for this calculation.

For Step 3 I opened the zero-locus/radical equivalence, finite-generated radical-power and change-of-ideal completion node files. They give respectively the equality of radicals, positive exponents in both directions, and a canonical ring isomorphism from cofinal reindexing. A0 is Noetherian from Step 1, so both ideals are finitely generated. Extending their power inclusions supplies exactly the hypotheses of the completion-change statement on R0 and E0. This proves K-completeness and the actual presentation, not merely a homeomorphism of supports. Sources read: algebra.tex Tags 00E0, 00IM and 0319, and restricted.tex remark-take-bar.

Step 4 cites no non-elementary theorem. I checked q on representatives: pi(J²)=pi(J)² gives well-definedness and surjectivity, and the target is killed by H. Polynomial partial derivatives preserve each I-power, so their continuous extensions and coefficient reductions are compatible directly at every finite level. Cofinal reindexing preserves these equalities. The Leibniz calculation is exactly what ensures each conormal map is defined. Thus the displayed square really commutes; no equality of full algebraic differential modules is hidden here.

Step 5 is an elementary basis lift, followed by the calculations delta(alpha delta - a) = 0 and a(alpha delta - a) = 0. The hypotheses that a kills the cokernel and the kernel are each used once, in that order. The resulting scalar is a², not a; I checked both compositions. This is the elementary two-term core of the source's criterion. Step 6 then factors qh through coordinate reduction because H kills the target, and cancels only the surjections q and rho. Evaluating the two descended identities proves annihilation of the new kernel and cokernel. The new kernel is never identified with the tensor of the old one. These two computations contain the full argument rather than delegating the item's torsion clause to another node.

For Step 7 I reread the Noetherian definition node and checked the finite-generator bound. For t generators of I^c, every degree t+1 monomial has a repeated generator. Thus I^{c(t+1)} is contained in the ideal of their squares, whose image annihilates both modules by Step 6. The previously proved K^v inclusion gives the explicit d=vc(t+1). The zero-generator case is a zero ideal and the inclusion still holds. The c=0 case gives d=0, correctly forcing both modules to be zero.

I checked the other small cases as well: r=0 uses the zero free module and an empty basis, with the same identities; H=0 leaves the conormal presentation unchanged apart from cofinal ideal replacement; H=A gives zero rings and zero modules; I=0 makes the torsion conclusion trivial for a positive power and still requires an isomorphism if c=0; I=A forces the completion P to be zero. No properness assumption on H, I, K or J is introduced. Neither characteristic restrictions nor division by an integer is used.

All proof steps are below 2000 characters. The elementwise steps are short quotient, basis, composition or monomial computations from hypotheses and preceding steps, with all formulas supplied; they do not hide a comparison theorem. Non-elementary completion and radical facts are the statements of cited existing nodes. Every uses entry has an exact statement quote in citations.json, and proof_deps is their union. All generic off-unit tools are declared in split_report.tool_uses. I checked B–E against the actual files: no new-node defects, no clause moved to a replacement node, no target or source statement weakened, and no SGA source. No prior return was supplied.

## Unfinished work

None in the split. Server dry run and delivery are the remaining operational checks, to be recorded after completion.
