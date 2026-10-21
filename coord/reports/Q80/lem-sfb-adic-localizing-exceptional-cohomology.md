# Q80 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-localizing-exceptional-cohomology.json`: existing item, statement and stmt_deps unchanged; three assembly steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-proper-localizing-adjunction-comparison.json`: one new statement-only node, status unsplit, no Mathlib match.
- `citations.json`: exact statement excerpts for every citation of the item's three steps.
- `searches.jsonl`: real msearch records, retained as generated.

## Attachments

None. I searched the notion and blueprint id in lean/WeilConjectures and read the indicated Sheaf module. The item's only declaration in that module ends in sorry (line 73); it cannot be an attachment. Generic adjunction transports in WeilConjectures are not this geometric comparison.

## WANTED

None. All source material used is already in the read clone.

## Existing work and defects addressed

The assignment describes a 5702-character proof. On first read, the live item already carried the Q39 repair reviewed on 2026-10-21: six steps totaling 2221 characters, an unsplit predicate-comparison node, and a Mathlib transport leaf. There was no prior Q80 item, report, or search log in the sandbox. I used that current item as the base and retained its statement, searches, metadata, existing comparisons and route. Following the explicit instruction that this remains a deliberate re-split, I extracted a different argument: matching both ordinary constructible presentations AND the actual proper-pushforward adjunction. This comparison contains no conclusion about constructibility of an arbitrary supplied right adjoint, so the item still has to apply the geometric restriction theorems and prove its conclusion using uniqueness.

The new comparison is the bridge between different coefficient-category interfaces, not a renamed instance of generic adjunction transport: its input hull is generated using the stratified locally-finitely-presented predicate, whereas the geometric functors live on the finite-constant-model, finite-Tor hull. Both object properties and the proper left functor have to be matched before applying the existing transport leaf. No new elementary topology or categorical transport node was created.

## Proof in words for lem-sfb-adic-proper-localizing-adjunction-comparison

The following is the complete four-step comparison argument extracted from the live item. The new JSON is deliberately statement-only so another worker can develop this argument.

1. The field $k$ is Noetherian since its only ideals are $(0)$ and $(1)$. Thus [lem-weil-pbc-finite-type-over-noetherian] makes $Z,Y$ Noetherian and quasi-compact. They are quasi-separated: their separated diagonals are closed immersions, which on affine charts are spectra of quotients and hence quasi-compact. By [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal], a descending closed chain has a minimal term and stabilizes. Thus their spaces, and every subspace given by a locally closed stratum, are Noetherian.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.

2. For $T=Z,Y$, [lem-sfb-adic-constructibility-predicate-comparison] applies to step 1 and the specified certificate; hence $\mathcal B_T=\Dbc(T,\Lambda)$.

Uses: lem-sfb-adic-constructibility-predicate-comparison.

3. The qcqs hypothesis in step 1 lets [det-def-localizing-closure-ctf-equals-bc] give $\Dbc=\Dctf$. The hull definitions [def-sfb-bounded-constructible-localizing-closure; sk-def-localizing-closure] now intersect the same properties containing the same generators, with the same ambient $u+1$-indexed coproducts. Hence $\mathcal L_T=\Loc(\Dctf(T,\Lambda))$.

Uses: det-def-localizing-closure-ctf-equals-bc, def-sfb-bounded-constructible-localizing-closure, sk-def-localizing-closure.

4. Let $J=g^!$ and $Rg_!\dashv J$ be supplied by [sk-prop-sf-existence]. Properness gives $Rg_!\cong Rg_*|_{\mathcal L_Z}$ by [det-cor-existence-ii-restriction](1), whose right side is the actual $F_g$ of [lem-sfb-adic-proper-localizing-pushforward]. Apply [lem-sfb-adjunction-transport-left-iso] to obtain $F_g\dashv J$ on exactly these hulls.

Uses: sk-prop-sf-existence, det-cor-existence-ii-restriction, lem-sfb-adic-proper-localizing-pushforward, lem-sfb-adjunction-transport-left-iso.

5. The adjunction in step 4 has the claimed Hom formula by the statement of lem-sfb-adjunction-transport-left-iso: for $h:F_gM\to N$ it is $a_{M,N}(h\circ e_M)$. The object-property equalities identify full subcategories on the same ambient objects; all morphisms, identities, composition and full-inclusion functors are inherited from $D_T$. The bounded inclusions therefore agree as well. These are explicit identifications of ordinary ambient categories, with indexing universe $u+1$ fixed throughout; no completion or completed coproduct enters.

This handoff preserves every argument in former steps 1-4. In particular the geometric Noetherian checks, the existing non-elementary predicate comparison, the finite-Tor comparison, the same-coproduct check, and the actual compact-support-to-proper-pushforward isomorphism were not suppressed. Former steps 5-6 remain in the item as steps 2-3, with their internal step references repaired.

## Not duplicates

lem-sfb-adic-proper-localizing-adjunction-comparison vs lem-sfb-adic-constructibility-predicate-comparison: the latter compares the two constructibility predicates on one Noetherian scheme; it does not identify the finite-Tor localizing hulls and the actual proper-pushforward adjunction on them. It remains an input, not a second new predicate comparison.

lem-sfb-adic-proper-localizing-adjunction-comparison vs det-def-localizing-closure-ctf-equals-bc: the latter begins with the finite-constant-model predicate and proves finite Tor amplitude; it does not compare the lfp predicate or the two proper left functors.

lem-sfb-adic-proper-localizing-adjunction-comparison vs det-cor-existence-ii-restriction: the latter identifies proper compact support and ordinary pushforward on the finite-Tor hull and restricts to Dctf; it does not match that hull to the general ring-object lfp constructible interface. The new comparison has no geometric restriction conclusion.

lem-sfb-adic-proper-localizing-adjunction-comparison vs lem-sfb-adic-proper-localizing-pushforward: the latter proves that the actual pushforward preserves the lfp hull and has coproduct/shift properties; it supplies neither the comparison with the finite-Tor hull nor the compact-support adjunction on that presentation.

lem-sfb-adic-proper-localizing-adjunction-comparison vs lem-sfb-adjunction-transport-left-iso: generic Mathlib transport assumes an isomorphism between functors on already fixed categories. The new comparison establishes the geometric inputs and applies this existing leaf; it does not reintroduce the generic fact as unsplit.

lem-sfb-adic-proper-localizing-adjunction-comparison vs lem-sfb-adic-localizing-exceptional-cohomology: the item concerns cohomology constructibility for ANY supplied right adjoint; the new comparison identifies the geometric compact-support adjunction and has no constructibility conclusion for its right functor. The coefficient restriction and uniqueness arguments remain in the item.

I searched the whole DAG by the comparison, hull, proper-adjunction and predicate words; searched the whole imported blueprint with blueprint_refs.py (proper direct image, localizing hull, local-finite-presentation, compact support Brown); and inspected the above closest existing statements. No blueprint node states the combined comparison. The ancestor command returns None because created.item of the existing item is a Lean module name. Accordingly the new node uses null from.node, with the exact source place and via=[item], following the existing predicate comparison's convention; the item's existing filled blueprint is retained.

## Mathlib search review

All searches are real calls of batch2/msearch.py and their query strings are copied unchanged from searches.jsonl. Two different LeanFinder formulations return sheaf pushforward-as-right-adjoint declarations, scalar local cohomology or condensed module infrastructure. Those have the wrong functors and do not identify finite-Tor/lfp constructible hulls. LeanSearch returns localization-of-complexes and derived-category API, with no geometric comparison. Loogle returns Adjunction.ofNatIsoLeft and its Hom-equivalence formulas: I read Mathlib/CategoryTheory/Adjunction/Basic.lean at lines 493-518 and reused the existing Mathlib leaf. Grep across Mathlib and a second grep focused on AlgebraicGeometry return generic monadic adjunctions or Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean; I read that file, whose definitions are the ordinary integral ell-adic sheaf and cohomology, not compact-support exceptional functors or these hull comparisons. Thus the new geometric comparison remains unsplit; no additional Mathlib leaves are introduced.

## Review by Q80

I read coord/delivery-errors.md B-E in both recorded versions, the worker and stage-1 instructions, GOAL.md, the three blueprint levels in SETUP.md, the chapter and unit records, and the current node. I read det-existence-restriction.proof.md in main-20261015: its rational and integral bullets prescribe exactly the restriction route retained here. For the new node I also read sk-cor-existence-ii-restriction.proof.md (1), which uses the identity compactification for a proper morphism. The comparison proof above preserves current steps 1-4 literally and exposes the Hom formula. No SGA source is used.

Step 1 cites sk-prop-sf-existence for the actual compact-support adjunction and the new comparison for the equality of bounded generators, equality of ordinary hulls including their full inclusions, and transport to the same actual F_g. Both statements explicitly give those clauses; citations.json quotes them. The schemes are separated and finite type over the specified positive-characteristic field, the prime is invertible, and proper g is separated of finite type. The certificate has exactly its three constructors (including the specified multiplication), not an arbitrary isomorphic or completed coefficient ring. The algebraic closure keeps its finite-subextension meaning. Universe u+1 controls the ambient coproducts on both sides.

For the new comparison's handoff I read the full statements of lem-weil-pbc-finite-type-over-noetherian (Noetherian base required), lem-weil-pbc-noetherian-scheme-closed-subsets-minimal (closed-set minimality), lem-sfb-adic-constructibility-predicate-comparison (Noetherian scheme and certificate), det-def-localizing-closure-ctf-equals-bc (qcqs, the listed adic rings), both hull definitions (ordinary ambient coproducts), sk-prop-sf-existence (compact-support Brown adjunction), det-cor-existence-ii-restriction (1) (properness and actual ambient pushforward), lem-sfb-adic-proper-localizing-pushforward (definition of the actual F_g), and lem-sfb-adjunction-transport-left-iso (orientation Rg_! to F_g and explicit Hom formula). A field is Noetherian; finite type then supplies Noetherianity and qc. Separatedness supplies qs. The existing closed-set minimality statement gives descending-chain stabilization and Noetherian strata, so no finite-stratification finiteness hypothesis was lost. The three coefficient constructors meet the finite-Tor comparison hypotheses. The hull argument keeps the same object properties, coproducts and replete full inclusions throughout.

Step 2 cites the certificate for the three cases, sk-thm-restriction for E and Qbar, det-prop-int-brown-adjoint for identification of the integral Brown right adjoint with J after Dctf=Dbc, and sk-thm-int-restriction for its Dctf preservation. I read each complete statement; each says precisely the clause used. Step 1 puts the bounded input K in Dctf. The restricted geometric setting and morphism hypotheses in those statements all follow from the original hypotheses, and neither boundedness of the output nor derived completeness is assumed in this step.

Step 3 cites det-sp-unique-right-adjoint for the isomorphism between G and J as right adjoints to exactly the same F_g. I read its counit-compatible natural inverse statement. The full inclusion and the homology functor send this to an isomorphism of modules. Step 2 and the generator comparison make H^n(JK) constructible in the general lfp sense. I read def-sfb-constructible-module: its finite-stratification and local-presentation witnesses pass across an isomorphism by pulling it back on each cover and composing the presentation isomorphism with its inverse. This last operation is explicitly written in the retained item step and is elementary; no new isomorphism-invariance lemma is invented.

I tested the new comparison on the empty schemes (zero derived categories), the identity of Spec k (the identity compactification and identity adjunction), and integral torsion inputs such as O_E/(varpi) in degree zero (allowed finite presentations and finite Tor amplitude, not assumed free). Finite nonregular torsion coefficients are deliberately excluded: Dbc=Dctf fails there, as the existing finite-Tor comparison explains. Arbitrary characteristic-zero or non-finite-type schemes are not silently included. No extra flatness, derived-completeness, field algebraic closure or output constructibility hypothesis was added. Statement and stmt_deps of the item are unchanged. No item proof step exceeds 2000 characters, and its entire assembly is below 3000 characters.

## Unfinished work

Only the new comparison remains statement-only, as requested; its complete handoff argument and sources are above. No Lean was written and no compiler, Lake or local preflight/check_dag/review_split was run. Required server dry run and delivery results are recorded below after execution.

## Validation

The required deliver.py --no-push process exited successfully: OK (not pushed), preflight passed at 7c62543893e. Both node files parsed, exact citations were accepted, all real search records were accepted, and the server preflight (including check_dag and review_split) passed. A final dry run follows this report update before the authorized direct push. One new unsplit statement, zero new Mathlib leaves.
