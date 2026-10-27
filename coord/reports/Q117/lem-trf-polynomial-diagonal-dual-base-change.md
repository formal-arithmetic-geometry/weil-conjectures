# Q117 stage-1 report: lem-trf-polynomial-diagonal-dual-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-polynomial-diagonal-dual-base-change.json: statement item, split in six steps using only existing nodes; no Mathlib match for the complete statement.
- citations.json: one entry per step citation, copying the full current cited statement verbatim.
- report.md: this report. searches.jsonl is the unedited search-command log.

No new nodes and no new Mathlib leaves. No unit file changed: this auxiliary is not the unit's key node.

## Attachments

None. Searched lean/WeilConjectures by the exact item id, polynomial diagonal/dual language, coinduction and dual base change. The étale upper-shriek base-change files and sheaf coinduction from abelian groups do not state this ordinary-module result. No project declaration giving all clauses was found.

## Wanted literature

None. All sources needed for the assembly and the existing tool lemmas are present.

## Findings and changes

The live item had an empty proof. Its statement is correct, including its assertion in D(B) before cancellation and its use of the second coprojection. Statement, statement dependencies, source, created and all other inherited records were retained. The proof uses the existing flat polynomial quotient perfectness, perfect biduality and flat quotient coinduction comparison; duplicating those as new nodes would be wrong. The graph cancellation is written out on K-flat representatives rather than made into a node that merely repeats a clause of the item.

Read the current latest blueprint locality proof and its statement, the chapter and unit records, GOAL.md, the three-level route restriction, and delivery-errors.md B--E (including the historical repeated copy). The ancestor is the locality theorem's nearby-cycle/relative-duality auxiliary branch, through the inherited chain to the polynomial diagonal reduction; this split does not replace any unit step. Blueprint searches for polynomial diagonal, coinduction and biduality found no blueprint statement equal to the item: the biduality hits are coefficient/geometric duality, not this polynomial module package.

The five new Mathlib searches were run with the required msearch.py and their actual JSON log entries were appended to the pre-existing item searches. Both semantic phrasings were read. LeanFinder returned cotangent-complex and ordinary scalar-change facts, LeanSearch ordinary dual base change and flatness, Loogle the ordinary restriction/coextension adjunction, and grep unrelated polynomial text. Inspected ModuleCat.ChangeOfRings (coextendScalars at 520, restrictCoextendScalarsAdj at 659) and Dual.BaseChange (baseChange at 45, baseChange_baseChange at 56, toDualBaseChange at 113). These are ordinary module facts; toDualBaseChange even assumes a finite free module. They do not attach the derived coinduction package or prove every clause in one specialization.

## Not duplicates

No new node exists, so there are no new/existing-node overlap pairs. In particular, the existing lem-trf-flat-polynomial-quotient-perfect, lem-trf-perfect-complex-derived-biduality and lem-trf-coinduction-flat-quotient-base-change were reused. The more general perfect Tor-independent coinduction base-change nodes were read too; the existing Noetherian flat quotient version already suffices for M=P[0].

## Review by Q117

I read more-algebra.tex Tag 068X (lemma-perfect-over-polynomial-ring), Tag 07VI (lemma-dual-perfect-complex), Tag 0A6A (lemma-base-change-RHom) and Tag 08YU (lemma-double-base-change), including the warning immediately before 08YU that the two possible output module actions can differ. I also read the flat finite-presentation perfect-map lemma (067J) and the polynomial perfect-map characterization (068Y). For the enhanced coinduction comparison I read dualizing.tex Tag 0BZM (lemma-flat-bc-surjection), Tag 0E2A (lemma-check-base-change-is-iso) and the counit construction just before it. These say exactly why the comparison is an A'-object and why its underlying map is the RHom base-change map. There is no use of an SGA source.

For step 1 I opened the complete statements of lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-flat-tensor-exact and def-weil-pbc-flat-ring-map, and read algebra.tex Tags 00FN and 00HD. The Noetherian lemma applies separately to P over R and S and B over A1; each has the displayed finite polynomial presentation. The tensor lemma applies to injections of underlying R-modules because A1 and A2 are flat over R by hypothesis. The balanced identifications show flatness of P to S and each coprojection without relying on an uncited base-change theorem. This step is elementary relative to those cited statements, with the identifications and inverses written explicitly.

For step 2 I read the full existing flat polynomial quotient perfectness statement. Its first application has base R and algebra A2; the second has base A1 and algebra B. Both bases and both algebras are Noetherian; finite type is supplied by the fixed presentation, and step 1 supplies the second flatness hypothesis. The node states perfectness of the quotient over its polynomial presentation, which is exactly the needed conclusion. It is not merely the definition of a perfect ring map.

For step 3 I read def-trf-derived-coinduction, lem-trf-perfect-complex-derived-biduality and lem-sf-ringed-derived-closed-symmetric-monoidal. Coinduction's statement identifies the restriction of E with RHom_S(B,S) and fixes the precomposition action. The biduality statement includes BOTH perfectness of the dual and the canonical evaluation isomorphism; it is not being used for a statement found only in its proof. I explicitly supplied its braided-structure and universe convention using the small one-object ringed-site monoidal statement. Thus it applies to the B object already proved perfect over S.

For step 4 I read the entire statement of lem-trf-coinduction-flat-quotient-base-change. It requires a Noetherian P, a quotient P to A, a flat map P to P', and bounded-below M. Here these are P to A2, P'=S and M=P[0]. The balanced identification A2 tensor_P S=B is written with its inverse; it carries A2 to the second coprojection, not the first. The cited statement asserts the comparison in D(A'), hence D(B), with its coinduction action; it is not just an underlying S-linear comparison. The ordinary algebra tensor factor has degree zero, so changing its displayed position contributes no Koszul sign.

For step 5 I read the full statements of lem-pc-kflat-resolution, lem-pur-kflat-change-of-rings and lem-pc-derived-tensor-second-factor-functor, together with the monoidal statement cited in this step. Read sites-cohomology.tex 06YS (lemma-K-flat-resolution) and 0G7E (lemma-pullback-K-flat) as well. They supply a K-flat A2-complex Q with flat terms, K-flatness of its B-extension, the derived tensor computation and symmetry to compute in the K-flat factor. No flatness of A over B is claimed or needed. The two cancellation maps are inverse balanced chain maps, and A2 to A is the identity under the specified identification of copies. This uses general K-flat facts plus an explicit two-line tensor calculation, so there is no hidden new lemma or restatement child.

For step 6 the calculation is elementary: multiplication by s on the A factor is multiplication by mu(q(s))=a1 times p-bar, and the explicit cancellation formula carries it to exactly that scalar on Q. This verifies the restriction along e and accounts for both actions, including the first-copy scalar after cancellation. It cannot be replaced by a cancellation over the first coprojection without changing which given action is tracked.

All twelve citation entries quote a verbatim complete statement from the node actually cited by that step. Every non-elementary ingredient is a cited statement. Generic off-unit K-flat and monoidal tools are declared in split_report.tool_uses, with the purpose of each; all other non-leaf proof nodes are in this unit. I checked the small cases n=0 (a flat quotient), A=R, A=0, R=0, and R a field with A=k[epsilon]/(epsilon^2). The argument never requires smoothness, regularity of A, or a flat multiplication quotient B to A; singular flat algebras and zero rings cause no failure. No statement correction is needed. Each proof step is below 2000 characters; no long step hides a separate lemma. No unsupported source download, Lean edit, compiler, git command or write in the shared repository was used.

## Unfinished work

None in this stage-1 split. Existing proof dependencies remain separate DAG items with their own existing states; no new unsplit obligation was introduced.
