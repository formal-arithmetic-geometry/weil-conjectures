# Stage-1 repair: prime coefficients in smooth proper curve families

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-proper-smooth-curves-prime-coefficients.json: statement; repaired split, not a Mathlib leaf.
- citations.json: 56 citations, one entry for each use in the nine proof steps, with the cited node's full statement copied verbatim.
- report.md: this report.
- searches.jsonl: the five fresh searches logged by msearch.py. Their actual results are appended to the item's mathlib_searches; the inherited search records are retained.

New nodes: 0. New Mathlib leaves: 0. All subsidiary facts are reused from existing nodes.

## Attachments

None. I searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id, the recorded properSmoothCurves_prime_higherDirectImage_constructible name and proper smooth curve/constructible concepts. The hits concern individual curves, Jacobians or reductions, not this theorem for families over a Noetherian base. The recorded stage-2 Lean signature is retained verbatim and is not evidence of an attachment.

## Wanted literature

None. All sources needed for this repair are present.

## What was wrong and what changed

The repair note of 2026-10-17 explicitly reopens old Step 2: its 2185 characters combine proper base change, Noetherian topology, quotient-ring Noetherianness, and gluing of immersed stratifications. The request keeps the statement, the other proof steps, and the Lean record. I followed that scope.

Old Step 2 is replaced by Steps 2--4. Step 2 uses the existing minimal-closed-subset and compact-subset statements, the existing Noetherian-open-subscheme leaf, immersion-local-finite-type and locally-Noetherian permanence leaves, and the existing locally-Noetherian quasi-separatedness leaf. This replaces the finite affine cover and quotient ascending-chain proofs with named inputs. Step 3 is proper base change on the two pieces and permanence of the family hypotheses. Step 4 uses the existing generic constructible-stratification assembly node, with its qcqs ambient hypothesis now explicitly verified, and the existing inverse-image composition node. It does not hide a fresh gluing lemma. No new node is justified: the DAG already contains all these facts.

Steps 1 and old Steps 3--6 are unchanged (now 1, 5--8). Old Step 7 is now Step 9; only its final step references are renumbered. The finite-stalk, invertible-locus and characteristic-prime Artin--Schreier route of Stacks 0GKV is preserved. The statement, stmt_deps, source, blueprint ancestry, all audit and review fields, and the entire Lean record remain unchanged. The removed proof dependencies are lem-sc-affine-noetherian-underlying-space, pqf-lem-affine-open-locnoeth, lem-weil-pbc-proper-fp-permanence and pqf-def-locnoeth, since their former inline argument is replaced by more directly applicable statements. No existing node is edited or deleted.

I read the current main-20261015 proper-base-change unit and the ancestor finiteness proof. The ancestor contains a historical forbidden-source reference; this delivery takes its curve argument solely from the allowed Stacks source, and adds no such reference. There is no change to the unit or chapter route and no statement dispute.

## Not duplicates

No new nodes are introduced. In particular I reused rather than recreated:

- lem-weil-pbc-noetherian-open-subscheme-noetherian for open subschemes;
- lem-weil-pbc-immersion-base-change-lft and pqf-lem-locnoeth-lft for local Noetherianness of the closed piece;
- lem-weil-pbc-noetherian-scheme-closed-subsets-minimal and lem-sfb-noetherian-space-compact-subsets for the topology and compactness arguments;
- lem-weil-pbc-locally-noetherian-quasi-separated for the ambient qs hypothesis;
- lem-weil-pbc-constructible-stratification-assembly for the finite immersed-partition assembly;
- lem-weil-pbc-inverse-image-composition for composite restrictions.

I searched the whole DAG by Noetherian/open/closed/subscheme/stratification concepts, inspecting actual statements rather than metadata matches, and used blueprint_refs.py searches for Noetherian, constructible-stratification, closed subsets and proper smooth curves, together with ancestor lookup. The existing statements cover the necessary arguments and no additional Mathlib leaf is created.

## Review by NS

I read the worker brief, stages/1-dag.md, the three blueprint levels in SETUP.md, delivery-errors.md B--E in full, GOAL.md, dag-sync.md, the chapter and unit records, the item's current JSON, its 2026-10-17 repair note and earlier NV report. The sandbox initially had no node or report, so this starts from the current repository proof rather than inventing another route.

For the item I read more-etale.tex, Tag 0GKV, label lemma-proper-smooth-family-curves, from the Noetherian reduction through both coefficient cases and the Artin--Schreier conclusion. For the new applications I read properties.tex, labels lemma-locally-Noetherian (01OW), lemma-locally-Noetherian-quasi-separated (01OY), lemma-Noetherian-topology (01OZ) and lemma-locally-closed-in-Noetherian, and topology.tex, lemma-constructible-in-constructible (09YJ). I also read the actual etale stratification argument at etale-cohomology.tex, lemma-etale-stratified-finite (03S0). The assembly node is used for what its own statement asserts; I do not treat 03S0 alone as a theorem about arbitrary module sheaves. There are no new node sources to audit.

I opened and read every statement cited by every proof step, and checked the following specific inferences.

1. The exchange-forgetting statement identifies module and abelian higher images. cor-weil-pbc-geometric-fiber-finite gives the exact stalk formula, and lemma-constructible-pullback-constant identifies the fibre input. lem-sc-c5 explicitly permits the characteristic prime and every nonnegative degree. Proper base-change permanence and smooth-relative-dimension permanence supply the smooth proper curve hypotheses. The given nonempty connected geometric fibres provide connectedness and dimension one, not an unstated projectivity hypothesis.

2. The minimal-closed-subset statement applies to a Noetherian scheme, meaning locally Noetherian and quasi-compact. If a strictly descending closed chain existed, its members would contradict its asserted minimal element; this is the only elementary conversion here. The compact-subsets statement explicitly assumes precisely this descending-chain condition and gives compactness of every subset. The closed immersion identifies |Z| with its closed image, so it is compact, and all intersections needed for retrocompactness of U are compact. The open-subscheme leaf states the full Noetherian conclusion, not just its local part. The immersion-lft leaf states local finite type for every immersion, so it applies to the closed immersion Z -> S; pqf-lem-locnoeth-lft then supplies local Noetherianness. Combining that with the compactness just established is the definition of a Noetherian scheme. The qs leaf asserts exactly the missing qs hypothesis for S. Thus no quotient-ring permanence, finite-union topology or compactness theorem remains unrecorded inside this step.

3. The prime-base-change statement supplies the canonical derived exchange for the underlying abelian sheaf of a prime-field module, for arbitrary base maps and proper f. The forgetting comparison explicitly supplies the module exchange and reflects its being an isomorphism. Pullback of the constant coefficient sheaf is exactly the constant coefficient sheaf. The properness and smooth-relative-dimension statements permit these two base changes. At a point of an open subscheme or a closed subscheme the residue field is unchanged (for the closed immersion this follows from the quotient description in def-weil-closed-immersion), so the geometric fibres here are those in the hypothesis. Neither a perfect base nor a reduced closed subscheme is assumed.

4. The constructible-subset definition includes Boolean closure and retrocompact opens; it makes both U and its complement Z constructible. The assembly statement asks for a finite disjoint covering by constructible immersed images in a qcqs scheme, plus finite constructible stratifications on the pieces. Step 2 verifies qcqs and retrocompactness; the chosen open and closed subschemes give precisely the two immersions. With P(h) = finite local constancy of h^{-1}G_q, the composite restrictions have P by the inverse-image composition statement. That statement is for abelian sheaves, so I explicitly checked the coefficient issue: its isomorphism is natural for every scalar-multiplication morphism, and the forgetting comparison identifies the abelian inverse images with those of modules. It is therefore a module isomorphism. The assembly node's conclusion then gives exactly the partition and restriction conditions of def-weil-pbc-etale-constructible-sheaf. This is a genuine use of its statement, not of a construction hidden in its proof.

5. The smooth-proper specialization statement applies to the constant F_ell module on the source curve when ell is invertible on U, and provides all the specialization isomorphisms. The finite-stalk criterion assumes a finite ring, finite geometric stalks, a Noetherian base and precisely those bijective specialization maps. The ring F_ell is finite; Steps 1--3 give the remaining hypotheses. Its finite locally constant conclusion gives the one-stratum constructible partition.

6. The characteristic-p curve-vanishing statement has q>1 and applies to the geometric fibres. The stalk formula and stalk conservativity give zero higher images for q>=2. The sections-upstairs statement assumes flatness, quasi-compactness and connected geometric fibres, all available on every etale base change from smooth-flat, properness and the permanence statements. Pullback of constants and naturality of section pullbacks identify the degree-zero sheaf with the constant sheaf. Zero and constant module sheaves have the required finite one-stratum models. This step makes no local-freeness assertion about O_Z.

7. The two scheme Artin--Schreier statements work on a scheme with p=0 in its global functions, including a nonreduced scheme, and use the same sectionwise universe lift. The direct-image left-exactness statement and enough-injectives statement give the hypotheses of the right-derived universal-delta-functor theorem. Its long exact sequence yields the displayed short exact cokernel/kernel segment by exactness at the adjacent terms. The middle sheaf is the underlying abelian first higher direct image, as required; the structure sheaf is never claimed finite as an F_p module.

8. The structure-direct-image statement supplies O_Z and E_et with the natural scalar action and with E finite locally free, rank allowed to vary. The section-data statement supplies sectionwise p-th power. The higher-image presheaf statement gives local representatives as cohomology classes over etale base objects. Applying cohomology to F m_a = m_(a^p) F gives semilinearity, and the restriction formula retains it under sheafification. The Frobenius-vector-bundle statement asserts zero cokernel and constructible abelian kernel for an arbitrary additive semilinear F; it does not require F invertible. Apply it separately to O_Z and E; the short exact segment identifies the middle sheaf with the latter kernel. This step remains 1382 characters and is one explicit functoriality calculation, with all its non-elementary inputs named.

9. The two constructibility definitions specify finite additive charts and finite module charts respectively. The constant-stalk statement identifies the additive chart value with a geometric stalk on a nonempty chart; p kills that group. Its F_p action is forced by repeated addition, so additive chart maps are F_p-linear. Forgetting commutes with all stratum inverse images. The finite partitions on the two pieces therefore satisfy exactly the hypotheses of Step 4, yielding the desired finite module partition on S. Only the cross-references in this retained step were renumbered.

The two generic off-unit statements newly used in the proof, assembly and inverse-image composition, are declared as tool uses in split_report.tool_uses with their specific roles. They support the source's U/Z reduction and do not replace the unit's theorem route. All other newly cited statements are already Mathlib leaves, so they are tools under the contract. I did not modify the maintainer-owned tool_uses field.

Small cases: empty S, empty U (pure characteristic ell), empty Z (ell invertible everywhere), and nonreduced Z=V(ell) are covered. In the empty case the stratifications can be empty; the Noetherian and compactness conclusions hold vacuously. I checked q=0, q=1 and q>=2 separately, P^1 (rank-zero H^1 of the structure sheaf), and ordinary versus supersingular elliptic fibres, where Frobenius-fixed ranks may jump and only constructibility is concluded. No invertibility of ell on S, reducedness, projectivity, fixed global genus or perfectness of S is added.

B--E audit: no new node can be elementary, duplicated, a restated clause or an unsearched Mathlib match because there are no new nodes. The item statement and Lean record are unchanged. All nine proof steps have complete arguments, citations and source places; all are below 2000 characters. I checked citation meaning (C4) as above, used named statements for non-elementary inputs (C1), and generated each citations.json quote from the statement field actually read. No proof_deps contains an unused citation. The five fresh Mathlib searches returned only subset constructibility, etale sites, etale ring maps, profinite locally constant functions and stalk-rank results; I read every hit's returned type, and none states curve-family higher-image constructibility. LeanSearch was available this time and is correctly recorded as available with no match. No previous unavailable verdict is rewritten.

## Unfinished work

No mathematical part of the assigned repair is left open. This delivery introduces no new unresolved statement; its existing dependency nodes keep their existing states. No Lean files, builds or compiler commands were used. Server-side preflight results are recorded below after the required dry run.
