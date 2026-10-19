# Q19 — lem-per-exceptional-costalk-gysin

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-exceptional-costalk-gysin.json`: split into nine proof steps; statement unchanged, no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-power-supported-calculus.json`: statement, unsplit; no Mathlib match. Localization, supported restriction and the continuous essentially-finite-type exceptional pseudofunctor, for Z/ell^n.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-power-regular-gysin.json`: statement, unsplit; no Mathlib match. Absolute-purity classes on regular schemes with prime-power coefficients, factorization independence, composition and purely inseparable degree.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-field-exceptional-tensor.json`: statement, unsplit; no Mathlib match. The actual exceptional tensor map for an arbitrary input over a field; also its formal composition identity.
- `citations.json`: the 30 step/node citation pairs, with verbatim statement excerpts.

## Attachments

None. Searches of the project source `WeilConjectures/` by the exact blueprint id and by costalk/Gysin and exceptional-localization concepts found no declaration of this result. General lower-shriek composition declarations do not give the pointwise Gysin comparison. Upstream master's declarations are reference material, not completed proofs.

## WANTED

None. The ILO volume and Scholze six-functor notes are present locally. The earlier sandbox contained the ILO transcription and searches but no item node, split or report. Those searches were read and retained; the field-coefficient tensor question was newly searched. No previous completed work was discarded.

## Problems found and scope

No statement correction was necessary. The arbitrary-input tensor extension in the imported statement needs an explicit tool: the source's displayed calculation starts with a pinned putative dualizing object and hence a rank-one field costalk. That display alone does not prove the assertion for an arbitrary complex M. The new field-base tensor statement isolates this additional input, with its canonical map and no hidden perfectness assumption. Its source field-calculation and six-functor provenance are identified explicitly as an agent extension, not as a literal quotation of an ILO theorem for arbitrary M.

The existing `lem-per-regular-gysin-calculus` and `lem-per-exceptional-costalk-calculus` have coefficients F_ell, not Z/ell^n. They cannot be applied to n>1. I have not silently changed their statements or used an unproved reduction through coefficient extension. The new nodes state the prime-power results directly. The field-base tensor node is not the false assertion that an exceptional tensor map is invertible for every sheaf on an arbitrary base.

For a non-finite-type residue-field morphism, exceptional restriction is computed on a finite-type model and then restricted to its generic point. The supported-calculus node explicitly avoids claiming a right adjoint to a compact-support functor for a non-finite-type morphism. A regular open over an imperfect field need not be smooth; regular absolute purity is therefore essential here.

No clause of the item's conclusion was moved into an identical lemma. The support tool has no Gysin map, twist, or pinning; the regular Gysin tool concerns constant coefficients on regular schemes; the tensor tool has no Gysin or costalk normalization. Steps 1–3 assemble their maps, Steps 4–6 prove the choices/compositions/closed-immersion assertions, and Steps 7–9 compare the specified smooth pinnings.

## Not duplicates

lem-per-prime-power-supported-calculus vs lem-per-exceptional-costalk-calculus: the existing node assumes Lambda=F_ell; the new node works for every Z/ell^n and explicitly supplies the essentially-finite-type residue-field model restriction and its coherent composition. No existing statement gives this generalization.

lem-per-prime-power-regular-gysin vs lem-per-regular-gysin-calculus: the existing node assumes Lambda=F_ell; the new node covers Z/ell^n, retaining the Kummer/diagonal normalization. It is not a specialization of the existing node.

lem-per-prime-power-regular-gysin vs sk-thm-regular: the blueprint theorem assumes an ambient scheme smooth over its perfect ground field and concerns regular closed immersions. The new node allows arbitrary regular excellent affine schemes (including imperfect residue fields) and concerns regular finite-type morphisms and their essentially-finite-type localizations, with composition and inseparable scalar.

lem-per-prime-power-regular-gysin vs thm-pur-regular-immersion-purity: the latter's perfect-ground-field purity setting does not cover the arbitrary excellent/imperfect-field setting or the composition theorem stated here.

lem-per-field-exceptional-tensor vs lem-pur-etale-exceptional-constant-tensor: the existing node's schemes are finite type over an algebraically closed field of positive characteristic, and its tensor variable is a constant coefficient complex. The new node allows an arbitrary base field and a complex on its etale site with its Galois action. Neither existing hypothesis can be discarded by a one-line specialization.

lem-per-field-exceptional-tensor vs lem-trf-exceptional-tensor-open-restriction: that node gives an open-restriction identity on finite-Tor constructible pro-etale categories over the fixed field. It does not prove invertibility on arbitrary ordinary etale field inputs.

lem-per-field-exceptional-tensor vs lem-exc-constant-tensor: that node is a tensor projection formula for an open direct image and a finite constant module, not exceptional pullback with a field sheaf complex.

Whole-DAG searches used the statements, Gysin/absolute-purity keywords, the source's theorem numbers, exceptional restriction/localization, and exceptional tensor/field phrases. Whole-blueprint searches used `Gysin`, `regular closed immersion`, `supported restriction`, `field exceptional`, `regular Gysin`, `exceptional tensor`, and `local cohomology`. None states the added tools. All new nodes retain the nearest imported ancestor `lem-per-artin-gabber-affine-curve` and its complete via chain.

## Mathlib searches

The existing sandbox log was reused for the item, the support node, and the regular-Gysin node. The actual logged LeanFinder, LeanSearch, Loogle and grep queries are recorded verbatim in their `mathlib_searches`. The support searches found localization of O-modules and abstract adjunction composition, which do not supply etale exceptional continuity. The Gysin searches found scheme etaleness, closed-immersion classes and residue-field maps, not Gysin morphisms of sheaf derived categories. The grep hits concerning `finestTopologySingle` are substring matches, not purity results.

For the field tensor node I ran LeanFinder, two plain-word LeanSearch phrasings, Loogle, and grep. The corrected Loogle pattern `CategoryTheory.Adjunction, "tensor"` returns monoidal adjunction unit/counit identities and tensor-Hom adjunctions, not the geometric exceptional tensor isomorphism. The first malformed Loogle expression is recorded as an invalid query, not treated as evidence of absence. LeanSearch returned ordinary pullback/inverse isomorphisms and LeanFinder returned scheme fibre-product tensor-ring descriptions; none gives the desired comparison. The precise queries and results are in the unchanged search log and new output files. No service outage was misreported as an empty successful search, and no unrun query was fabricated.

## Review by Q19

I read the item's source in ILO XVII, Lemma 4.4.1, including the immediately following statements about composition, quasi-finite maps, and smooth pinnings. I also read XVII Proposition 2.4.3.1, Remark 2.4.3.2, the proof of Proposition 2.4.3.3 (where the inseparable scalar is explicit), Lemma 2.4.3.4, Lemma 4.3.1.1 and Lemma 4.3.1.2. For the new Gysin node I read XVI Definition 2.1.1, regular-immersion composition Theorem 2.3.2, Definition 2.5.4 and Theorems 2.5.5/2.5.12, and absolute purity Theorem 3.1.1/Corollary 3.1.2. The source's smooth convention is replaced by the already specified current-blueprint diagonal/deformation convention, through `lem-trf-ambient-diagonal-purity-base-change`; no excluded trace construction is used as a proof input. For the support and field-tensor nodes I read the fibrewise ILO calculation alongside Scholze Proposition 7.14 and Theorems 7.15–7.16, distinguishing the bounded-below ordinary derived category from unrestricted hyperdescent/left-completion categories. The general-input extension is marked agent-formulated.

For C4 I opened every cited node and read its statement. In Step 1 the support node actually states both the fibre comparison and the residue-field model identification; I am not inferring those from adjunction existence. In Step 2 `lem-exc-fields-excellent` and `lem-exc-finite-type-localization-excellent` give excellence of the integral fibre model. The J-2 clause in the definition of excellence makes its regular locus open; `lem-weil-pbc-field-regular-ring` makes its generic point regular, so that locus is nonempty. The new regular-Gysin statement supplies both the class and the virtual-dimension/transcendence-degree equality, including factorization existence. In Step 3 the field tensor node explicitly says its canonical map is invertible for every D+ input, not only perfect inputs. The regular-Gysin class and the supported identification then give the required beta in the displayed direction.

Step 4 uses the restriction/independence clauses of the Gysin tool, restriction/naturality of the tensor tool, and the open compatibility of the supported tool. The common open really contains the unique generic point of the same reduced integral closure. Step 5 uses the composition clause of supported restriction, the constant Gysin composition formula on the essentially-finite-type field tower, and the explicitly stated identity T_(kh)=h!T_k composed with T_h. I wrote out how naturality moves the constant class past T before applying this identity. `lem-kun-transcendence-degree-tower` is the cardinal equality; the finite transcendence degrees here turn it into the asserted integer equality. No tacit comparison of distinct coefficient categories occurs.

Step 6 uses the closed-immersion clause of the support theorem. In that case the residue field and the fibre's reduced closure are the same point, so the Gysin and coefficient maps are identity maps. A nontrivial radicial extension is different: the Gysin node gives degree multiplication, and the tensor map preserves that scalar. This checks the normalization rather than replacing it by an unnormalized isomorphism. In Step 7 I use the new regular-Gysin composition formula for the closed point of the regular localized smooth fibre, and the base-change clause of the specified ambient smooth orientation. Their equality identifies the actual pinning maps, with the exceptional tensor map and supported transitivity named. The statement of `lem-per-regular-pullback-pinnings` supplies the fibrewise recipe being compared. Its potentiality hypothesis is not asserted for an arbitrary M: the comparison uses only the given individual costalk pinnings and the displayed recipe. Step 9 uses exactly the finite-type-over-a-field local-dimension formula stated by `lem-kun-dimension-formula`; the fibre is smooth pure dimension d, so the dimension on its left is d. Rearrangement is elementary.

For B–E, every new node introduces its own coefficients, scheme hypotheses, categories and comparison maps, and has a statement only, empty proof/dependencies and status unsplit. All notions cite their defining nodes or are defined inline. The regular affine hypotheses and localization clauses cover both the chosen regular model and the localized closed-point calculation. No new node is an elementary rearrangement or a clause-only restatement. No step uses a theorem hidden in a definition, a node's proof instead of its statement, or a result stated for a different coefficient category. The explicit helper dependencies point away from this item; no helper refers back to it. The largest proof step has 1434 characters, below the long-step review threshold.

I tested the statements and signs on the identity, a closed point, the empty source (no points to check), the generic point of A^1_k (r=1, degree shift 2), a closed point of a smooth d-fold (c=d, r=0), and a purely inseparable extension of degree p^a (class p^a, a unit mod ell^n). The tensor assertion was also checked against a non-flat Z/ell^n-module Z/ell: the statement requires the derived tensor, so it neither assumes freeness nor replaces it with the underived tensor. Infinite cohomological dimension of k is permitted; the calculation is sheaf-valued on its etale site, not a boundedness claim about global Galois cohomology.

## Unfinished work

No unresolved proof step remains in this one-level split. The three newly stated tools remain unsplit as required for new nodes; proving/splitting them is subsequent DAG work, not a claim that their Lean proofs already exist. No Lean was written and no compiler, Lake, or local preflight/check script was run.

## Final self-review refinements

After the first successful dry run, I made the smooth comparison fully explicit. The support tool now states regular supported base change from ILO XVII Corollary 4.2.3 and its compatibility with the smooth exceptional comparison. This theorem is independent of potentiality. I reread that corollary and Lemma 4.3.1.1; new semantic searches for this additional statement returned regular sequences under flat algebraic base change, etale algebras, and scheme restriction isomorphisms, not the supported comparison. They were recorded from the actual command log. The expanded support tool still has no Gysin normalization or pinning conclusion, and remains a statement-only node.

The final Step 7 separately verifies smooth-fibre regularity and the regular-immersion hypothesis at its localized closed point. I opened the statements of lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-smooth-over-field-regular-local and lem-weil-pbc-regular-local-generators-regular-sequence. The first supplies the fibre's smooth pure dimension, the definition of smoothness identifies affine-locally smooth ring maps, the second supplies regular local rings, and the third makes the maximal-ideal parameters a regular sequence. These generic tools are declared in split_report.tool_uses. This closes C1 gaps that would arise from writing merely “the smooth fibre is regular” or assuming a closed point immersion regular without justification. Final Step 8 writes an equality of inverse-pinning maps, using p_s^{-1}, so their direction is unambiguous; its equality after inversion is the desired equality of pinnings. Final Step 9 is the dimension calculation. No proof step exceeds 2000 characters.
