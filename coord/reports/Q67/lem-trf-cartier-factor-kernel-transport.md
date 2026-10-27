# Stage-1 delivery: lem-trf-cartier-factor-kernel-transport

## Files written

- dag/nodes/sec-trace-formula/lem-trf-cartier-factor-kernel-transport.json: statement item split into six proof steps; Mathlib verdict no match. Statement unchanged. No new nodes, no Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the ten step/node citation pairs.
- report.md: this report. searches.jsonl is the actual msearch log; prepare.py is sandbox-only preparation code.

## Attachments

None. Searched the upstream project source under lean/WeilConjectures for the exact item id, strictTransform/strict_transform, blowup and Cartier. The scheme strict-transform and blowup algebra declarations do not state the module-kernel transport assertion with its two inclusions and both supported-section formulas. No sorry declaration was treated as a finished proof.

## Wanted literature

None. All sources used are present in literature/stacks-project. The proof is marked agent because the explicit section transport argument assembles the existing facts; it is not a verbatim proof supplied by Tag 080H.

## Problems in the input and corrections

The statement is sound and was retained. It had no proof. The key distinction is that this item only describes the two kernels; equality of them needs the later no-supported-sections hypothesis and is not asserted here. I did not import that hypothesis from Tag 080H (2), or infer equality merely because the blowups are isomorphic.

The product ideal's finite type and the equality of its underlying vanishing subset with the union are proved explicitly. The word "transports" has been replaced in the proof by section bijections commuting with restrictions, their inverse, and the inverse image of the included submodule under these bijections.

Added def-nagata-invertible-ideal to statement dependencies to name the local rank-one meaning of invertible. No definitions or targets were changed. All original source, created, chapter, unit and blueprint ancestry fields are preserved. The blueprint ancestry explains this item's supporting position below the Orgogozo modification route; it does not assert that the current blueprint's local-term proof itself states Cartier kernel transport.

## Unfinished work

None in this stage-1 split. The reused non-elementary lemmas remain their existing DAG items. This delivery does not claim a Lean proof or close those dependencies.

## Not duplicates

No new nodes. Searched the whole DAG and imported blueprint before choosing dependencies, including searches for 080D, 080H, supported sections, strict transform, Cartier ideals, and pullback quasi-coherence. Existing lem-trf-strict-transform-sheaf-kernel gives the kernel and quasi-coherence for a single centre; the present item adds explicit common-ambient transport for two centres and their support union. Reused that node rather than introducing a second kernel lemma. Existing lem-trf-supported-kernel-blowup-charts serves the later affine torsion comparison and is not required for the current transport proof.

## Review by Q67

I read Stacks divisors.tex, the paragraph preceding definition-strict-transform (080D), that definition, and lemma-strict-transform-different-centers (080H), including its full proof. I also read properties.tex lemma-sections-supported-on-closed-subset (07ZP), divisors.tex lemma-characterize-effective-Cartier-divisor (01WS), and modules.tex lemma-pullback-quasi-coherent (01BG). I checked the tag-to-label correspondence in tags/tags. No forbidden SGA route is used. There are no new-node sources to review.

I read the chapter and unit records and the latest blueprint files for sk-i-curve-zero and lem-trf-local-term-locality, plus the latest invertible-factor statement. This supporting calculation stays under the existing modification input and changes neither the unit's route nor its statement. The latest blueprint root is the 2026-10-23 snapshot recorded in COMMITS.txt. Whole-blueprint keyword searches found no equivalent statement; same_as remains empty.

For step 1, I opened lemma-nagata-effective-cartier-is-invertible, which says exactly that an effective Cartier ideal is invertible; I use only that statement, not its inherited proof. The local regular-generator and finite-generator hypotheses come from the opened statements of def-nagata-effective-cartier-ideal and pqf-def-coherent. Multiplication by x is injective on the ideal because it is injective on the ambient structure sheaf. Its image is the product ideal, giving quasi-coherence and finite type locally. The prime-ideal argument proves the union equality; it does not identify schemes defined by different nilpotent thickenings.

For step 2, I opened lemma-nagata-blowup-invertible-factor: its conclusion supplies the base isomorphism, and its only factor hypothesis is the invertibility just established. I opened def-pc-fibre-product and checked it states the projection identities, induced morphism and uniqueness needed to construct alpha and its inverse. I opened def-pc-module-pullback, whose statement explicitly includes composition isomorphisms. Thus the pullback identification follows from p alpha = p_D without any flatness assumption. For the Mathlib search hit I also read Scheme.Modules.pullbackCongr and pullbackComp in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean, lines 241 and 261; they only cover these generic comparisons, not the item's strict-transform assertion.

For step 3, I opened the complete statement of lem-trf-strict-transform-sheaf-kernel. It asserts both the kernel description and that the included kernel is quasi-coherent. Its hypotheses require a finite-type quasi-coherent centre and a quasi-coherent module; those are satisfied for the original centre by the input and for the product centre by step 1. Applying it twice does not assume that pullback along f preserves regular elements. I checked the dependency closure of this cited lemma does not return to this item, so this citation is not circular.

For step 4, the cited module-pullback definition gives inverse image followed by tensor extension. I spell out the inverse to tensor extension along the structure-sheaf isomorphism. The unit sends s to 1 tensor s, which commutes with restriction. Since alpha is a homeomorphism, every open of T_D is the inverse image of a unique open of T. Consequently these bijections define the transported subsheaf on all opens, including its inclusion and quotient morphism; this is a direct special case of the definition, marked elementary rather than a new lemma.

Step 5 uses only the projection identities, the established product-support equality and the section bijections. I checked its preimage-of-complement identity as a set identity on points, and checked that zero restriction is equivalent in both directions because c on the smaller open is injective as well as surjective. This proves the formulas for all opens rather than merely stalkwise isomorphism of abstract modules.

For step 6, I opened lem-weil-pbc-module-pullback-quasi-coherent: it applies to every scheme morphism and every quasi-coherent module, so beta = alpha inverse and L_D satisfy its hypotheses. Its quasi-coherence conclusion is all that is used. The section identifications already constructed identify beta pullback L_D with K_D. The affine-local definition in pqf-def-coherent makes invariance under this module isomorphism immediate. This generic result and the two Nagata tools are explicitly declared in split_report.tool_uses; no trace-formula route is replaced.

I checked the edge cases I = 0 (the blowup is empty, so the formulas have zero section modules), I = O_S, D empty, X empty, and F = 0. In particular take S = Spec k[x], I = O_S, D = V(x), X = S and F = O_D: both blowups are S, but K = 0 and K_D = F, exactly as the two formulas say. Thus the proof does not smuggle in the false conclusion that the kernels are equal without the missing torsion-free hypothesis. Finite type of F, Noetherianity, separation, and flatness are nowhere assumed. No affine-intersection claim is made.

I checked delivery-errors B to E against the final item: no redundant or clause-restating nodes were created; every non-elementary invocation names a node that states the needed fact; every citation quote in citations.json is copied verbatim from that node's statement; all steps are below 2000 characters; proof_deps is the union of the uses. Genuine searches were performed using the mandated msearch command and retained as run, including two distinct semantic phrasings. Generic kernel.mapIso, ideal-kernel lemmas, and pullbackCongr do not imply the whole item by a one-line specialization. No project, launcher, or Lean file was written, no git command was run in the shared repository, and no compiler/build tool was invoked.
