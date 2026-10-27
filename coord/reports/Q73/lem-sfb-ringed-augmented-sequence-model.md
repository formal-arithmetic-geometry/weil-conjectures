# Worker report: lem-sfb-ringed-augmented-sequence-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-augmented-sequence-model.json`: statement, split into eight proof steps; no whole-item Mathlib match. Added the definition of flat module sheaves to statement dependencies. The mathematical statement is unchanged.
- No new nodes; zero Mathlib leaves created.
- `citations.json`: one exact statement quotation for every proof-step citation, numbered from 1. Full statements are quoted to keep all their hypotheses visible.
- `searches.jsonl`: actual Q73 command results; the item's older Q123 searches are retained as history. `write_split.py` records the sandbox JSON construction.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag and for augmented sequences, telescopes and tensor-cone comparisons found no declaration stating every clause of this item. The existing KFlatClosure and telescope-colimit declarations cover inputs, not this whole statement. Statements containing sorry in Sheaf are not attachments.

## WANTED

None. The proof uses the local Stacks sources and existing DAG statements; no model-category existence assertion or additional reference is needed.

## Problems found and changes

The imported item had no proof. Choosing unrelated K-flat resolutions would not produce maps representing the supplied successor arrows. Choosing an arbitrary map between cones would not prove the requested natural tensor comparison. The split repairs these gaps by an induction using the flat-terms clause of Tag 0G7D, followed by an explicit comparison on the two copies of the cone.

The item's source field names derived.tex, although Tags 06YS and 06YM are in sites-cohomology.tex. The proof steps and proof_origin give the actual files and labels. Some existing input nodes also have broad historical 06YS citations for closure; the relevant source labels read here are lemma-K-flat-two-out-of-three (07A3) and lemma-colimit-K-flat (06YR), rather than asserting that 06YS itself states closure.

The inherited blueprint.from.node is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-ringed-augmented-sequence-model` returned `None`. Its long inherited via chain and place are retained. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3); this auxiliary telescope calculation is the inherited supporting input, not the unit's key statement. No unit record is changed. Blueprint searches for `ringed augmented sequence model`, `K-flat complex mapping telescope`, `telescope` and `K-flat` found no blueprint node stating the item. The generic functor-preserves-hocolim node gives a comparison of selected triangles, not compatible strict models and a natural chain isomorphism.

The isomorphism to a supplied telescope is existential and can be nonunique (0CRH). Naturality is the strict tensor-cone comparison and its localization in compatible strict models and coefficient complexes; it does not assert a functorial cone choice for arbitrary commutative squares in the triangulated derived category. There is no change of statement or statement dispute under this reading.

## Unfinished work

None in the stage-1 split. Proofs of cited unsplit nodes remain their own items. No Lean file was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. The DAG was searched globally for Tags 06YS, 06YM, 090Z, 0CRH, 0CRI and keywords K-flat, telescope, hocolim, roof, sequence, coproduct and cone. Existing lem-pc-kflat-resolution, lem-pc-kflat-cone-direct-sum, lem-pur-kflat-map-factorization, lem-kun-complex-colimit-hocolim and the other named tools are reused. In particular no new node merely restates strictification or tensor compatibility as a clause of the item.

## Mathlib searches

All new searches used the required msearch.py command and were read. The first LeanFinder query returned ordinary Module.Flat tensor-exactness statements; the second returned mapping-cone cochain and additive-functor comparisons. LeanSearch returned HomologicalComplex.tensorObj/tensorHom and ordinary-module tensor/direct-limit results. Loogle `"mappingCone", "tensor"` and grep `telescope|hocolim|homotopyColimit|mappingCone.*[Tt]ensor|[Tt]ensor.*mappingCone` in Algebra/Homology returned no hits. None simultaneously represents an arbitrary sequence of derived sheaves and proves the full telescope, roof and coefficient-action assertions. The two distinct semantic formulations were both run and logged. No unavailable service was counted as absence.

## Review by Q73

I read derived.tex definition-derived-colimit (090Z), remark-uniqueness-derived-colimit (0CRH), remark-functoriality-derived-colimit (0CRI), lemma-direct-sums, lemma-compute-colimit, lemma-colim-hocolim, the cone convention, and lemma-third-isomorphism-triangle (014A). I read sites-cohomology.tex lemma-K-flat-resolution (06YS), lemma-factor-through-K-flat (0G7D), lemma-derived-tor-exact (06YM), lemma-K-flat-quasi-isomorphism (06YP), lemma-derived-tor-quasi-isomorphism-other-side (06YT), lemma-K-flat-two-out-of-three and lemma-colimit-K-flat. I also read injectives.tex theorem-K-injective-embedding-grothendieck (079P), the K-injective Hom computation of derived.tex 070I, and sites-modules.tex lemma-tensor-commute-colimits (03EP). No SGA source is used.

Step 1 uses prop-pur-kinjective-resolutions-exist for exactly its small-ringed-site Grothendieck and K-injective existence assertions. The statement of lem-sf-kinjective-replacement-triangulated explicitly gives a fully faithful equivalence from K-injectives to D; therefore each successor arrow has a homotopy-class representative between the chosen I_m. Picking chain representatives is enough because a forward sequence has only one path between comparable indices. No simultaneous strictification theorem for arbitrary indexing categories is smuggled in.

Step 2 uses lem-pc-kflat-resolution for its flat-term, surjective quasi-isomorphism at the initial index, and lem-pur-kflat-map-factorization for precisely its homotopy factorization and final flat-terms clause. Its hypothesis is K-flatness of the source, which the induction maintains, and not projectivity or K-projectivity. Equality after Q follows from def-weil-abstract-derived-category's equivalence with homotopy-category localization. This was the main correction to the tempting but invalid lifting of each derived arrow between arbitrary fixed K-flat resolutions.

Step 3 uses both clauses of lem-pc-kflat-cone-direct-sum: closure under countable sums and under the cone of a chain map. Lem-kun-complex-colimit-hocolim explicitly states that the degreewise sum localizes to the coproduct with its given insertions and that its cone triangle is a telescope, for general module sheaves over a ringed site. It is not just a result for constant coefficients or bounded complexes. The maps v_m are isomorphisms of sequences by Step 2, so the first square commutes on each insertion. TR3 is explicitly in def-weil-triangulated-category; lem-sf-triangle-morphism-iso states the needed two-out-of-three conclusion. The resulting comparison respects the supplied connecting map as well as the legs. I checked 0CRH to avoid claiming uniqueness.

Step 4 uses lem-weil-pbc-independent-sheaf-tensor-colimits only for ordinary module-sheaf tensor and small coproducts; its coefficient-universe hypothesis is supplied by the item's smallness convention. Commutativity of O permits the sheafified flip when the fixed tensor factor is on the other side. The remaining interchange of coproduct indices and the two differential terms is written out and is elementary from the tensor-complex definition, not a new categorical theorem.

Step 5 uses the exact cone matrix in def-weil-abstract-derived-category and the signed differential of def-pc-tensor-complex-sheaves. I checked the shifted generator with original P-degree a: its L-differential has sign -(-1)^a on the source and (-1)^(a-1) on the target. These are equal, so no extra sign belongs in the map. The off-diagonal cone term has coefficient +1 on both sides. The reverse rearrangement is its actual chain inverse. The formula for the leg is checked in the unshifted copy. This is a routine matrix calculation written in the item, not an uncited tensor-cone theorem.

Step 6 checks strict naturality on both cone copies. Lem-pc-kflat-closure actually states that countable sums of flat sheaves are flat, giving flat terms for T; lem-weil-pbc-kflat-fixed-tensor-triangulated consequently applies to T and all P_m. That node states preservation of arbitrary quasi-isomorphisms in the varying factor, so its use does not assume L flat. The equality for a coefficient roof follows by multiplying the already established naturality equality by the inverse of the denominator, not by making a fresh choice of cone map.

Step 7 treats roofs in the strict model variable separately. Prop-pur-kinjective-resolutions-exist supplies exact filtered colimits; the countable sum is a filtered colimit of finite biproducts, which proves its exactness. Src-weil-homology-preserves-exact-colimits states homology preservation for any exact colimit shape, including this discrete countable sum. This justifies the quasi-isomorphism on the two sums. Lem-sf-triangle-morphism-iso then applies to the actual cone map. Lem-pur-quasi-iso-cone-acyclic supplies its acyclic cone and lem-pc-kflat-cone-direct-sum its K-flatness. Lem-pur-acyclic-kflat-tensor-arbitrary explicitly permits arbitrary L, not merely K-flat L. The two-copy formula already proved in Step 5 identifies the tensor of that cone with the cone of the tensor map. Thus both functors invert the denominator before it is inverted in the naturality equation. No claim about all incoherent morphisms in Fun(N,D) is used.

Step 8 is the balanced-tensor generator calculation from def-pur-sheaf-tensor-product, with differential from def-pc-tensor-complex-sheaves. The commuting actions are needed for balancing, and the fact that the action is on the complex L means it commutes with d_L. The comparison is identity on these generators, so it is B-linear in both cone copies and after localization. Flatness of B over R is never used. For roofs retaining the action, underlying quasi-isomorphisms remain the ones inverted; their inverses retain the action by the same commuting equation.

I tested the zero ring and empty site (all constructions are zero), the zero sequence, zero transitions (1-s is identity and its cone is contractible), an identity constant sequence (its ordinary colimit and telescope agree), and L=0. For the cochain signs I tested a single homogeneous P-degree a and L-degree b, including odd a, on the shifted and unshifted copies. The induction works at m=0 and adds one arrow at a time; it makes no boundedness claim. Unbounded totalizations use sums in every degree, not products. The B-linear check allows B nonflat, for example R=Z and B=Z/2 acting on a suitable L. Every proof step is below 2000 characters and contains no hidden existence or comparison lemma beyond its explicitly cited statements.

The split_report declares the generic tools used from other units and explains why each is a black box here. The unit route is preserved: this is the inherited supporting telescope calculation below the direct-image/constructibility route, not a replacement of a unit step. I checked each cited node's statement directly, and citations.json preserves a verbatim copy for every use; no proof-only construction is being cited as if its node asserted it.
