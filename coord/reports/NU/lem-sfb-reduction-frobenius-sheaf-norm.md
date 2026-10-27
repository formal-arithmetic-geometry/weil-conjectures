# Worker report: lem-sfb-reduction-frobenius-sheaf-norm

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-reduction-frobenius-sheaf-norm.json — statement unchanged; six-step split; no exact Mathlib match.
   - citations.json — ten verbatim statement excerpts, one for every step/node citation.
   - searches.jsonl — six actual searches through the required msearch command; all services answered. The item retains its six inherited Q59 searches and adds the six NU searches. No inherited work was discarded.
   - report.md — this report.
   No new DAG nodes and no new Mathlib leaves.
2. Attachments: none. Searched WeilConjectures/ for the exact blueprint tag/id and for Frobenius/norm/reduction/nilradical combinations. Ring Frobenius and uniform nilradical nilpotence already have project declarations, but neither states this item. In particular AlgebraicGeometry.Scheme.exists_nilradical_pow_succ_eq_bot belongs to the existing lem-sc-reduction-nilradical-nilpotent, not to this norm item.
3. WANTED: none.
4. The live item was statement-only and had no lean_audit record or Lean attachment. Stacks 0BDZ supplies the affine construction but explicitly leaves gluing details omitted. Those details are now the proof itself; no new node repackages the item. No statement dispute, hypothesis change, or source correction was needed.
5. Unfinished mathematical work: none for this stage-1 split. The six assembly steps and their supporting existing nodes cover every clause. Independent maintainer review remains part of the delivery process.

## Sources and reuse

Read Stacks divisors.tex, Tag 0BDZ (lemma-Frobenius-gives-norm-for-reduction), and Tag 0BCX (section-norms): the norm conditions are multiplicativity, composition with restriction equal to the indicated power, and preservation of vanishing at the image point. The affine construction actually gives unital ring homomorphisms in characteristic p, as the item states. Read algebra.tex, Tag 00IM (lemma-Noetherian-power), for the nilpotent-ideal input; varieties.tex, Section 0CC6 after Definition 03SM, for the Frobenius ring homomorphism; schemes.tex, Tags 01J3 and 01J4, for reduction; and morphisms.tex, Tag 01QO (lemma-closed-immersion), for the affine quotient description.

Read the item's chapter, dag/units/sk-thm-sf-ctf-stability.json, and the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The newest snapshot is main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8. This item is supporting input far below the recorded direct-image/ampleness chain, not the key statement of the unit, so no unit record is changed. blueprint_refs.py ancestor prints a null ancestor; preserved it and the existing detailed from.place/via chain. Searches `ring Frobenius`, `reduction norm`, and `nilradical nilpotent` of the whole imported blueprint found no equivalent item: the single reduction/norm result is an adic tower definition, about different objects.

Searched all DAG statements/titles for ring Frobenius, nilradical nilpotence and reduction norms; opened every cited node. Reused def-weil-ring-frobenius, lem-sc-reduction-nilradical-nilpotent, def-weil-pbc-scheme-reduction, def-weil-closed-immersion, def-weil-residue-field and def-pc-scheme. Read the project's ReductionNilradicalNilpotence.lean and Mathlib/Algebra/CharP/Lemmas.lean project extension as source only. No compiler, Lake or build was run.

The NU search hits concern iterateFrobenius/frobenius, perfect closures, arithmetic Frobenius, and reduced scheme properties. pNilradical_eq_bot_of_frobenius_inj assumes Frobenius injectivity and concludes a zero p-nilradical; it does not construct a reverse map on a nonreduced scheme. PerfectRing.lift_aux concerns a p-radical ring map, with an element-dependent exponent and no sheaf norm. None states this item or specializes to it in one line. The two different natural-language phrasings and both grep patterns are recorded exactly as run. No new node required any searches of its own.

## Tool use

lem-sc-reduction-nilradical-nilpotent is a generic statement about every Noetherian scheme, even though filed in the curve-estimates unit. Its conclusion is exactly the uniform nilpotence input to Stacks 0BDZ. It neither assumes a curve nor uses this item. Declared this use in split_report.tool_uses. The remaining citations are definitions or Mathlib leaves. This follows the given local Frobenius/nilpotence route.

## Review by NU

I checked the unchanged item directly against divisors.tex 0BDZ and the two norm conditions in 0BCX. The source assumes Noetherianity and p times the structure sheaf zero; the item spells Noetherianity as a finite Noetherian affine cover and imposes precisely this characteristic condition in local rings. Its e >= 1 is the source's e > 0. The extra ring-homomorphism and affine-formula clauses are properties of the displayed construction, and Step 4 proves the ring laws rather than assuming a norm is additive.

Step 1 uses the reduction node's quotient sheaf and identity on points, and the nilpotence node's full statement, which is for an arbitrary Noetherian scheme and explicitly includes the empty scheme. Its positive exponent n is the cited node's n+1 renamed. Taking q >= n annihilates each product of q nilradical germs. A single e works everywhere. No affine exponent is silently reused on another chart.

Step 2 takes the ring endomorphism and iteration formula from def-weil-ring-frobenius: its statement has exactly p prime and p times 1 zero, permits the zero ring, and gives the p^e power map. The local-ring hypothesis implies p=0 in every section ring by equality of germs. Restriction preserves powers as a ring map. I separately checked the empty open, where the ring is zero and its unique endomorphism is unital; no nontrivial-ring hypothesis is added.

Step 3 uses the quotient sheaf in the reduction statement, not surjectivity of global sections on an arbitrary open. Each quotient germ has a representative, so lifts exist after shrinking. Two representatives differ by a section of the kernel sheaf, and the same exponent from Step 1 kills its q-th power on every stalk. The Frobenius node supplies the exact identity a^q-(a')^q=(a-a')^q. This proves agreement on overlaps without assuming they are affine or choosing lifts globally.

Step 4 applies the sheaf axiom inherent in the locally ringed space in def-pc-scheme. I wrote the local lifts for the sum, product and unit and used the cited ring-Frobenius homomorphism to verify each law. Gluing uniqueness proves independence of covers and compatibility with every restriction. This is a direct sheaf-axiom computation, not an unproved comparison lemma.

Step 5 first uses the global lift a itself to check the composite on every open. For an affine open only, def-weil-closed-immersion explicitly provides a quotient presentation and surjectivity on affine sections. The reduction node identifies the kernel as the nilradical. Thus the quotient is A/sqrt(0), and the formula follows by taking any representative. Both cited statements say exactly these facts; I did not infer surjectivity of arbitrary global sections from an epimorphism of sheaves.

Step 6 uses the homomorphism of residue fields supplied in def-weil-residue-field. A local lift a maps to b in the quotient, so its residue maps to b(y). The elementary injectivity argument for field homomorphisms is written out. Hence b(y)=0 forces a(x)=0 and the constructed power also vanishes. No preservation of arbitrary zero loci or residue-field isomorphism is assumed.

For B–E of delivery-errors I checked that there is no new unsplit node with an embedded proof, no duplicate, no new clause disguised as a node, no uncited non-elementary lemma, no citation to a dependency's proof instead of its statement, and no SGA source. Each citation has a literal excerpt in citations.json. Only Step 1's nilpotence theorem and Step 2's Frobenius theorem are used as substantive results; the other steps write out their elementary local and sheaf consequences. All steps are shorter than 2000 characters.

Small cases checked: X empty; V empty; X reduced (then every positive e works); X=Spec(F_p[epsilon]/epsilon^r), including r>p, which rules out fixing e=1; p=2; disconnected X with different nilpotence orders; and a nonseparated Noetherian scheme, whose affine intersections need not be affine. The proof handles them all. I corrected no statement and introduced no new node: the main issue to avoid was treating the reduction quotient as surjective on every open's sections. The local-lift argument explicitly avoids that inference.
