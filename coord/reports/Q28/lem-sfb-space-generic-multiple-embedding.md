## Worker report

Files written under dag/nodes/sec-six-functors-basics/:
- lem-sfb-space-generic-multiple-embedding.json: item, split; mathematical statement unchanged.
- lem-sfb-space-generic-freeness.json: statement, unsplit; no Mathlib match.
- lem-sfb-space-homs-over-open.json: statement, unsplit; no Mathlib match.
- lem-sfb-space-power-ideal-kills.json: statement, unsplit; no Mathlib match.
- lem-sfb-space-artin-rees.json: statement, unsplit; no Mathlib match.

Attachments: none. Searched the exact item id and generic embedding/rank, Artin-Rees and generic freeness in lean/WeilConjectures. SpreadGenericProductEmbedding, CoherentHomsOverOpen, CoherentIdealPowerTorsionFreeProduct and the coherent patching modules are scheme results, not declarations of this algebraic-space assertion. There were no AlgebraicSpace/algebraic-space hits in the algebraic geometry subtree supplying the missing result. No Mathlib declaration is offered as an attachment.

WANTED: none.

The original item had no proof. Its source correctly points to the last paragraph of Stacks 07UT, ending before the property hypothesis (3)(b). I expanded its generic-rank, extension and kernel-removal argument, without changing the statement. Its ancestry command prints None, as for its already reviewed parent: I preserved that inherited node value and via chain, making each new supporting place precise. Read the current blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md (3), and the chapter and unit records. This prerequisite lies below the existing coherent-devissage/finite-affine-descent chain; no unit route was changed. No Lean was written and nothing was compiled.

Four inputs remain unsplit by design. No proof obligation of the item is left outside its named dependencies. citations.json contains all nine step/node pairs and verbatim statement excerpts.

## Searches

Before creating any node I searched the whole DAG for tags 07UQ, 07UM, 07UK and 07UL and their labels, for generic freeness and closed-space ideals. The only tag-bearing nodes were the item, its coherent-devissage parent, and coherent-ideal-filtration. I read their statements: none states one of these four tools. I also read the existing reduced-closed-support, closed-immersion-quasi-coherent-modules, coherent-kernel-cokernel-extension and noetherian-coherent-support statements and reused them. blueprint_refs searches for each of the four tags and homs-over-open returned zero; the broader generic and Artin searches provided no equivalent assertion about coherent modules on algebraic spaces. New ids were checked against all DAG filenames.

Every new node has two LeanFinder phrasings, LeanSearch, Loogle and source grep, run through the required msearch.py. The exact queries and actual service summaries are in mathlib_searches and searches.jsonl. All services answered. Ring localization generic freeness (Module.FinitePresentation.exists_free_localizedModule_powers, Localization/Free.lean:78) does not give the dense schematic open of a space. Ideal.exists_pow_inf_eq_pow_smul (RingTheory/Filtration.lean:389, source read) is the affine module theorem, not its globalization with a uniform constant on an algebraic space. Module.support_eq_zeroLocus does not supply ideal-power annihilation on the etale ringed site. The remaining hits were scheme denominators, ideal-sheaf zero loci, ambient Hom objects and completions. Thus none is a one-line specialization of the four statements. The item itself was also searched; inherited searches were retained and the new actual queries appended.

## Not duplicates

lem-sfb-space-generic-freeness vs lem-sfb-space-coherent-devissage: generic triviality of one coherent module is a tool, not the property-devissage theorem.
lem-sfb-space-generic-freeness vs lem-sfb-space-coherent-ideal-filtration: generic triviality gives one free restriction; the existing node gives a global finite filtration with closed-support ideal factors.
lem-sfb-space-generic-freeness vs lem-sfb-space-generic-multiple-embedding: the new lemma concerns one sheaf on an open; it asserts neither a global comparison nor injectivity of an ideal multiple.
lem-sfb-space-homs-over-open vs lem-sfb-space-coherent-devissage: the new node extends arbitrary morphisms from an open, without any property P.
lem-sfb-space-homs-over-open vs lem-sfb-space-coherent-ideal-filtration: the new node gives the Hom colimit, not a filtration.
lem-sfb-space-homs-over-open vs lem-sfb-space-generic-multiple-embedding: extension gives no injectivity and works without reducedness, irreducibility or full support.
lem-sfb-space-power-ideal-kills vs lem-sfb-space-coherent-devissage: supported modules are annihilated by an ideal power; no property P is involved.
lem-sfb-space-power-ideal-kills vs lem-sfb-space-coherent-ideal-filtration: annihilation by a prescribed ideal power is not stated by the filtration theorem.
lem-sfb-space-power-ideal-kills vs lem-sfb-space-generic-multiple-embedding: annihilation handles a supported kernel; it neither creates generic isomorphisms nor gives embeddings.
lem-sfb-space-artin-rees vs lem-sfb-space-coherent-devissage: the new node states a uniform intersection formula, not property devissage.
lem-sfb-space-artin-rees vs lem-sfb-space-coherent-ideal-filtration: a uniform intersection formula is not the filtration assertion.
lem-sfb-space-artin-rees vs lem-sfb-space-generic-multiple-embedding: the new node has an arbitrary coherent ambient module and submodule, with no generic-rank comparison.

The scheme versions in other chapters (coherent-homs-over-open-extension, coherent-artin-rees, ideal-power torsion lemmas) assume a scheme and do not cover an arbitrary algebraic space. No new node is an elementary consequence of the statements being cited, or a clause obtained merely by renaming the item.

## Review by Q28

I read spaces-cohomology.tex, lemma-property-higher-rank-cohomological (07UT), especially the two ideal-power inclusions, the common-open isomorphism, its extension, and the kernel argument. I read lemma-prepare-filter-irreducible (07UQ), including the paragraph that chooses a dense open scheme and shrinks to a free module; that paragraph is the precise source for generic-freeness, rather than incorrectly claiming its statement says generic freeness. The new generic-freeness node assumes Noetherian, reduced, nonempty irreducible X and full support. These are exactly the hypotheses that make the open scheme integral and the finite generic rank positive. This new lemma does not move the final comparison into a duplicate node.

For homs-over-open I read the full statement and proof of 07UM: its source is coherent, its target only quasi-coherent, and the transition maps restrict to deeper ideal multiples. The new node states that isomorphism and its existence consequence, without claiming the extension is injective. For power-ideal-kills I read 07UK: it requires coherence and a Noetherian space, and only set-theoretic containment of support. For artin-rees I read 07UL, including its affine-atlas reduction: the submodule is quasi-coherent and the constant applies to all n at least c. I copied its intersection formula with the exponent n-c in the correct position. All four new files contain statements only, with every object introduced and their notions either defined inline or tied to actual definition nodes. TeX escapes were checked in decoded strings.

Step 1 uses exactly the generic-freeness conclusion, twice. Intersections of nonempty opens are nonempty by the item's irreducibility hypothesis; a=s and b=r give equal free rank rs, so the coordinate reindexing really is an isomorphism in the stated direction. There is no hidden claim that G or H is globally torsion-free.

Step 2 uses reduced-closed-support for the existence of the closed subspace, and separately closed-immersion-quasi-coherent-modules for the surjective ring map and its quasi-coherent kernel. The first statement alone does not provide the defining ideal, which is why both are cited. On an affine chart the quotient ring vanishes precisely outside the closed image, giving the unit ideal on V. The noetherian-coherent-support node says O_X is coherent and quasi-coherent submodules are coherent, so it applies to I. Local products of finite generating sets give the coherent ideal products; coherent-kernel-cokernel-extension supplies finite direct sums by split extensions. Neither the scheme-only closed-immersion definition nor a source tag alone is used as a theorem about spaces.

Step 3 uses the actual existence clause of homs-over-open with source G^a and target H^b. Step 2 checked their coherence. The kernel/cokernel theorem states precisely that its kernel is coherent; restriction of a kernel is sectionwise, and f is the chosen isomorphism on V, so its support lies in Z(I). The coordinate identity I^n(G^a)=(I^nG)^a is simply multiplication of tuples, not an appeal to tensor exactness.

Step 4 applies power-ideal-kills to this coherent K, obtaining I^d K=0. Artin-Rees is applied inside the coherent module M=I^n(G^a), not inside G^a with a mismatched exponent. With m=c+d its stated equality gives I^m M intersect K = I^d(I^c M intersect K), contained in I^d K=0. This explicitly proves injectivity of the restricted morphism and explains the final exponent n+m. I corrected the potential ambiguity of the source's phrase 'after increasing n' by writing both independent exponents and this calculation.

Step 5 defines J=I^(n+m). Local products give the domain (JG)^a; J is the unit ideal over V. Nonemptiness of V makes its structure sheaf nonzero, so J is nonzero, even if n+m=0. All positivity and isomorphism clauses are retained. This step uses only the established objects and local product identities.

Small cases: on Spec(k), positive ranks r,s give a=s,b=r and J=O. For G=O plus a coherent torsion summand supported on the complement, the initial extension can have a nonzero kernel; the Artin-Rees restriction, not multiplication of that kernel alone, removes it. The formula remains valid for d=0 (K=0) and c=0. The empty scheme is excluded by irreducibility, not by an added hypothesis. For the three general tools, I=O forces supported F=0 and the formulas reduce correctly; I=0 makes U empty and n=1 supplies a zero source in the Hom colimit. Generic-freeness explicitly excludes F=0 through full support on nonempty X. Nonreduced or reducible X is not inadvertently allowed in that node, whereas the other three correctly allow it. No step exceeds 2000 characters and no hidden comparison lemma remains in a long step.

I checked B1-B10 (statement-only new files, self-contained hypotheses, definitions, TeX, exact tags and labels, honest searches and no false attachment), C1-C8 (actual theorem citations, quotes from statements, existing-node reuse, no ancestor dependency and no off-unit theorem), D1-D5 (argument carried in the item; four genuinely smaller tools) and E1-E7 (hypotheses, correct ambient module, exponent calculation and edge cases). All sources are Stacks and the latest blueprint; no SGA route is used.
