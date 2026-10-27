## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-good-character-embedding.json`: statement unchanged; split into six steps realizing the two-generator dual-disk embedding and the extra factors detecting differential cokernels.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-character-separates-points.json`: statement, Mathlib leaf, exactly `CharacterModule.exists_character_apply_ne_zero_of_ne_zero`, `Mathlib/Algebra/Module/CharacterModule.lean:220–223` (the character type is defined at line 46).
- `citations.json`: verbatim statement quotes for both uses of the new leaf (steps 3 and 6).

Attachments: none. Searching `lean/WeilConjectures/` for the blueprint tag, good-character/good-sub/character-dual/graded-injective language, and differential-graded constructions found ordinary free-complex resolutions but no project declaration of this DG-algebra statement. The existing declarations are not attachments of the item or the new leaf.

WANTED: none. All sources used were read locally.

What needed correction: the node had no proof. Its source annotation suggests obtaining graded splitting from injectivity, but the source's free two-generator disks already give a graded splitting, which is exhibited explicitly here. There is also a source-proof shift-index error described below. Neither correction changes the item statement, its hypotheses, or the inherited route.

Unfinished work: none for the requested one-level split. The sole new node is already a Mathlib leaf. No Lean was written and no compiler, Lake, or build tool was run.

## Sources and blueprint

I read `literature/stacks-project/dga.tex`, Tag 09KT (`lemma-good-sub`), including the construction of the left two-generator disks and the final paragraph adding character-dual shifts. I read the graded and DG character-duality sections (Tags 0FQC and 0FQD), Tag 09K4 (`lemma-hom-into-shift-dual-free`), Tag 09K2 (`lemma-source-graded-injective`), and the shift convention `definition-shift`. The supporting character-separation assertion is precisely the proof of `literature/stacks-project/more-algebra.tex`, Tag 01DB (`lemma-ev-injective`), specialized to the underlying abelian group. I also read the exact Mathlib declaration and its character definition.

The latest blueprint is the `main-20261024` snapshot pointed to by `literature/blueprint/latest/`, as listed in `COMMITS.txt`. I read its `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), together with the recorded chapter and unit. This item is an inherited DG-resolution prerequisite of that direct-image branch, not the key node of the unit; no unit realization fields are changed. `blueprint_refs.py ancestor lem-sfb-dg-good-character-embedding` reports `None` for the inherited creation chain. The new node therefore retains that computed null ancestor, inherits the full via list with this item prepended, and names the exact character-separation sentences of 09KT served by it. I have not fabricated an imported ancestor.

Whole-blueprint searches for `differential graded`, `graded`, `character dual`, `characters`, `cogenerator`, `09KT`, and `01DB`, and whole-DAG searches for these notions, the tags, and the Mathlib declaration names found no statement of character separation for arbitrary abelian groups. The broad character searches found the algebraic-torus results listed below, whose statements were opened. Searches in the whole DAG for `09K4`, the duality-section labels, and graded-injectivity terminology found this item and the neighbouring DG-resolution/orthogonality nodes, which have different conclusions.

All new searches used the prescribed `msearch.py` command; their returned records are retained verbatim in `searches.jsonl` and in the relevant node's `mathlib_searches`. The item was searched using two semantic phrasings, Loogle, and the DG-specific Mathlib grep. The hits concern ordinary injectives, ordinary cochain complexes, or additive character modules; none supplies the DG-A-linear statement with both specified layers and the differential-cokernel condition. The leaf's LeanFinder, LeanSearch, Loogle, and grep searches all identified its exact declaration. No unavailable search is recorded as a negative result.

## Source error

The last paragraph of Tag 09KT chooses a character of `M^k / d(M^{k-1})` and writes its target as `A^vee[k]`. With the source's own shift convention `M[k]^n = M^{n+k}`, the target must be `A^vee[-k]`. For example take `A = Z` in degree zero and `M = Z` in degree one. There is a character of `M^1` nonzero at 1, but every degree-zero map `M -> A^vee[1]` is zero, since that target is concentrated in degree -1. The target `A^vee[-1]` is in degree one and does detect it. Step 4 uses `V_k = A^vee[-k]` and checks the differential explicitly, so it does not propagate the source's indexing error. The theorem's existential statement, and hence our item statement, requires no correction.

## Not duplicates

No existing node contains source Tag 01DB. The following are the potentially misleading hits for the character notion or declaration name; I read their statements.

lem-sfb-abelian-character-separates-points vs lem-per-divisible-abelian-hom-extension: the latter extends a given homomorphism into a divisible group; it does not assert existence of a character nonzero at a prescribed element.

lem-sfb-abelian-character-separates-points vs lem-per-divisible-group-hom-extension: the latter is the extension property, also specialized to multiplicative groups of algebraically closed fields, rather than separation by Q/Z.

lem-sfb-abelian-character-separates-points vs lem-trf-localization-system-kernel-stabilization: character separation appears in its proof but its statement is eventual injectivity of localization systems. Using that proof as a statement would violate C3.

lem-sfb-abelian-character-separates-points vs lem-sfb-torus-finite-character-separation: the latter separates finitely many algebraic torus characters by one rational point, not an element of an arbitrary additive group by a rational character.

lem-sfb-abelian-character-separates-points vs lem-sfb-torus-nonfixed-complement-annihilation: the latter annihilates equivariant Grothendieck classes using torus characters.

lem-sfb-abelian-character-separates-points vs lem-sfb-torus-coherent-concentration: the latter is localized equivariant coherent concentration on smooth projective schemes.

lem-sfb-abelian-character-separates-points vs lem-sfb-semisimple-characters-trivial: the latter says algebraic characters of a semisimple group vanish.

lem-sfb-abelian-character-separates-points vs lem-sfb-connected-group-characters-torsion-free: the latter proves torsion-freeness of an algebraic character lattice.

lem-sfb-abelian-character-separates-points vs lem-sfb-independent-torus-character-values: the latter prescribes simultaneous values of independent algebraic torus characters.

## Review by Q06

I checked the unchanged item against all three clauses of Tag 09KT: degreewise injection, injection on the cokernel of each differential (not merely injection on cohomology), and a two-layer extension by products of shifts of the character dual. The source says the extension is admissible, meaning split after forgetting the differential. Our displayed sections prove exactly that condition. All actions are right actions over the given associative DG algebra; no commutativity, flatness, boundedness, or finite generation is added.

Step 1 uses the explicit character-dual and shift formulas already in the item. I checked the square of the matrix differential and the two components of the Leibniz rule, particularly the minus sign on the second differential. The projection lands in `V_k[1]`, whose differential is `-d_V`; both kernel inclusion and quotient projection commute with differentials. The graded section is right A-linear, and no assertion that it is a chain map is made. These are direct formula checks, not appeals to an injectivity theorem.

Step 2 also uses no uncited theorem: evaluating a graded coinduced map is explicitly `g(m)(a)=lambda(ma)`. Associativity verifies right linearity, and the commutator `t=g d_M-d_V g` has the required unsign-ed right linearity because the two Leibniz error terms cancel. Substitution into the disk differential proves `d_J f=f d_M`. I checked the degrees of both coordinates and evaluation at the unit. This is the expanded two-generator construction, not a new node restating an item clause.

Step 3 cites only `lem-sfb-abelian-character-separates-points`. Its statement literally supplies an additive character nonzero on the nonzero element of `M^p`; no module-linearity of that character is assumed or needed. The graded coinduction formula from step 2 supplies DG-A-linearity of the disk map. Products, the exact sequence, and its section are all constructed coordinatewise, so exactness of arbitrary products is not a hidden input. The index is a set of characters and integers in the chosen universe bound.

Step 4 does not cite a Hom-adjunction node: it proves the needed special case by evaluating both sides on an arbitrary homogeneous `a`. I checked the exponent `(-1)^k(-1)^{p-k+1}=(-1)^{p+1}`, the fact that `ma` has degree `k-1`, and the use of `lambda d_M=0`. Evaluation of boundaries at 1 vanishes because the derivation identity gives `d_A1=0`. The calculation needs no hypothesis that the original representative is a cocycle, which is essential for differential cokernels.

Step 5 combines previously constructed maps and gives both the kernel and the graded section explicitly. The extra character-dual product goes into the first layer, so the extension still has exactly two layers. Reindexing the first layer by the disjoint union of the two index sets is an equality of coordinate data. No general product-exactness theorem or graded-injective-product theorem is used.

Step 6 again cites precisely the character-separation leaf, now on the abelian group `C_k`. Its exact statement gives the nonvanishing character claimed in the step, as quoted in `citations.json`. Projection of a boundary to a DG factor is a boundary by the chain-map equation. Step 4's evaluation identity rules this out in the selected factor. Hence the quotient map has zero kernel, not just an injective restriction to cohomology classes. Both citations were checked against the new node's actual statement rather than against its source proof.

For the new leaf I checked B1–B7: the file is statement-only with empty proof and proof dependencies, introduces `G`, `x`, `chi` and the quotient group, has its own Stacks tag and label, and contains no hidden external setup or proof sketch. Its Mathlib match is exact at lines 220–223; the line-46 definition identifies the target with Q/Z. The statement works for finite cyclic groups (send a generator of order n to 1/n), for Z (send 1 to 1/2), and for arbitrary torsion or mixed groups; for the zero group the nonzero-element hypothesis is impossible. I read the local proof of 01DB rather than inferring separation from an unrelated injectivity definition.

For C1–C8 and D1–D5 I checked that every non-elementary input is the cited leaf, all other steps are written formula computations, no cited proof is substituted for a node statement, and no cycle or off-unit non-Mathlib tool is introduced. There is no new node for an item clause or for an elementary matrix calculation. Each proof step is below 2000 characters; there is no long step hiding a separate lemma.

For E1–E7 I checked the zero DG module, the zero algebra (whose unital modules are zero), degree-zero algebras, positive and negative shifts, and unbounded modules. All products are degreewise; the proof never interchanges them with an infinite direct sum. For a zero module both maps remain injective and the extra zero characters cause no problem. For a module with nonzero differential, including the two-term identity complex, the quotient-character argument still concerns all differential-cokernel classes; it does not inadvertently require cycles. The source's shift error was repaired explicitly as recorded above. No statement dispute in the item's own statement remains.

The preliminary server `review_split` check passed before this report. This self-review was performed under the direct-delivery brief; no second worker or subagent was started. The delivery remains subject to the maintainer's independent review.

The first full dry run requested an explicit notion citation on the new leaf and a numeric `mathlib_match.line`. I added the same universe convention as the item, with `stmt_deps = [def-weil-size-convention]`, and `line = 220` verified in the pinned source. The convention was read: it fixes the universe bounds and has no role in character separation itself. The citation quotes were regenerated verbatim from the scoped statement. No mathematical hypothesis or proof step changed.
