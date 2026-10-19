# Q90 — lem-trf-associated-primes-fibre-bound

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-associated-primes-fibre-bound.json`: repaired split, statement preserved.
   - `dag/nodes/sec-trace-formula/lem-trf-fibre-module-localization.json`: new unsplit statement; no exact Mathlib match.
   - `dag/nodes/sec-trace-formula/lem-trf-fibre-associated-primes-module-ring.json`: new unsplit statement; no exact Mathlib match.
   - `citations.json`: one verbatim statement quote for every node used by every item step.
2. Attachments: none. Searches of the read-only `WeilConjectures/` source for the exact blueprint tag and id, associatedPrimes and annihilatorAssociatedPrimes, and the helper names found no matching project declaration. The associatedPrimes hits are unrelated regular/projective-dimension arguments.
3. WANTED: none.
4. Returned delivery: the previous Steps 2–3 used the flat-base-change and fibre-prime nodes for facts those statements do not supply. The repair introduces two statement-only helpers, and the item now cites exactly their module identification, annihilator witness and associated-prime correspondence clauses. It also repairs a further missing argument: the prime p_0 selected from the union is shown to equal q intersect R before localizing. The previous irrelevant localization at q and residue-field comparison are removed. The item statement and ancestry are unchanged; comparison with current repository found no upstream statement change to incorporate. The required initial dry run failed on missing exact search-log queries; the actual searches were rerun with the item argument, and the final records are copied from the returned log data. The earlier searches remain in searches.jsonl.
5. Nothing remains mathematically unfinished in the item's split. The two new helpers are intentionally unsplit, as required for one-level delivery.

## Not duplicates

lem-trf-fibre-module-localization vs lem-weil-pbc-fibre-ring-localization-quotient: the existing node identifies rings only; the new node identifies arbitrary module fibres and preserves the exact annihilator of a witness when the contracted prime is p.

lem-trf-fibre-module-localization vs lem-weil-pbc-associated-prime-localize-at-prime: the existing node inverts the whole complement of q and gives an annihilator in B_q; the helper inverts only the image of A minus p, identifies the result with a residue-field fibre and gives the B-annihilator there.

lem-trf-fibre-module-localization vs lem-weil-pbc-localization-tensor-over-base: the existing node localizes a tensor product; it does not form the prime quotient/residue-field fibre or state exact annihilator preservation over B.

lem-trf-fibre-module-localization vs lem-weil-pbc-tensor-over-quotient-ring: the existing node gives a quotient-tensor equivalence; it does not invert base denominators or identify the resulting fibre and its annihilator witness.

lem-trf-fibre-associated-primes-module-ring vs lem-weil-pbc-fibre-ring-primes-residue-fields: the existing node gives prime and residue-field bijections; the helper gives the corresponding equality of associated-prime sets for an arbitrary module over the fibre ring, with elementwise annihilator extension and contraction.

lem-trf-fibre-associated-primes-module-ring vs lem-weil-pbc-fibre-ring-primes-bijection: a prime correspondence alone states no associated-prime or module-annihilator result.

lem-trf-fibre-module-localization vs lem-trf-fibre-component-relative-associated: the latter concerns generic points of scheme fibre components, whereas the helper concerns fraction formulas and module annihilator witnesses.

lem-trf-fibre-associated-primes-module-ring vs lem-trf-fibre-component-relative-associated: generic points of fibre structure sheaves are different from transport of associated primes for every module over a fibre ring.

lem-trf-fibre-associated-primes-module-ring vs lem-trf-associated-primes-fibre-bound: The item proves containment for Q tensor_R P with P flat; the helper is the scalar restriction theorem for every module over C, contains no Q or flatness hypothesis, and states elementwise ideal extension/contraction. It is the generic 05BY/05BZ input to the interpretation of the item, not a renamed tensor-flat containment clause.

lem-trf-fibre-associated-primes-module-ring vs lem-weil-pbc-associated-prime-localization-depth-zero: The existing node localizes the ring R at an associated prime and gives an element annihilator there; the helper compares scalar rings B and C on the same arbitrary C-module.

lem-trf-fibre-module-localization vs lem-weil-pbc-affine-conormal-sections-existence: The existing node identifies conormal sections for a closed immersion, not arbitrary residue-field module fibres or localized annihilator witnesses.

lem-trf-fibre-module-localization vs lem-weil-pbc-completion-tensor-quotient-separated: The existing node asserts injectivity into all completion quotients for a finite algebra, not a module fibre/localization equivalence.

lem-trf-fibre-module-localization vs lem-weil-pbc-etale-quotient-base-change: The existing node gives etaleness under quotient base change and a ring quotient formula, with no module fibre or annihilator witness.

lem-trf-fibre-module-localization vs lem-weil-pbc-module-pullback-ideal-quotient: The existing node concerns sheaf pullbacks commuting with ideal quotients, with no residue-field localization or exact associated-prime witness.

lem-trf-fibre-module-localization vs lem-weil-pbc-tensor-quotient-base-change: The existing node identifies quotient algebras B/IB and B tensor A/I, not arbitrary modules tensored with a residue field or their annihilators.

lem-trf-fibre-module-localization vs lem-weil-pbc-tensor-right-exact: Right exactness of tensor is an ingredient for a quotient; it states neither the residue-field localization nor exact witness transport.

lem-trf-fibre-module-localization vs lem-pc-intrinsic-flat-module-stalk-tensor-presentation: The existing node identifies a quasi-coherent sheaf stalk on an affine scheme with tensor by its local ring, not an arbitrary module residue-field fibre with its annihilator witness.

lem-trf-fibre-module-localization vs new-lem-pc-complex-localization-unit-kernel: The existing node gives a denominator killing a cohomology class annihilated by a localized adjunction unit, not a prime quotient/fibre identification or associated-prime witness.

lem-trf-fibre-module-localization vs lem-weil-pbc-algebra-localization-away-base-change: The existing node concerns algebras localized at powers of one element, with no module prime quotient or residue field and no annihilator claim.

lem-trf-fibre-module-localization vs lem-weil-pbc-essentially-smooth-base-change: The existing node preserves essential smoothness under tensor base change, not module fibres or annihilator witnesses.

lem-trf-fibre-module-localization vs lem-weil-pbc-fibre-dimension-neighborhood-localized-bound: The existing node bounds Krull dimensions of localized fibres, not module isomorphisms or exact associated-prime witnesses.

## Review by Q90

I read the item and its parent input in flat.tex (Tag 05DM's final paragraph), Algebra Tags 0312 (lemma-bourbaki, including its full equality proof), 05C1 (lemma-post-bourbaki), 05C2 (lemma-bourbaki-fibres), and 05E0 (remark-bourbaki). For the new module helper I read 00DK (lemma-tensor-localization), the quotient-tensor exactness statement 00DF, and 05BZ (lemma-localize-ass), including its annihilator computation. For the new associated-prime helper I read 05BY (lemma-ass-quotient-ring) and 05BZ(1), the two facts explicitly invoked by 05E0. The generalization from the fibre of N to every C-module L uses exactly the same annihilator calculation; it needs no flatness or Noetherian assumption. The new helpers do not restate the tensor-flat containment item: they contain no Q or flatness hypothesis and provide strictly more basic module/scalar-change operations.

Step 1 uses only the equality statement of `lem-weil-pbc-associated-primes-flat-base-change`, which I opened. Its R-Noetherian hypothesis is given, and its R-flat S-module is P. It supplies p_0 and an exact annihilator witness in P/p_0P. The elementary observation that the witness is nonzero uses that q is proper. Step 2 opens and uses `lem-weil-pbc-flat-tensor-exact` for preservation of an injection and `lem-weil-pbc-tensor-over-quotient-ring` for the explicit quotient-tensor map. Primality of p_0 makes multiplication by a outside p_0 injective on R/p_0. Under the cited map the tensored endomorphism is literally multiplication by a, so no unquoted flatness-of-a-quotient theorem is used. This shows p_0=q intersect R, a hypothesis missing in the earlier localization step.

Step 3 uses only `lem-trf-fibre-module-localization`: its statement gives the exact module isomorphism and the annihilator conclusion for z/1, under the contraction hypothesis just proved. I checked the source calculation: b kills z/1 if and only if some image of u outside p kills bz; then u b lies in q, u does not, and primality yields b in q. The reverse implication is immediate. The new helper is statement-only; its intended future proof constructs the maps n tensor (a/s) -> an/s and n/s -> n tensor (1/s), checks balancing and the zero-fraction relation, and applies this annihilator calculation. This is the specific non-elementary module identification that was previously uncited.

Step 4 uses only `lem-trf-fibre-associated-primes-module-ring`, whose statement gives contraction as a bijection of the two associated-prime sets, not just spectra. Its intended future proof: every scalar of C is b/s after killing pB; for an element z of L, Ann_B(z) is the contraction of Ann_C(z). Since denominators are units on L, (b/s)z=0 iff bz=0, giving Ann_C(z)=Ann_B(z)C. Quotient and localization ideal correspondence show that one is prime iff the other is prime, and properness implies all base scalars outside p avoid the annihilator whereas p kills z. These are Tags 05BY and 05BZ(1). The action on the actual fibre in Step 4 is the displayed balanced formula, so the helper applies in the exact coefficient ring C in the statement. The existing prime and residue-field node is no longer misused to supply this equality.

I searched the whole DAG by the helper concepts and tags, opened the existing ring-fibre, localization and quotient/tensor nodes and the scheme fibre-component node, and searched the whole blueprint with `blueprint_refs.py search` for fibre module, tensor localization, 05E0 and 05BZ. None states either helper. The Mathlib candidates were read in AssociatedPrime/Localization.lean, Localization/BaseChange.lean and LocalRing/ResidueField/Fiber.lean. They cover general localization association, tensor-localization and fibre spectra; they do not supply the complete arbitrary-ring module-fibre/witness statement or the arbitrary C-module restriction-of-scalars equivalence. Mathlib's associatedPrimes uses radical annihilators here; that is another reason its generic localization result is not a direct arbitrary-ring match. A second phrasing is recorded for each helper. All recorded new-node search query texts occur in searches.jsonl with actual results; invalid earlier Loogle queries are not used as the sole evidence of absence.

Small cases checked: N=0 gives zero fibres and no exact associated primes; A a field and p=0 gives the ordinary module and its original annihilators; A=Z, p=(2), B=Z[x] gives the localization of N/2N at odd scalars; A=Z -> B=Q with p=(2) gives the zero fibre and has no q over p, as required. For arbitrary C-modules the denominator-unit argument still works for modules that are not finite and rings that are not Noetherian. In the item, Q=0 or P=0 makes the premise empty; a=0 or a in p is never passed to the injection argument. No assertion that the fibre is finite over S is made (localizing a finite S-module need not remain finite over S). Both new nodes carry empty proofs and no hidden proof sketch inside their statements. All item proof steps are below 2000 characters.

The generic off-unit Bourbaki equality is explicitly declared in `split_report.tool_uses`; the flat-tensor and quotient-tensor inputs are existing Mathlib leaves. This follows the same Tag 05DM/05C2 route as the original item. Both C1/C4 issues in the return and the additional contraction gap are repaired. No Lean code was written and no compiler was run.
