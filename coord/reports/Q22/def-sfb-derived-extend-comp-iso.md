# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-six-functors-basics/def-sfb-derived-extend-comp-iso.json` — item, split statement; no Mathlib match.

2. Attachments: none. No sorry-free declaration for this item exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the upstream-master declaration is reference material and is not used as a finished-proof attachment.

3. WANTED: none.

4. The imported one-paragraph proof was expanded into four steps. Step 1 proves exactness of the three underived extension functors from right exactness and the two flatness statements. Step 2 computes the composite restriction action and composes the two adjunction Hom bijections. Step 3 applies the existing equal-right-adjoint uniqueness lemma, then identifies the coefficient map composite and the equal-map extension comparison. Step 4 constructs the termwise chain isomorphism and descends it through the unbounded derived localization using exactness. The statement and hypotheses are unchanged. No new node was needed: underived composition is proved explicitly in steps 2–3 from the cited change-of-scalars statement and the existing uniqueness leaf.

5. Nothing remains unfinished. No Lean code, compiler, Lake, or build tools were used.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q22

I read the current item source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.md`, its proof source, and the surrounding unit and chapter sections. The item statement keeps exactly a prime `ell`, an arbitrary scheme `X`, finite inclusions `E <= F` inside `Qlb`, the two unbounded derived module categories, and the natural-isomorphism conclusion.

For step 1 I opened both derived-extension definition nodes, clause (2) of `sk-def-sfb-change-of-scalars`, and the statements of `lem-sfb-subfield-flat` and `lem-sfb-qlbar-flat`. The first flatness statement applies to `E <= F`; the second applies separately to `F` and `E`, for every scheme. Right exactness plus finite-limit preservation gives exactness for precisely `A`, `B`, and `C`.

For step 2 I checked clauses (1) and (2) of `sk-def-sfb-change-of-scalars`. Its displayed restriction action gives the composite action `(psi circ phi)`; restriction leaves morphisms unchanged; and the two displayed Hom bijections compose to the claimed adjunction. This is an elementary calculation from that statement, so no auxiliary composition node is needed.

For step 3 I read the complete statement of `lem-weil-pbc-conjugate-iso-unit-equation`, which supplies the unit-compatible isomorphism of left adjoints with equal right adjoint. I also read `lem-sfb-subfield-coefficient-map-comp` for the literal coefficient-map equality and `def-sfb-extend-scalars-iso-of-eq` for the induced extension comparison. Every fact used by the step is stated by one of these citations.

For step 4 I read the exact-functor and localization clauses of `sk-def-sfb-derived-categories` and both derived-extension definitions. Naturality of the underived comparison gives the displayed chain-map equation; componentwise inverses exist; exactness identifies cohomology after applying each functor, so the chain isomorphism and inverse descend to the unbounded derived categories. All 13 entries in `citations.json` are verbatim substrings of the cited current node statements.

I searched the source checkout by item id, blueprint tag, and the upstream declaration name; no finished slopmaster2 declaration exists. I ran and recorded LeanFinder, Loogle, grep, and LeanSearch searches in `searches.jsonl`; they found only generic adjunction tools and the ordinary-module analogue `ModuleCat.extendScalarsComp`, not this internal derived-module statement. I checked edge cases `E = F`, `E = Q_l`, zero complexes, complexes in degrees 0 or 1, `X` empty, and `X = Spec(k)`; no hypothesis or clause changes. The discarded auxiliary node from the earlier attempt was removed because its assertion is established directly by steps 2–3.

The prior dry run `second-dry-run.log` records `OK (not pushed) ... preflight passed`. A fresh retry was attempted; concurrent deliveries again held the shared Git config lock and produced the same checkout error before preflight. No lock or shared repository file was modified.

## Second reading by Q22

- Step 1: checked the finite-extension hypotheses against the item source and the exact statements of `sk-def-sfb-change-of-scalars` (clause 2), `lem-sfb-subfield-flat`, and `lem-sfb-qlbar-flat`; the three extension functors are right exact and left exact under the stated arbitrary-scheme hypotheses, so the exactness conclusion is supported.
- Step 2: checked the restriction action and both adjunction clauses against `sk-def-sfb-change-of-scalars`; the displayed composite action, unchanged underlying morphisms, and pasted Hom bijections establish the composite adjunction, and the elementary mark is appropriate.
- Step 3: checked equal-right-adjoint uniqueness against `lem-weil-pbc-conjugate-iso-unit-equation`, coefficient-map equality against `lem-sfb-subfield-coefficient-map-comp`, and the induced comparison against `def-sfb-extend-scalars-iso-of-eq`; each cited statement supplies the claimed fact under the hypotheses in force.
- Step 4: checked the exact-functor and localization clauses of `sk-def-sfb-derived-categories` together with both derived-extension definitions; naturality gives the chain map, exactness preserves cohomology and quasi-isomorphisms, and localization yields the stated unbounded derived natural isomorphism.
- No new nodes are present; therefore B1–B7, duplicate-node checks, and Mathlib-leaf checks have no applicable new-node cases. The item statement was compared clause by clause with its blueprint source, including the prime, arbitrary scheme, finite subextensions, coefficient categories, and unbounded derived source and target.

I changed no node or citation: the existing split already has verbatim citation quotes, recorded searches, and the required four-step expansion. Changes in this second reading are this audit record and correction of the earlier claim that the master declaration itself contains `sorry`: its displayed body is a composite of comparison isomorphisms, and the read-only master is reference material rather than a finished-proof attachment; edge cases (equal fields, zero complexes, degrees 0 and 1, empty scheme, and `X = Spec(k)`) leave the statement and proof route unchanged.
