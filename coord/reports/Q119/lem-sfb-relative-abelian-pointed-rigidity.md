# Q119 — lem-sfb-relative-abelian-pointed-rigidity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-abelian-pointed-rigidity.json: statement, split into six steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-space-finite-image-neighbourhood.json: new statement-only prerequisite, unsplit; no Mathlib match. This is the finite-image theorem for general proper algebraic-space families, not abelian-group rigidity.
- citations.json: exact statement quotations for every use in all six steps.
- searches.jsonl: actual msearch.py queries and result digests; existing item searches retained in its JSON, new queries appended.

## Attachments

No exact project declaration was found for the item or the new general algebraic-space lemma. Reading WeilConjectures/AlgebraicGeometry/AbelianVariety/Rigidity.lean found field rigidity only; that is already attached to lem-sc-rigidity and is reused here. Scheme global-functions and existing category group-homomorphism results do not state the relative algebraic-space assertion.

## WANTED

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Proposition 6.1, for the item's originally requested relative reference. Its PDF is absent. This delivery does not depend on the unavailable proof: it supplies an agent assembly from the available field reference and Stacks algebraic-space inputs.

## What was wrong and what changed

The live item was statement-only, created today by Q153. There was no prior sandbox split, report or search log after the interrupted turn; only dispatcher marker files were present, and no delivery process was active. The item's statement has not changed. Its source explicitly warned against concluding equality of morphisms from geometric-fibre equality over a nonreduced base. Steps 3 and 4 now supply that missing relative argument using genuine closed finite image factorizations and the full rings of functions.

The inherited blueprint.from.node is null. blueprint_refs.py ancestor reports precisely None, and the via chain reaches the det-thm-sf-ctf-stability-direct-images proof-(3) support material. I retained that result and filled the new node's place and via accordingly. I read the latest main-20261023-1620 unit and direct-image proof through literature/blueprint/latest, in addition to the DAG chapter/unit records; their current direct-image argument uses compactification. This local prerequisite does not alter that route or its unit statements.

## Not duplicates

lem-sfb-proper-space-finite-image-neighbourhood vs def-sfb-finite-stack-scheme-tests: the latter defines finite representable stack maps and scheme testing, whereas the new lemma asserts existence of a finite closed factor of a proper algebraic-space map near a finite fibre image. They share Tag 03ZP only for the definition of finite; the new mathematical assertion is Tag 0AEJ.

The new Tag 0AEJ node has no existing same-tag node (searched the entire DAG and blueprint). lem-sc-finite-image-locus-open is only a constant-family statement over a field and concludes finiteness of fibre images, not a finite closed algebraic-space factorization over a relative base. Its statement was opened. The stronger algebraic-space closed-factorization conclusion is needed here. Mathlib's AlgebraicGeometry.exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage, Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:424–439, was read after the grep hit: it concerns schemes, so it is a candidate analogue, not a one-line specialization for algebraic spaces. The new node records this limitation.

I did NOT create a universal-global-functions node with Tag 0E0S: lem-sfb-rigidified-space-picard already states the exact required universal assertion under the geometrically integral fibre and section hypotheses, both available here. I also reused lem-sfb-space-affine-target-global-functions (Tag 05Z1), lem-sfb-space-flat-proper-fp-locality and the field rigidity and characterization nodes. No new node repeats the item or either of its clauses.

## Review by Q119

I read Milne, Abelian Varieties I, Theorem 1.1 and Corollary 1.2, printed pp.8–9, including the actual additivity-defect formula and the proof of two-axis vanishing. For the new lemma I read spaces-more-morphisms.tex, lemma-flat-proper-family-cannot-collapse-fibre (Tag 0AEJ), both statement and proof: proper source over the base, separated locally finite type target, and finite geometric-fibre image are exactly its hypotheses (3)(a). I use no flatness assumption there. Shrinking its base open to an affine open gives an affine finite scheme Z, since finite means representable and finite scheme maps are affine. I checked the finite definition in spaces-morphisms.tex (definition-integral, Tag 03ZP). The new lemma is statement-only, with no hidden proof in its statement.

Step 1 cites lem-pc-smooth-flat only on scheme charts, where its statement applies; chartwise flatness is exactly the convention in the item. I opened lem-sc-abelian-variety-characterization: it says that a proper smooth connected group scheme is geometrically integral. Each geometric fibre is such a scheme by the item's explicit hypothesis. I opened lem-sfb-rigidified-space-picard: its first assertion states the canonical structure-sheaf isomorphism for every scheme parameter. Its locally Noetherian base, proper/flat/finite-presentation, geometrically integral fibres and identity section hypotheses have all been checked. The proof uses only that assertion; it does not use any unprovided claim from the Picard node's proof. I read spaces-perfect.tex Tag 0E0S and its reference to the proper-flat H0 lemma (0E6B) to check that this assertion includes arbitrary base changes and nilpotents.

Step 2 cites the full statement of lem-sc-rigidity. It is applied over the algebraically closed residue field, with proper geometrically connected/reduced first factor, connected second factor, separated finite-type target, and the identity rational point. These are schemes, not assumed scheme presentations of the relative spaces. The first axis gives the one-point fibre; the second identifies the resulting factor g as zero. Hence the conclusion is equality of scheme morphisms on each fibre.

Step 3 cites def-trf-algebraic-space for its etale atlas and sheaf fibre products, the full proper base-change assertion of lem-sfb-space-flat-proper-fp-locality, and the new finite-image lemma. I read each statement. The parameter is a scheme chart T of Q; both P_T and R_T are proper over T. Properness supplies separatedness and local finite type for the target. Every geometric-fibre image is the identity singleton by step 2. The new lemma supplies a real factorization through Z; no unsupported factorization through a closed subscheme from set containment is used.

Step 4 cites the bijection of lem-sfb-space-affine-target-global-functions. I read that full statement and its source Tag 05Z1 (spaces-properties.tex, lemma-morphism-to-affine-scheme). It allows arbitrary source algebraic spaces and affine scheme targets. The isomorphism on global functions comes from step 1 and is the canonical p-pullback, so the identity section induces its inverse. Writing b=as yields (bp)^sharp=p^sharp s^sharp a^sharp=a^sharp; injectivity gives a=bp. This calculation is valid for nonreduced rings and is why fieldwise equality suffices here without discarding nilpotents.

Step 5 cites the definition of an algebraic space as a sheaf: testing an equality after pulling the atlas back to any scheme test and using uniqueness of gluing is elementary. Step 6 is the explicit group-law calculation of Milne's Corollary 1.2, now using the two-axis assertion proved in steps 1–5. It does not assume the desired homomorphism property. Pullback of an established equality gives the base-change clause directly. The v assertion was proved for arbitrary P,Q,R, so no product-smoothness or product-integrality theorem is silently used.

I checked the B–E faults against all files: all new objects are introduced and their notions cited; no extra hypotheses on the item; no clause restated as a prerequisite; no cycle back to the item from the rigidified-Picard node (its dependency closure was read and checked); no proof or proof dependencies on the new node; every cited assertion is quoted verbatim in citations.json. The six proof steps have lengths 749, 665, 713, 562, 433, 576 characters, so none hides an argument beyond the long-step threshold. Searches were actually run with msearch.py, including a second semantic phrasing for both the item and the new node. I read the hits and the relevant Mathlib source rather than marking scheme results as space results.

Edge cases: the proof is vacuous over the empty base and works for the trivial dimension-zero abelian space. Characteristic p and nonreduced S=Spec(k[epsilon]/epsilon^2) require no change: step 4 uses the full structure ring. For the new lemma the empty image is permitted (choose an empty factor on a neighbourhood where the proper source is empty); a positive-dimensional constant family maps to a section and has finite image; the identity of a positive-dimensional proper fibre does not satisfy the finite-image hypothesis. No connectedness, reducedness or flatness was inadvertently imported into that lemma. No SGA reference is used.

## Unfinished work

The new finite-image lemma remains an unsplit stage-1 prerequisite. No Lean was written, and no compiler, Lake or build command was run. All checks and delivery are through the authorized server tools.
