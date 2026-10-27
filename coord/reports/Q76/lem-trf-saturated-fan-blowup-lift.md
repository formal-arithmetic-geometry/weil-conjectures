# Stage-1 report: lem-trf-saturated-fan-blowup-lift

## Files written

- dag/nodes/sec-trace-formula/lem-trf-saturated-fan-blowup-lift.json: item, statement, now split into eight proof steps. Mathlib verdict: no match.
- citations.json: verbatim statement excerpts for every proof-step dependency.
- searches.jsonl: actual search-command records. The sandbox also contains the source PDF's text extraction and a local JSON-writing script; these are not delivery files.

No new nodes; no Mathlib leaves. The statement and statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by saturated fan, fan blowup, monoidal space and KatoFan; no matching project declaration exists. The three reused statement nodes are not attachment claims.

## WANTED

None. Read the supplied ILO PDF, Exposé VIII, printed pp.98--102 and 108--109, especially 3.1.8(ii), 3.1.17--3.1.25 and 3.3.13(i),(iii). This is a monoidal-geometric argument, for which no Stacks tag states the result; no SGA source is used.

## Audit findings

The imported item has no proof and correctly asks for arbitrary sharp saturated integral monoidal spaces, not just fine fans or characteristic spaces of log schemes. ILO 3.1.21 explicitly states universality among saturated monoschemes, and 3.1.24 discusses fans; extending the chart construction to the item's arbitrary source requires the sectionwise argument and affine-fan Hom theorem written here. Accordingly proof_origin is agent, with the actual ILO source retained. No statement dispute was found.

The current blueprint's lem-trf-local-term-locality proof follows contracting correspondences, whereas this created item's metadata records a historical nearby-duality/monoidal-resolution ancestry. I read the current blueprint and retained the item's explicit historical ancestry; this split does not change a chapter or unit route. The immediate parent lem-trf-log-fan-chart-blowup now uses this lemma at steps 3--5 (its earlier creation metadata says step 8). This split supplies exactly that parent's needed uniqueness and gluing fact.

## Not duplicates

No new nodes are proposed. Whole-DAG searches by saturated monoid, monoidal space, fan blowup, principal/invertible monoid ideal and global-section Hom found the existing affine-fan Hom, finite-saturation and fs-face-sharpening nodes used here. Blueprint searches for fan blowup, affine fan and saturated fan found no same statement; the broader monoid results describe different categorical and logarithmic constructions. The existing fan-chart-local-monoid-lift concerns lifting characteristic charts to log structures, and sharpening-blowup-chart-comparison concerns passage from monoschemes to fans; neither proves this item's arbitrary-source universal lift. No duplicate was created.

## Review by Q76

I checked delivery-errors B--E against the item and the open sources. There are no unsplit new-node statements to audit, no invented Mathlib matches, no hidden proof in a new statement and no relabeling of the item's clauses. The proof actually constructs the section maps, establishes chart membership for any competitor and glues them. Every non-elementary input is one of three existing statements, whose full statements I opened: lem-trf-affine-fan-hom-universal (ILO VIII 3.1.8(ii)), lem-trf-fine-monoid-finite-saturation (VIII 3.1.17 and the finiteness portion of 3.2.9), and lem-trf-fs-face-sharpening (VIII 3.1.1--3.1.5, with the fs algebra recorded in its statement). All three are in sk-i-curve-zero, so no off-unit tool declaration is needed. None depends on this item. I also read both definition dependencies; the group completion, sharpness, saturation, locality, spectrum, ideal pullback and blowup overlaps used here are explicitly defined there.

Step 1 uses the integral/saturated group-completion definition and the sheaf definition, not an unstated theorem about global sections. I wrote the germ representatives and the cancellation gluing to check saturation of sections even when the space is not quasi-compact. Step 2 uses only the monoid ideal definition: membership of the chosen principal generator in the ideal gives one element of the finite generating family, and sharp cancellation makes it the same generator. Only finitely many relations must be spread to one neighborhood.

Step 3 applies the universal group-completion relations and the elementary saturation argument of step 1. There is no need to choose roots of images or assume torsion-free group completions. In particular uniqueness comes from C_a containing P inside P^gp, so C_a^gp=P^gp, not from cancelling a positive integer. Step 4 uses finite-saturation for the fine integral Q_a, fs-face-sharpening with the units face of the fs C_a, and affine-fan Hom only after its fine sharp hypothesis has been established. That Hom statement really allows an arbitrary topological space with sharp stalks. Its naturality identifies the composite with d; no theorem merely defining a fan is cited for this bijection. Localization and unit quotients give the canonical chart identification directly.

Step 5 computes on every e-chart that a is a generator exactly when a-e is a unit; it identifies this with the actual D(a-e) overlap specified by the definition. This avoids inferring factorization from an image containment without checking the sheaf maps. Step 6 first uses locality to force a competitor into that open chart, then uses the unique fraction extension and the actual Hom bijection to identify the full morphism, not just its continuous map. Step 7 glues the continuous maps and sheaf homomorphisms explicitly and checks locality on stalks. Step 8 maps the generator relations under precomposition; this proves the principal-ideal hypothesis for the composite before invoking uniqueness. Restriction and cover gluing are then consequences of the uniqueness already proved.

I tested empty T; the zero monoid; singleton E (where a nonsaturated base still needs saturation); the whole ideal with 0 among its generators; and P=N^2 with E={(1,0),(0,1)}, where both principal generators on an overlap force the difference to map to zero in the sharp source. To test the absence of an unjustified cancellation of n, I considered the sharp fine monoid generated by (1,0),(1,1) in Z x Z/2: the fraction construction is in its group completion and remains valid when maps kill its torsion. I also checked that sectionwise saturation uses local representatives without demanding one common neighborhood for infinitely many elements of C_a. No fine, Noetherian or quasi-compact hypothesis on the source has been introduced. Every step is below 2000 characters; the only non-elementary geometric constructions are the cited three nodes. The two charts need not be sharp before taking their unit quotient, and the proof explicitly takes that quotient before using the sharp affine-fan theorem.

Mathlib searches were run with msearch.py, and the returned signatures were read. They give Proj and scheme quotient lifts, ring localizations and fractional ideals, not saturated monoid-ideal fan blowups. The grep hit Submonoid.saturation is the multiplicative-divisor saturation (its source explicitly distinguishes PowSaturated/NSMulSaturated), so it is not this saturation theorem. The log retains every actual query and digest. No unrun search is recorded.

## Unfinished work

None within this stage-1 item. No Lean was written and no compiler, Lake or build was run. Required delivery preflight is the remaining verification step.
