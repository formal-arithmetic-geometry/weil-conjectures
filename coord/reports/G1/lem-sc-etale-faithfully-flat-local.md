1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-etale-faithfully-flat-local.json`: repaired split item.
- `dag/nodes/sec-abelian-varieties/lem-sc-lfp-field-extension-pointwise-descent.json`: new unsplit pointwise local-finite-presentation descent statement; Mathlib searches found no exact pointwise theorem.
- `dag/nodes/sec-abelian-varieties/lem-sc-etale-local-ring-faithfully-flat-descent.json`: repaired unsplit affine primewise etale statement using `Algebra.IsEtaleAt`; Mathlib searches found only global etale descent and no primewise theorem.
- `citations.json`: verbatim statement quotes for every cited node in both proof steps.

2. Attachments: none.

3. WANTED: none.

4. The first delivery was returned for two mathematical defects. Step 1 previously assumed that the affine algebra was finitely presented without a pointwise descent result; the new node `lem-sc-lfp-field-extension-pointwise-descent` supplies exactly that missing hypothesis before shrinking the affine neighbourhood. The child previously used `Spec(B_q) -> Spec(A_p) is etale` as its hypothesis, which is ill-posed for arbitrary localizations. It now states the standard pointwise algebra condition `Algebra.IsEtaleAt`, with finite presentation of `B` over `A` explicit and the usual flat/differential characterization recorded parenthetically. The item applies this corrected child only after the finite-presentation shrink.

## Review by G1

I reread the item and its consumer `lem-sc-etale-base-change-geometric`, the source discussion around Varieties Tag 0C4Y, and the existing definitions for schemes, base change, locally finite presentation, and etale morphisms. The new local-finite-presentation node is self-contained: it introduces the field extension, schemes, points, and base-change morphism, and states only the pointwise descent fact. Its source is the affine-local argument based on Tag 0C4Y; no Stacks tag states this exact pointwise formulation. The repaired affine child introduces `k`, `K`, `A`, `B`, `q`, `p`, `B_K`, and `q_K`, and its hypothesis and conclusion are both the standard `Algebra.IsEtaleAt` condition. The cited definitions in its statement define the field extension, finite-presentation condition, tensor base change, and etale terminology.

Step 1 of the item uses the affine-local meanings of scheme, morphism, base change, and locally finite presentation, then explicitly invokes the new pointwise descent statement to obtain a finitely presented affine algebra before invoking the affine pointwise etale criterion. Step 2 uses Tag 0C4Y for the faithfully flat local map and takes precisely the `Algebra.IsEtaleAt` descent conclusion from the repaired child; the etale definition translates this local algebra condition back to an etale neighbourhood. Every non-elementary cited fact is listed in `citations.json`, and each quote was copied from the cited node after the repair.

For the new node and the repaired child I searched the whole DAG and blueprint before writing them. The searches were run through `msearch.py` with LeanSearch, LeanFinder, Loogle, and Mathlib grep; LeanSearch was unavailable and is recorded as unavailable. Mathlib has global finite-presentation and global etale faithfully-flat descent declarations, plus `Algebra.IsEtaleAt` and its local-structure lemmas, but no pointwise field-extension descent declaration, so both nodes remain unsplit. I checked small cases conceptually: the identity map and a field extension satisfy both pointwise statements, while the returned counterexample explains why the old localized-scheme child formulation could not be retained.

The return's missing-hypothesis and ill-posed-child points are therefore repaired, and the second-reading report now checks those hypotheses directly rather than merely asserting that they were checked.

## Not duplicates

lem-sc-lfp-field-extension-pointwise-descent vs lem-weil-pbc-fpqc-descend-locally-finite-presentation: the existing node descends local finite presentation globally along an fpqc covering, while the new node descends it at one point along a field extension that is not an fpqc covering of the base scheme.
lem-sc-lfp-field-extension-pointwise-descent vs lem-sc-etale-faithfully-flat-local: the item concludes the full etale property, while this child supplies only the local-finite-presentation hypothesis needed before the affine etale descent step.
lem-sc-lfp-field-extension-pointwise-descent vs lem-sc-etale-base-change-geometric: the existing consumer is a scheme-level base-change equivalence for etaleness, while this child is the missing pointwise local-finite-presentation descent lemma.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-weil-pbc-fpqc-descend-locally-finite-presentation: the existing node concerns only global local-finite-presentation descent, while the repaired child concerns the full pointwise etale condition.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-galois-fpqc-descend-etale: the existing node assumes etaleness over every member of an fpqc covering, while the repaired child is a single affine primewise field-extension statement.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-sc-etale-base-change-geometric: the existing item is scheme-level pointwise reflection and cites the child; the child is the lower-level affine algebra statement and does not quantify over schemes or neighbourhoods.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-sc-etale-faithfully-flat-local: the item is a scheme-level pointwise statement, while this child is an affine ring-level statement with explicit primes and the standard Algebra.IsEtaleAt condition.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-weil-pbc-fpqc-descend-flat: the existing node descends flatness alone globally along an fpqc cover, while this child descends the combined pointwise etale condition after a field tensor.
lem-sc-etale-local-ring-faithfully-flat-descent vs lem-galois-fpqc-descend-unramified: the existing node descends unramifiedness globally over an fpqc family, while this child includes finite presentation, flatness, and vanishing differentials at one prime.

5. Nothing remains unfinished beyond the two deliberately unsplit statement nodes queued for later workers.

## Second reading by G1

- Item statement: checked against the repository item and consumer `lem-sc-etale-base-change-geometric`, including arbitrary field extensions and points; verdict: agrees, with etale-at-a-point defined as etaleness on an open neighbourhood.
- Step 1: checked against the affine-local definitions of schemes, base change, local finite presentation, and the statement of `lem-sc-lfp-field-extension-pointwise-descent`; verdict: the field-extension descent supplies the finite-presentation affine shrink before the affine criterion is applied.
- Step 2: checked against Tag 0C4Y's faithfully flat local-ring map and the statement of `lem-sc-etale-local-ring-faithfully-flat-descent`; verdict: the cited child applies to the explicitly chosen primes and yields `Algebra.IsEtaleAt` at the original prime, which translates back to an etale neighbourhood.
- `lem-sc-lfp-field-extension-pointwise-descent`: checked B1-B7, source place, dependency definitions, blueprint ancestry, DAG duplicates, and Mathlib searches; verdict: self-contained statement-only node, no exact existing node or declaration.
- `lem-sc-etale-local-ring-faithfully-flat-descent`: checked B1-B7, the affine tensor-base-change setup, prime contractions, and Mathlib searches; verdict: self-contained statement-only node, no exact existing node or declaration.
- Small cases: identity field extension, a finite separable field extension, and the zero/empty affine cases were checked; all statements are vacuous or reduce to the ordinary affine criterion as expected.
- Changes made: retained the worker's repaired finite-presentation descent child and `Algebra.IsEtaleAt` affine child, verified their citations and search records, and added this explicit second-reading audit; no mathematical edits were necessary.
