1. Files written:

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-generic-finite-algebra-splitting.json` (item, split).
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-generic-separable-algebra-splitting.json` (statement, unsplit, no Mathlib match).
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-spread-finite-separable-extension.json` (statement, unsplit, no Mathlib match).
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-spread-purely-inseparable-factors.json` (statement, unsplit, no Mathlib match).

2. Attachments: none.

3. WANTED: none; the parent blueprint document is present as the recorded source reference, although the imported Markdown copy is not in this checkout.

4. The imported item had no proof. I checked the parent node's finite-algebra paragraph and replaced the single opaque argument by three genuine auxiliary statements and an idempotent-spreading step. The existing `lem-fin-finite-splitting` node is not a duplicate: it decomposes a finite morphism over an etale neighbourhood of one geometric point, while this item gives a generic localization and requires every factor to be radicial over the base. I repaired the purely-inseparable child to avoid the false integral-closure finiteness assertion: it now takes a finite domain factor E itself and states only the localized surjective/radicial universal-homeomorphism conclusion.

## Review by M1

I read the item source reference and the parent node's proof, including the finite-algebra calculation (generic fibre, separable extension, purely inseparable factors, and spreading idempotents). I checked each new statement against the corresponding clause of that calculation and against the existing DAG: the first child is the generic reduced-algebra decomposition, the second supplies the finite etale model after a principal localization, and the third supplies finite domain factors whose maps are finite, surjective, radicial, and hence universal homeomorphisms. The item proof's first three steps cite exactly those statements; the fourth uses only denominator clearing and the finite idempotent relations, so it is marked elementary. I verified the hypotheses (Noetherian integral domain, fraction field, finite-dimensional generic algebra, finite separable and purely inseparable field extensions) in each statement. I ran LeanFinder, Loogle, grep, and LeanSearch searches for the item and every new child; LeanSearch was unavailable and is recorded as such. All citation quotes are verbatim statements from the cited child nodes.

5. Nothing remains unfinished in the split; `deliver.py M1 lem-weil-pbc-generic-finite-algebra-splitting --no-push` completed with `OK (not pushed)` and preflight passed.

## Second reading by M1

- Item statement: checked against the parent blueprint's finite-algebra calculation and the downstream use in `lem-weil-pbc-finite-pushforward-generic-constructible`; the generic fibre, finite etale cover, finite radicial factors, and reduction/product conclusion have the stated hypotheses.
- Step 1: checked against `lem-weil-pbc-generic-separable-algebra-splitting`; it uses exactly the finite separable extension and purely inseparable field-factor decomposition.
- Step 2: checked against `lem-weil-pbc-spread-finite-separable-extension`; it uses the stated principal localization, domain `A'`, fraction field `K'`, and finite etale surjectivity.
- Step 3: checked against the repaired `lem-weil-pbc-spread-purely-inseparable-factors`; its finite domain algebra hypotheses and surjective, radicial, and universal-homeomorphism conclusions match the cited statement, with the finitely many localizations combined.
- Step 4: checked against both generic decomposition and factor-spreading statements; the denominator clearing, idempotent relations, torsion-free reduced finite module, generic embeddings, and product splitting are written explicitly, with no integral-closure identification.
- `lem-weil-pbc-generic-separable-algebra-splitting`: statement-only B1, self-contained field/algebra hypotheses and definition citations, blueprint/source/search metadata present; tested on a field and on the zero algebra.
- `lem-weil-pbc-spread-finite-separable-extension`: statement-only B1, self-contained domain and fraction-field hypotheses, definition citations and search metadata present; tested on `A=K` and the trivial extension.
- `lem-weil-pbc-spread-purely-inseparable-factors`: statement-only B1, explicitly says `A'` is a domain, and its integral-closure and morphism notions are cited; tested on `L=K'` and a finite purely inseparable field extension.
- `lem-weil-pbc-generic-finite-algebra-splitting`: source, blueprint ancestry, and search records were checked; no duplicate existing node states this localization-plus-universal-homeomorphism conclusion.

Changes made: made the domain hypotheses on both finite etale algebras explicit; expanded step 4 to state the denominator, idempotent, finite-subalgebra, and generic-fibre arguments; changed step 4 to non-elementary and added both verbatim citation quotes.

The repaired split was dry-run with `deliver.py --no-push`; preflight, citation, search, and duplicate checks passed after replacing the false integral-closure claim and its dependent citation.

## Not duplicates

lem-weil-pbc-spread-purely-inseparable-factors vs lem-weil-pbc-integral-injective-dimension-equal: the existing node concerns dimension equality for an integral injective map, while this child spreads a finite purely inseparable fraction-field algebra after localization and proves surjectivity, radiciality, and universal-homeomorphism properties.
lem-weil-pbc-spread-purely-inseparable-factors vs lem-weil-pbc-integral-injective-lying-over: the existing node is a lying-over statement for integral injective maps, while this child constructs a localized finite algebra E and establishes the full morphism properties of Spec(E) over Spec(A').
lem-weil-pbc-spread-purely-inseparable-factors vs lem-weil-pbc-finite-over-complete-local-product: the existing node concerns products after completion of a finite algebra, while this child concerns spreading a purely inseparable field factor over a principal localization and does not use completion.
lem-weil-pbc-spread-purely-inseparable-factors vs lem-weil-pbc-radicial-prime-unique-degree-p: the existing node gives uniqueness and degree behavior of primes under a radicial map, while this child proves that a localized finite purely inseparable algebra map is radicial and surjective.
lem-weil-pbc-spread-purely-inseparable-factors vs lem-pc-spec-pure-insep-integral-radicial-surjective: the existing node proves an abstract implication for an integral radicial surjective field-extension map, while this child supplies the localization and finite-algebra spreading that produces those hypotheses for E over A'.
lem-weil-pbc-spread-purely-inseparable-factors vs lem-pc-homeo-pure-insep: the existing node states the universal-homeomorphism consequence for a field-level purely inseparable extension, while this child is a relative finite-algebra localization result over a Noetherian base.

## Second reading by M1

- Item and source proof: checked the finite-algebra calculation and its four proof clauses against the parent blueprint and downstream use; the localization, generic product, and universal-homeomorphism conclusions have matching hypotheses.
- Step 1: checked against the generic separable-splitting statement; the finite-dimensional algebra and purely inseparable field-factor data are exactly supplied.
- Step 2: checked against the finite-separable-spreading statement; the principal localization, finite etale domain, fraction field, and surjectivity conclusions match.
- Step 3: checked against the purely-inseparable-spreading statement; its finite domain algebra and localized base-change hypotheses provide the cited surjective and radicial morphism.
- Step 4: checked the idempotent denominator clearing, torsion-free localization, and product-factor argument against the two cited statements; no uncited integral-closure assertion remains.
- Generic separable child: statement-only and self-contained with definition citations; field and zero-algebra edge cases are consistent.
- Finite-separable-spreading child: statement-only and self-contained; the trivial extension and localization-at-one cases are consistent.
- Purely-inseparable-spreading child: statement-only and self-contained; the identity extension case is consistent, and the morphism notation is explicit.

Changes made: removed the child’s unsupported “equivalently” clause involving an undefined characteristic $p$, made the localization/base-change objects explicit, normalized the morphism notation, and updated both verbatim citation quotes. Dry run passed after the repair.
