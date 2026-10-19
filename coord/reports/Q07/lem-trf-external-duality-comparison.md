## Files written

- `dag/nodes/sec-trace-formula/lem-trf-external-duality-comparison.json` — statement, split proof, no new nodes; Mathlib searches found no match.
- `citations.json` — verbatim citations for every proof-step dependency.

## Attachments

None.

## WANTED

None.

## What was checked

The imported item is the left inner square of Varshavsky’s external-duality diagram, with the two projection legs interchanged. Its statement has the full finite-coefficient, admissibility, comparison-axiom, and pre-cancellation hypotheses; it does not assume that the product comparison `Pi` is invertible and it makes no trace-class claim. I found no finished project declaration carrying the blueprint tag, and no duplicate node or alternate blueprint node stating this comparison.

The proof follows §4.4.3 of the cited Varshavsky paper. Step 1 reads the definitions of `kappa` and `Pi` in `def-sf-kv-maps` and `def-trf-cohomological-comparison`, and checks that tensor–Hom uncurrying reduces the desired equality to the two uncurried routes of diagram (4.14). Step 2 applies exactly axiom (IV) of `def-trf-cohomological-comparison` to the first projection and the inputs `K` and `D_X K`; the quoted formula is the axiom’s displayed tensor equation.

For Step 3 I read the full statement of `lem-trf-cohomological-evaluation-calculus`. Its clauses (a), (c), and (d) say respectively that exceptional tensor comparison, tensor-unit/diagonal normalization, and the dualizing projection exchange commute with the comparison data. I also read `lem-trf-projection-kunneth-tensor`, whose displayed formula identifies the exceptional Kunneth map with the same signed exceptional-tensor composite through `chi`. These are precisely the three factor maps in Varshavsky’s diagram (4.15), so each small square commutes and hence the right square of (4.14) commutes. Step 4 uses injectivity of the tensor–Hom uncurrying bijection and explicitly records that no cancellation of `Pi` occurs.

I checked the hypotheses at each use: the first projection is a listed arrow of the fixed diagram, all tensor/Hom objects are in the stated finite-Tor constructible domains, and the evaluation, unit, dualizing, and projection maps are the ones fixed by the cited nodes. The four Mathlib searches returned only generic monoidal or adjunction declarations and therefore do not state this geometric six-functor identity. No SGA 4 or SGA 4½ source was used.

## Review by Q07

I read the item, `def-trf-cohomological-comparison`, `def-sf-kv-maps`, `lem-trf-cohomological-evaluation-calculus`, and `lem-trf-projection-kunneth-tensor` in full, together with Varshavsky §4.4.3 and diagrams (4.14)–(4.15). The statement’s hypotheses are all used: (IV) supplies the first square; clauses (a), (c), and (d) of the evaluation calculus supply the tensor, unit, and dualizing exchanges in the second square; and the projection-Kunneth node supplies the signed Kunneth/tensor identification. The `Pi` map is only composed and is never cancelled. Every citation quote in `citations.json` is copied verbatim from the cited node’s statement. I checked identity and zero-object cases conceptually: both routes reduce to the corresponding unit/evaluation maps, and the conclusion remains meaningful when `Pi` is noninvertible. No new node is needed, no duplicate exists, and the item’s blueprint ancestry is retained.

## What was wrong or corrected

No mathematical or statement error was found. The isolated copy records fresh Mathlib searches; all returned hits were generic and were marked no match.

## What could not be finished

Nothing.
