Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-krull-akizuki-noetherian.json`: split statement; no Mathlib match.
- `citations.json`: verbatim quote for the existing finite-length dependency.

Attachments:

- `lem-weil-pbc-dim-one-submodule-quotient-finite-length` is the existing reviewed node for Stacks 00PE, and supplies finite length of `M/xM` for an arbitrary submodule of a finite-dimensional fraction-field space.

WANTED: none.

What was wrong in the node or brief:

- The imported node was unsplit and had no proof. Its statement agrees with Algebra Lemma 10.119.12 (Tag 00PG).
- No new node was needed: the DAG already contains the stronger 00PE finite-length statement. The proof's first step writes out the nonzero ideal intersection argument rather than creating a duplicate of the auxiliary 10.30.8 fact.

What I could not finish:

- Nothing.

## Review by C1

I read the Stacks Project page for Algebra Lemma 10.119.12 (Tag 00PG), including its proof and the cited finite-length input. The item hypotheses match: `R` is a Noetherian one-dimensional domain, `L/K` is finite, and `D` is an intermediate ring. The first step handles a nonzero ideal by choosing a nonzero element and clearing denominators in a minimal polynomial, producing a nonzero element of `I cap R`; the zero ideal is immediate. This is the elementary content of the source's 10.30.8 citation.

Step 2 uses exactly the statement of the existing reviewed 00PE node: for an `R`-submodule `M` of `K^oplus r` and nonzero `x`, `M/xM` has finite length. A finite `K`-basis of `L` identifies `D` with such an `R`-submodule, so `D/xD` has finite length. Its submodule `I/xD` is finite length; lifting finitely many generators and adjoining `x` gives finite generation of `I` as a `D`-ideal. The cited node says the quoted finite-length clause verbatim, as recorded in `citations.json`.

I checked small cases `D = R`, `L = K`, and a principal ideal `I = (a)`: the argument reduces to the identity extension and the obvious finite generation. Mathlib searches for the item were rerun with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder found only stronger integral-closure results, Loogle and grep found no match, and LeanSearch was unavailable. No Lean declaration with the item tag or statement exists in the source checkout.

## Second reading by C1

- Step 1 checked against Algebra Lemma 10.119.12 (Tag 00PG) and its minimal-polynomial argument; verdict: correct and elementary, including the zero ideal case.
- Step 2 checked against the global finite-length lemma 10.30.9 (Tag 00PF); verdict: repaired, since the previously cited 00PE node assumes `R` is local.
- `lem-sc-finite-length-global-submodule` checked against Algebra Lemma 10.30.9 (Tag 00PF), including its nonlocal hypotheses and finite-length conclusion; verdict: correct statement-only support node, distinct from local 00PE.
- Item statement checked against Algebra Lemma 10.119.12 (Tag 00PG), including arbitrary intermediate `D`; verdict: matches.
- Small cases `D = R`, `L = K`, and principal ideals checked; verdict: consistent.
- Changed Step 2 and `proof_deps` to cite the new global 00PF node, and replaced the citation quote with that node's verbatim statement.
- Added the missing global finite-length support node because the existing 00PE node has an extra locality hypothesis.
