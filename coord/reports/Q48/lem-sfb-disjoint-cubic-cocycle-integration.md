# Stage-1 delivery: lem-sfb-disjoint-cubic-cocycle-integration

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-disjoint-cubic-cocycle-integration.json`: unchanged statement; four-step cardinality-induction proof; status split. Not a Mathlib leaf.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-disjoint-symmetric-two-cocycle-integration.json`: one new statement-only binary integration lemma; status unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and whole-Mathlib grep.
   - `citations.json`: one verbatim statement quotation for each of the two step/node citation pairs.
2. Attachments: none. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and disjoint/cubic/cocycle notions. The Galois-cohomology hits, including `Field.exists_cocycle_monomial_coefficients` and `Field.GaloisUnitsTwoCocycle`, concern field coefficients and group actions, not potentials on disjoint subsets.
3. WANTED: Moret–Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129 (1985), I §2, especially I 2.4.5, for the upstream cubical-coherence context of lem-sfb-disjoint-cubic-cocycle-integration. Neither this combinatorial lemma nor its binary auxiliary is claimed to be a statement in that source. The algebraic proof below is agent-written; no SGA source is used.
4. Errors: none found in the item statement. Its inherited source is already explicit that this is an agent algebraic expansion, not an assertion in the blueprint. The inherited nearest blueprint ancestor is null; `blueprint_refs.py ancestor` confirms this. The existing via chain and all maintainer/import fields have been retained. No unit or chapter route was changed.
5. Unfinished work: only the deliberately unsplit new binary lemma, which joins the queue. No obstruction to the item proof remains.

## Proof of the auxiliary for the next worker

This paragraph is handoff material, not a proof embedded in the statement-only node. For a normalized symmetric q on a finite set, recursively define b(empty)=1 and b(S)=b(S minus {x})q(S minus {x},{x}) for any x in nonempty S. The value is independent of x: for distinct x,y in S, write R=S minus {x,y}, use the already independent value b(R), and compare

b(R)q(R,{y})q(R union {y},{x})

with

b(R)q(R,{x})q(R union {x},{y}).

The cocycle identities identify these respectively with b(R)q({y},{x})q(R,{x,y}) and b(R)q({x},{y})q(R,{x,y}), equal by symmetry. This is a strong induction on |S|, with the empty/singleton cases immediate. Next prove b(U union V)=b(U)b(V)q(U,V) for disjoint U,V by induction on |V|. The empty case is normalization. For V=V' union {x}, substitute the defining recurrence and the induction hypothesis; the cocycle on (U,V',{x}) reads q(U,V')q(U union V',{x})=q(V',{x})q(U,V), so the result follows after the recurrence for b(V). This uses only multiplication and inverses and works in every commutative group.

## Searches and small cases

The inherited Mathlib searches were retained and read. Fresh real searches are logged in `searches.jsonl`; their full outputs are `search-0.txt` through `search-5.txt`. The new node records exactly the five binary queries that ran, with their results. The item additionally records the fresh cubic phrasing. I read LowDegree.lean lines 605–710: IsMulCocycle₂ (625–626) is a definition of the identity and IsMulCoboundary₂ (677–678) defines, rather than proves, existence of a potential; the packaging/membership theorems already require cocycle or coboundary input. Powerset.lean lines 32–37 and 55–58 rearrange finite products and do not integrate cocycles. UniqueProds and NormalizationMonoid hits have unrelated hypotheses and conclusions.

Whole-DAG statement/concept searches and whole-blueprint searches (`cocycle`, `symmetric cocycle`, `disjoint subsets`, `coboundary`) found no binary integration statement. The blueprint coboundary hit is a Kummer/divisor cohomology statement. The exact new id does not exist in the live DAG. Existing cubic integration is our item and is not replaced by a renamed equivalent: the auxiliary has two arguments, a three-block identity and singleton normalization, while the item has three arguments, a four-block identity and two-element normalization.

`check_small_cases.py` is an independent finite linear-algebra check, with results in `small-case-results.txt`. For degrees two and three, sizes 0 through 5, and coefficients Z/2, Z/3, Z/5, it constructs the full space of symmetric normalized cocycles by Gaussian elimination, then checks the recursive construction on every basis vector and every disjoint pair/triple. It also checks the expected cocycle-space dimension and normalization. This includes the empty set, no nonempty admissible triples for |E|<3, and torsion coefficients. These computations support the written integral proof; they are not a substitute for it. No Lean was written or compiled.

## Not duplicates

No same-Stacks-tag pairs: this new agent algebraic lemma cites no Stacks theorem. No existing node states binary disjoint-subset integration. The cubic item is distinct for the reasons above. General Galois/group cocycle nodes do not supply the needed potential on the partial operation of disjoint union.

## Review by Q48

I read the chapter/unit records, the latest blueprint direct-images proof paragraph (3), the item and its parent cube-section-cubical-compatibility, and the statements of every cited node. The blueprint paragraph explains the ambient six-functor direct-image step; it does not prove the much lower algebraic assertion. The parent's step 3 needs exactly t=the third alternating difference of c to rescale frames. The item statement was therefore kept exactly, including c=1 through cardinality two and absence of divisibility assumptions. The binary auxiliary has its own complete hypotheses and explicit formula, and is not a clause of the cubic statement moved out wholesale. Its source field clearly labels the claim as agent-written; the unavailable Moret–Bailly context is reported above rather than asserted to have been read.

Step 1 uses only the finite-set definition: I checked that def-sfb-finite-infinite-set states the finite predicate, not an integration result. Its proof sets up the strong induction, verifies the empty/small-set base and restricts all hypotheses to F. Cardinality induction is the argument being written, not an invocation of an unstated geometric lemma. Step 2 uses precisely the new binary node's statement: symmetry and normalization come directly from t, and the four disjoint blocks (U,V,W,{x}) give exactly its three-block identity. F is finite and every U,V,W lies away from x, so all disjointness hypotheses hold. The node gives both b's singleton normalization and the required quotient, quoted verbatim in citations.json.

Step 3 gives c on every subset by a two-case formula and verifies the normalization in both cases. It needs only the b and c0 already obtained. Step 4 substitutes that definition, explicitly records the canceled quotient, and uses the original identity on (U,Z,{x},V). I checked the order of arguments and signs: symmetry changes t(U,Z,V) to t(U,V,Z) and t(U,Z union {x},V) to t(U,V,Z union {x}); q(U union Z,V)/q(Z,V) is exactly b(U union V union Z)b(Z)/(b(U union Z)b(V union Z)). No root extraction, nonempty-block condition, or torsion restriction enters. Empty blocks remain valid and the union may be smaller than E. Symmetry moves the unique block containing x to the third position. The final two steps are short explicit commutative-group cancellations, so they do not hide a further lemma.

I checked delivery-errors B–E against these actual files: the new node is statement-only and self-contained, uses the finite-set notion supplied by its one definition dependency, and has real logged searches; all two step citations use statements rather than their proofs and have literal quotes; no dependencies point back from the binary node to the item; the cubic argument stays in the item and includes its induction, mixed-block calculation and all edge cases. There are no proof steps over 2000 characters (the entire proof is 2279). I found no statement dispute or missing hypothesis requiring correction. The only new node is the genuine lower-degree integration lemma, and its handoff proof above explains why it is true independently of the cubic theorem.
