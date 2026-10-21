## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-local-frobenius-weil-morphism-naturality.json`: item, statement, split into six proof steps. The statement and its statement dependencies are unchanged. Mathlib verdict: no exact match for all clauses on the specified raw rational constructible categories.
- `citations.json`: nine entries, covering every step/node citation, each with a contiguous verbatim quotation from the cited statement.
- `report.md`: this report. No new DAG nodes; no Mathlib leaves created. `searches.jsonl` was produced by the required search command. `write_split.py` is sandbox-only working material.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for local-Frobenius and Weil-morphism naturality names. `CategoryTheory.Iso.powSuccStr_hom_naturality` in `TraceFormula/FrobeniusIterate.lean:107` is a generic helper for just iterated-structure intertwining. `AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible.frobenius_hom_naturality` in `TraceFormula/Slop/Basic.lean:197` concerns Weil objects for the identity in a different coefficient presentation. Neither states all the item's clauses, including its point transport and specified semilinear return, in the raw rationalized categories. Neither is claimed as an attachment.

## WANTED

None.

## What was wrong and what changed

The item had a statement and searches, but no proof. The statement is well typed and I found no false clause. In particular it correctly uses `g_X^n xbar = xbar g_s^n`; replacing this with `g_X^n xbar = xbar` would be wrong. I preserved every clause, including all rational constructible morphisms, noninvertible Weil-pair morphisms, and the absence of an integral Weil-lattice or finite-reduction Tor-amplitude assumption.

The proof supplies the argument rather than moving any clause into a new node. It constructs the composite transport `J_r`, proves its naturality by induction, and explicitly conjugates it by the specified comparison `c_r`. It expresses the return comparison as `b a^{-1}` for the two specified composition comparisons. The Weil-map induction writes its composition comparison `k_r` explicitly. Finally the two resulting squares are multiplied to obtain the operator identity. All six steps are below 2000 characters; none hides a separate comparison theorem. The non-elementary input about the specified comparisons is already exactly the statement of `lem-trf-integral-pullback-comparison-realization`.

## Blueprint and duplicate searches

I read `dag/chapters/sec-fourier-transform.json`, `dag/units/sk-def-trace.json`, the current `main-20261015` trace-function source, and the current local-Frobenius source in `sec-poincare-duality/sk-lem-finite`. The unit defines the trace by the local operator; this split proves the naturality needed for that operator without changing the unit or chapter route. This item is not the unit's key node, so no realized fields were changed. The blueprint provenance already names `def-fd-trace-function` and a precise formula; it is preserved and its place is explained in `split_report.blueprint`.

`tools/blueprint_refs.py ancestor` confirms that ancestor. Whole-blueprint searches for `point transport`, `Frobenius`, `iterated local Frobenius`, and `Weil morphism`, together with whole-DAG searches for iterated point transports and iterated Weil-map naturality, found definitions and related results, but no existing node stating this whole item. I opened `def-wf-weil-category`, `lem-wf-internal-hom-weil`, `lem-fd-weil-pullback-local-frobenius`, `lem-wf-rational-stalk-exact`, `lem-trf-iterated-weil-cocycle`, `lem-trf-frobenius-transport-induction`, and `lem-trf-derived-pullback-coherence`. They concern definitions, internal Hom, geometric pullback, the heart, strict finite coefficients, or a different transport identity. No duplicate node is introduced.

## Not duplicates

No new nodes were created, so there are no new/existing pairs requiring same-tag distinctions.

## Mathlib searches

The inherited searches were retained. I ran and read six further searches through the required `msearch.py` command, logged in `searches.jsonl` and appended with their exact tool and query texts. They include LeanSearch, two distinct LeanFinder phrasings, Loogle, and two source grep searches. No service was unavailable. The specialized phrasing finds Witt-vector and ring Frobenius results. The abstract phrasing finds endofunctor-algebra homomorphism equations. Loogle finds `CategoryTheory.NatTrans.naturality`. I read `Mathlib/CategoryTheory/NatTrans.lean:53` onward and `Mathlib/CategoryTheory/Endofunctor/Algebra.lean:65` onward: natural transformations compose and algebra morphisms intertwine one structure map, but these do not give all six assertions about the specified point transport, return, and Weil iterates in one specialization. Thus the item is split, not marked Mathlib. No new leaf merely repackages elementary category identities.

## Review by Q148

I read the item's current blueprint source, the related current local-Frobenius source, and the full statement of every statement dependency. There are no new nodes whose sources need a separate review. The proof is marked agent-written: the blueprint specifies the alternating-trace formula and the local-operator construction, but does not itself write these naturality calculations. I used existing theorem statements as inputs rather than attributing the calculations verbatim to the blueprint or to a Stacks tag. No SGA source was used.

For step 1 I checked clause 3 of `def-weil-finite-coefficient-point`: it defines the rational point-fiber functor on all morphisms of the raw scalar localization. I then checked clause 2 of `lem-weil-frobenius-point-transport-natural`, which explicitly includes coefficients E and says its equality for every morphism of the constructible category. Taking E=F supplies the exact starting square, with no integral representative restriction. Its naturality domain includes the pullbacks T^j N used in the next step.

For step 2 I checked the actual statement of `def-weil-local-frobenius-trace`: I is the product of the successive point transports followed by the pullback-composition comparison. I wrote the base and inductive equation for that product, rather than claiming an unspecified transport of equalities. The statement of `lem-trf-integral-pullback-comparison-realization` explicitly supplies natural comparisons, arbitrary finite-iteration compatibility, and their equations in the raw rationalized constructible categories. It therefore supplies the natural `c_r` and identifies this I with the specified one. The inverse is used only for an isomorphism of functors, not for w.

For step 3 I checked that the same comparison node asserts both naturality and compatibility with equality of scheme morphisms, after rationalization. This is why the two comparisons a and b can have a common source H for the exact return equality given in the item's hypotheses. I checked their directions: a maps H to S_n P and b maps H to P G_n, so b a^{-1} has exactly the type of rho. The two displayed naturality equations multiply with no missing map. This is a two-square calculation, not an unproved comparison lemma.

Step 4 uses only the previously proved equations of steps 2 and 3 and Q's functor laws. The application of step 2 has w=P(v), with source P(M) and target P(M'); applying Q to the rho square gives exactly the first replacement in the written calculation. It yields R naturality for every underlying v, before any Weil-pair condition is imposed.

For step 5 I read the morphism clause in `def-weil-weil-sheaf-complex`: v alpha = beta G_1(v) has no invertibility condition on v. I checked the recursion in `def-weil-local-frobenius-trace`, and the naturality of its explicitly inserted k_r from the comparison node. The induction's source is G_{r+1}(A); after k_{r,A} it is G_r G_1(A); the one-step intertwiner can therefore be sent through G_r. Naturality of k_r produces k_{r,B} G_{r+1}(v), giving precisely the required conclusion. No cocycle lemma at finite coefficients, or a hidden rational/integral identification, is used.

For step 6 I checked the local-operator definition in `def-weil-local-frobenius-trace`. Applying D to the step-5 equality and then multiplying by R(A) has matching source D(A) throughout. Step 4 moves D(G_n v) across R(A), and the resulting composite is exactly the other local operator followed by D(v). Nothing cancels v or assumes it invertible. The cited comparison theorem explicitly excludes a finite-Tor assumption on reductions, and all point-transport naturality was already at rational coefficients; thus the proof adds neither forbidden hypothesis.

I tested n=1 and r=1 (the base squares), identity maps, zero maps, zero complexes and shifts, and X_0=Spec(k_0). On constant point complexes with trivial point transport the conclusion is v A^n=B^n v whenever v A=B v; this includes noninvertible projections intertwining block-diagonal invertible operators and a two-dimensional Jordan block with its invariant-line inclusion. For a rank-one operator lambda the local action is lambda^n. The return argument uses only rationality over F_{q^n}, so it also applies when the geometric point has smaller period dividing n. These checks support the full domain and both recursion directions. There was no statement correction to make.

Finally I checked B--E of `coord/delivery-errors.md`: unchanged self-contained statement and definitions, no unsplit new-node proof, no invented Mathlib searches, no redundant elementary nodes, no use of a cited node's proof or missing theorem, explicit induction base/step, exact return equality, and full hypotheses at each use. `citations.json` was checked against the current statements as contiguous verbatim substrings. The two off-unit results are declared in `split_report.tool_uses`: single-step transport naturality and specified pullback comparison coherence are generic inputs, not a replacement for the unit's route.

## Unfinished work

None in the stage-1 split. Independent mathematical review and subsequent stages remain the maintainer's work.
