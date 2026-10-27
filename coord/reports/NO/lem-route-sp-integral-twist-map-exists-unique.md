# Stage-1 delivery: lem-route-sp-integral-twist-map-exists-unique

## Files written

- dag/nodes/sec-smooth-purity/lem-route-sp-integral-twist-map-exists-unique.json: statement, split, no exact Mathlib match. Replaced the provisional signature dump with a self-contained statement for arbitrary schemes, explicitly identifying every coefficient ring, reduction, tensor factor, module tower and projection.
- citations.json: 21 verbatim statement quotations, one for every node cited by every numbered proof step.
- report.md: this report. No new DAG nodes and no new Mathlib leaves.

## Attachments

None. The exact declaration AlgebraicGeometry.ProEtale.spIntegralTwistMap_existsUnique is still `sorry` in lean/Sheaf/Paper/ProEtaleTateTwists.lean:315–327. Searches for its blueprint tag, name, integral twist system and integral transition notions under lean/WeilConjectures returned no exact project declaration. The generic internal-module limit construction in WeilConjectures/CategoryTheory/Monoidal/Mod/Limits.lean proves only a component and is not an attachment of this item.

## WANTED

None. Read the current latest blueprint sources and the local Stacks sources; no external document or SGA source is needed.

## What was wrong and what changed

The imported node was a machine-generated placeholder with no statement dependencies, proof, or blueprint search result. It described a unique map without explaining the precise ambient category. The Lean statement is existence and uniqueness in abelian sheaves after forgetting two DIFFERENT scalar rings; it does not assert a morphism in a single module category. The new statement preserves that distinction and makes no unproved semilinearity claim. It uses the actual positive levels ell^(n+1), not uniformizer-power levels, and tensor_Z with the root sheaf, exactly as the source definitions do.

The attached Lean theorem has only X : Scheme, ell prime and E ≤ F as hypotheses. The Tate-twist sketch assumes ell invertible on X for its local-freeness assertions, but this route lemma needs neither invertibility nor local freeness: the roots exist and the compatible-limit argument works on arbitrary X. This is a faithful expansion of the actual provisional signature, not an added assumption or weakening. No target statement was changed. The report does not mark a false statement dispute: the imported Lean proposition is true as written.

The proof no longer hides the compatibility square under the word “commutes.” It identifies the chosen integral map with postcomposition by the valuation-ring inclusion, identifies the chosen j_n with the quotient class map using the EXISTING uniqueness lemma, checks adjacent reduction commutativity on representatives, and writes the tensor interchange equality. It uses a module/sheaf equivalence and sectionwise limits to justify forgetting the actual module limit, instead of citing finite-limit preservation for an infinite tower.

## Source and search record

Read literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.md and its proof (especially “The integral twist”), and literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md. The implementation definitions and theorem were read in lean/Sheaf/Paper/ProEtaleTateTwists.lean:49–327. The proof is explicitly agent-written: the blueprint supplies the integral-limit route, while this coefficient-field transition obligation is expanded here.

Read Stacks Tag 03DB, sites-modules.tex, lemma-limits-colimits, and Tag 03CO, lemma-limits-colimits-abelian-sheaves, including their proofs: module limits commute with forgetting and abelian limits are computed on sections. Read the matching existing def-pur-sheaf-inverse-limit node, the internal/sectionwise equivalence node, and the general internal-module limit construction in the project. Read Mathlib/CategoryTheory/Limits/HasLimits.lean:249–256 (limMap and limMap_π): generic limit functoriality alone does not identify j_n, prove tower naturality, or identify the underlying module cone, so the item is not a one-line Mathlib specialization.

All Mathlib searches ran through msearch.py and are preserved in searches.jsonl, with the exact query text copied to the node. Two concept phrasings, LeanFinder, LeanSearch, Loogle and local Mathlib grep were used. LeanSearch and the second Loogle query find limMap; the first Loogle query is empty. The searches restricted to guessed Mod/Mod_ Mathlib paths were empty; the broadened Monoidal grep finds internal monoids, not internal modules. No empty result was recorded as service failure, and no service failure was recorded as mathematical absence. No new nodes need additional search records.

Whole-DAG statement searches included spIntegralTwist, spEllMap, module-object limit creation, finite quotient transitions, underlying limits and coefficient-ring maps. Blueprint searches included Tate twist, inverse limit, module objects, forgetful functor, finite quotient, integral transition and uniqueness. sk-def-sp-tate-twist describes the construction under invertibility and is not the exact arbitrary-scheme, projection-normalized existence-and-uniqueness assertion; same_as is empty. Existing finite-level transition and generic limit nodes are reused. No new notion or clause of the item was moved to a new node.

## Review by NO

I read delivery-errors B–E in full and checked the actual statements, not the cited nodes' proof bodies. Every object in the new statement is introduced there; all specialized notions have definition dependencies. Quotient rings are explicitly ell powers and coefficient maps are pulled-back continuous-function maps, not silently identified with another coefficient category. The roots and their power arrows require only positive exponents; ell^(n+1) is positive since ell is prime.

For step 1, lem-weil-l-adic-extension-absolute-value says exactly the uniqueness needed for the restriction of F's norm to E. sk-def-sfb-condensed-ring defines the inherited topology and valuation subring, so this inclusion is continuous. def-sfb-continuous-map-condensed-ring-map states postcomposition is functorial; sk-def-sfb-pulled-back-coefficients states pullback is a functor on ring objects. Finally lem-route-sp-integers-map-exists-unique supplies precisely the uniqueness OVER E_X → F_X used to identify the constructed inclusion. Both its monoid-hom condition and coefficient square were checked; no merely abelian uniqueness was substituted.

For step 2, the two functoriality statements transport the explicitly written quotient class formula and its reduction square. lem-route-sp-ell-map-exists-unique says exactly that this square specifies j_n uniquely among the same underlying arrows. I used this to identify j_n, not to infer an unstated transition-compatibility theorem. The representative calculation is elementary, and continuity of the quotient transition map with discrete source needs no additional hypothesis. I also cite lem-sp-ell-quotient-finite-discrete for continuity of the integral reductions, checking its extending-norm/topology hypotheses with def-weil-l-adic-coefficient-extension and def-sfb-coefficient-extension-integers-topology. Step 2 is accordingly marked non-elementary. The phrase “quotient inclusion” is not used to deduce injectivity.

For step 3, the two coefficient composites agree on every quotient representative, then functoriality transports the equality. sk-def-sfb-sheaf-tensor supplies the tensor bifunctor, def-pur-roots-of-unity-sheaf gives the SAME ell-power arrow on both systems, and lem-sp-integral-level-transition-unique states that r tensor v is the underlying arrow of the chosen module transition. Thus these citations say exactly what the interchange formula uses. Identity and longer transition arrows follow by induction, not an assumed naturality lemma.

For step 4, def-weil-pbc-internal-abelian-sheaf-module-equivalence gives an equivalence retaining the underlying abelian sheaf identically. I checked its hypotheses: the small-site/coefficient-universe convention is explicit, R_G is commutative, and the tensor is sheafified objectwise tensor. The strong monoidal sheafification statement in sk-def-sfb-sheaf-tensor gives its monoidal local-equivalence condition: tensoring a sheafification equivalence still sheafifies to an isomorphism. The same tensor structure and rings are used on both sides. def-pur-sheaf-inverse-limit states existence AND the sectionwise compatible-tuple description for module sheaves, including the abelian case. This justifies the actual forgotten module cone, via the equivalence and projection-preserving uniqueness of limits; it does not assume the finite-limit-only lemma preserves a countable limit. The adjacent tower is linear by the exact statement of lem-sp-integral-level-transition-unique. The index is the small category N^op.

For step 5, the cone is written explicitly, and def-pur-sheaf-inverse-limit gives exactly its universal property and the coordinate description needed for existence and uniqueness. The coordinate rule is additive and commutes with restriction, and joint coordinate equality proves equality of sheaf morphisms. This is an elementary application of the already cited limit description, with no new hypothesis or hidden lemma. No step is longer than 2000 characters (all below 2000).

I tested E=F (j_n and the resulting limit map are identities by uniqueness), n=0 (quotient modulo ell, not a missing index-zero root), a ramified extension (ell powers remain well defined without changing to uniformizers), empty X, and X of characteristic ell (no local rank-one assertion is needed and possibly trivial root groups cause no obstruction). The explicit quotient representative calculation works with noninjective coefficient maps as well, so no unproved injectivity is hidden. No flatness, finite-type, Noetherian or inverse-image/infinite-limit interchange is used.

## Tool uses and duplicate check

No new nodes were created, so no same-tag new/existing pairs occur. The split_report declares generic off-unit tool uses for norm uniqueness and the internal/sectionwise module equivalence; these perform general infrastructure tasks, with no change to the purity unit's route. The other proof citations are definitions, the existing finite-level transition in this unit, or the existing coefficient-map uniqueness obligations. No tool_uses maintainer field was edited.

## Unfinished work

None in the requested stage-1 split. Existing cited nodes retain their own separate proof obligations. No Lean was written, and no compiler, Lake, or build command was run.

## Concurrent dependency refresh

The first packaged dry run passed at 6ebe5bec505, then the push refused a stale quotation because the independently reviewed lem-route-sp-ell-map-exists-unique had landed in the meantime. I reopened its new full statement: it still gives exactly the same uniqueness among all abelian-sheaf maps, with the specified reduction square and arbitrary X. I refreshed all citation quotations against current statements and made continuity of the integral reductions explicit using existing lem-sp-ell-quotient-finite-discrete. No new DAG node was needed. The added topology tool is declared in split_report.

The integral coefficient uniqueness obligation also landed while the retry fetched current server state. I read its new statement in full: uniqueness is among underlying abelian maps preserving the ring-object unit and multiplication, with the same coefficient square, exactly as used in step 1. Its norm conventions are restrictions from the fixed algebraic closure and agree with step 1 by uniqueness of extending norms. Citation quotations were refreshed to the precise relevant uniqueness clauses of both concurrent obligations.
