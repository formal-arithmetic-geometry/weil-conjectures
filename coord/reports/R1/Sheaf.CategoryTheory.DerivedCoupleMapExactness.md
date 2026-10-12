## What changed

Proved `CategoryTheory.derivedCoupleMapData_exact` without changing its public
signature or docstring. Four private, proved helpers organize conversion of
image/kernel equality to exactness and the three generalized-element chases.
Added the proof-only import `Mathlib.CategoryTheory.Abelian.Refinements`.
The second reader removed `family_transport` and used Mathlib's existing
`eqToHom_naturality` on pairs of indices at each call. The proposed helper
generalization and its change record are consequently absent from this delivery.
No existing statement or definition changes; no forced adaptations or new nodes.

## Proved and sorry left

Hole closed: `CategoryTheory.derivedCoupleMapData_exact`
(node `lem-sp-derived-map-exactness`), the only original hole in the module.
Holes added: none. Holes left: none. This is one proof, not a decomposition.
`#print axioms CategoryTheory.derivedCoupleMapData_exact` in a scratch copy
reports exactly `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`.

## No longer needed

No old proof dependency, import, node or module was pruned. Both old
`proof_deps`, `def-sp-abelian` and `lem-sp-abelian-refinements`, remain used.
The construction import provides the statement's maps and descent equations;
the refinements import is proof-only and necessary for the chases.
The sandbox's redundant private `family_transport` helper was removed.

## Where the brief, the DAG or earlier work was wrong

The earlier returned helper duplicated a private transport theorem elsewhere.
Generalizing that helper merely avoided a verbatim duplicate: Mathlib already
provides the required transport identity as `eqToHom_naturality`. Using that
identity directly resolves the duplication and avoids an unnecessary interface
change record. No fault was found in the exactness statement or its proof plan.
The assigned unit `sk-prop-av-pqf-finite` is geometric and its `realized` fields
are empty; this pre-existing placement does not make this auxiliary exact-couple
node a realization of the unit's statement or steps. No unit route changes.

## Second reading by R1

1. Compared the delivered module with the repository using `diff`, then checked
   the public theorem signature and existing docstring byte for byte. Both are
   identical. The only public import is unchanged; no existing data definition
   or public declaration was altered. Verdict: pass.
2. Read all three chases and their index transports. Local compilation of the
   original sandbox proof and the final scratch version succeeded without
   warnings; the latter's printed axioms are precisely the permitted three.
   No `sorry`, forbidden declaration, hollow definition, or arbitrary witness
   from an unproved existence statement occurs. The delivery tool additionally
   checks every declaration's axioms. Verdict: pass.
3. No statement is split off and no new hole or node is added. The private
   helpers are fully proved, and isolate genuinely different parts of the
   argument. Degenerate zero maps and `s = 0` require no exceptional case:
   the chases use only the displayed exactness equations, epi refinements and
   equality transport. Verdict: pass.
4. Repeated the transport search with `msearch.py ... grep eqToHom_naturality`
   and inspected Mathlib's declaration. Removed the redundant helper in favor
   of this existing lemma. Searched the upstream CategoryTheory sources and
   Sheaf's derived-couple modules; `DerivedCoupleExact` imports this item, so
   it cannot shorten this proof without a cycle. The refinements API supplies
   the shortest available direct route for the three raw-map equalities.
   All old proof dependencies remain used, and the unit route is unchanged.
   Verdict: pass after removing the helper.
5. Read `lem-sp-derived-map-exactness.json`, the construction module, and the
   unit's `realized` record. The existing four proof steps describe exactly
   the conversion/refinement argument and the three chases implemented here;
   `proof_deps` and `proof_origin` remain accurate. No new node is needed.
   Verdict: pass.

Second-reading changes: replaced every transport-helper call by Mathlib
`eqToHom_naturality`, removed the helper and its extra universe, removed the
obsolete generalization change record, and rewrote this report to describe the
final delivery and explicitly name the closed and added holes.
