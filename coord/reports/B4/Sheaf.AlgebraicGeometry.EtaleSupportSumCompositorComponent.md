## What changed

Filled `AlgebraicGeometry.Etale.etaleSupportSumCompositor_app` in the assigned module.
The statement, all public imports, and all other existing declarations are unchanged.
Added only proved private helpers and private proof imports.

The proof first shows that the actual graph sheaf map is invertible for every
compactification, using the support construction, a finite Zariski-main compactification,
and cancellation of the monic inclusion into direct image. It then identifies the support
and sum sheaf compositors by the composite restriction adjunction and the existing
nested-summand formulas. This yields section preservation for the specified sum compositor.
The graph-derived inverse is the exact compactification unit by its construction.
The existing tower and refinement unit theorems now give the requested equation directly
on the tower `k.ofComp d`. Naturality and cancellation finish at the specified object `M`.
The item node records these steps and the actual dependencies.
The derived comparison families returned by `quasifiniteCompactSupportExact` are discarded:
only its normalized sheaf identifications and nested-summand equations are used.
The actual graph maps are identified independently by monicity, and their exact units
are identified by unfolding the defining localization formulas.

Only the assigned module and its own node are changed. There are no interface changes,
consumer adaptations, or new modules. All choices in the private proofs are locally
eliminated existential witnesses in proofs of propositions; no data definition is chosen
from a mere existence theorem. The arguments use adjunction bijections and isomorphism
cancellation, which also apply to identities, empty schemes, and the zero coefficient ring.

## Proved and sorry left

Closed 1 of 1 local holes: `AlgebraicGeometry.Etale.etaleSupportSumCompositor_app`
(node `lem-pur-etale-support-sum-compositor-component`).
Added 0 holes; 0 split off. No `sorry` remains in the delivered module.
Validated the exact delivered Lean file with `lcompile.py`: exit 0, no warnings,
51.5 seconds (under the unchanged 60-second limit). A direct signature comparison
also confirms that the theorem statement is verbatim unchanged.
The proof uses existing project declarations, including
`AlgebraicGeometry.Etale.exactCompactificationUnit_tower`; their existing downstream
obligations are not claimed as closed here.

## No longer needed

No original public import is removed, and no existing module is withdrawn.
The proof does not directly use `lem-sfb-exact-compactification-unit-composition` or
`lem-sfb-etale-support-nested-summands`: it uses the former's existing tower/refinement
steps directly, and the latter's nested-summand conclusion through the stated
`quasifiniteCompactSupportExact` package. These remain transitive dependencies, so this
is not a claim that their modules can be deleted.
The broad comparison-coherence theorem `lem-amb-unbounded-compact-support-comparisons`
is no longer a direct proof dependency: the statement still uses its compositor API,
and the exact-unit refinement/tower declarations handle the required comparisons.
Removed the exploratory private import of `ExactCompactificationUnitComposition`.
No whole module is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The previous single proof step concealed the identification
of the actual graph maps with exact units and the sheaf-compositor normalization.
Both are now proved explicitly. The general composition theorem returns an equation for
chosen compactifications; its finer existing tower and refinement statements give a
shorter route to this theorem's already specified tower and arbitrary compactifications.
The unit route is unchanged.

Additional existing tools used explicitly are the section-preserving support construction,
Zariski main, the finite graph sheaf isomorphism, the monic compactification inclusion,
and the exact-unit tower/refinement lemmas. They serve the original support-normalization
argument and do not replace a blueprint unit.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
