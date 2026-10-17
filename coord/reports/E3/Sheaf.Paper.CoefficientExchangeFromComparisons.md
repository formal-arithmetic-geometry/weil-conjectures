## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps`
with its unchanged public statement. The proof constructs the qcqs instances,
specializes the proved categorical three-step comparison, reverses its vertex
isomorphisms, rewrites the six factors, and proves both total-arrow factorizations.
The restricted square equation receives the explicit realized bounded object.

Repaired the implementation of `finiteDiscreteExchangeSteps` in the unclaimed
`Sheaf.Paper.FiniteDiscreteRealizationFunctor` interface: its three factors use
`no_expose` aliases of exactly the original constructions. Each alias has a proved
`_eq_original` certificate and an equation for component calculations. The original
total internal exchange and total etale exchange morphisms are unchanged. The three
private component statements in the item use the equal aliases. All existing public
signatures and every Challenge declaration stay identical; no adopted-source file
is changed. The independent reader should check definition preservation using those
three equality certificates.

Updated the existing node's proof and proof-origin note. Its statement, dependencies
and protected blueprint unit route are unchanged. No new mathematical premise,
node or split-off obligation is introduced. The caches are implementation aliases
of existing data, not a second construction or an arbitrary existence witness.

Change record: `coord/changes/E3-coefficient-exchange-step-interface.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps`
(node `lem-weil-pbc-coefficient-exchange-from-comparisons`).
Holes closed: 1. Holes added: 0. Statements split off: 0.
Neither delivered Lean module contains sorry.

All three cache defining equations, all three `_eq_original` certificates, and
`coefficientExchange_factorization` are proved. The existing component helpers
remain proved and are not counted again. Imported obligations are unchanged;
this is local closure, not an axiom-complete proof of the full target closure.

Both changed modules compile cleanly with the default heartbeat budget and the
unchanged 60-second file limit (interface 10.8 seconds, item 21.6 seconds). The original
`FiniteDiscreteCoefficientExchange` and `FiniteDiscreteExchangeRealization` consumers
also compile unchanged against both repaired modules, with no warnings. Their
unchanged sources are not included in the delivery.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.Paper.CoefficientDerivedFunctorAPI` and
`WeilConjectures.SixFunctors.BaseChange.Derived`: their declarations remain
available through the retained imports and are still used by the proof. No DAG
node or whole module is pruned; all three old proof dependencies remain needed.
No blueprint statement or realized unit step is bypassed.
The direct proof import of `FiniteDiscreteRealizationFunctor` records use of its
new equations and ensures it compiles before the item in the delivery tool's
sibling import order. The proof does not need the `ModuleCat.AB` shortcut import.

## Where the brief, the DAG or earlier work was wrong

The mathematical three-step plan works. Kernel normalization of exposed concrete
restricted-step values caused the complete proof to exceed the file limit. The
Sheaf cache interface avoids this while certifying the same three data values.
A local name for the bounded object also obstructed the square rewrite under simp;
the final proof supplies the object explicitly.

The current gate requires adopted-source public interfaces to remain verbatim.
The final repair therefore changes only the Sheaf interface and the assigned item.
The upstream arbitrary-coefficient pushforward-constructibility statement remains
marked STATEMENT-DISPUTED in its own module; its statement and existing hole are
unchanged and are not counted as proved here.


## Second reading by E3

1. Compared both delivered modules with the shared repository using `diff`.
   Every existing public signature is byte-for-byte unchanged. The three private
   component signatures and the body of `finiteDiscreteExchangeSteps` change only
   as declared in `E3-coefficient-exchange-step-interface.md`. Each new cached
   factor is defined by the corresponding original construction, and its proved
   `_eq_original` certificate identifies exactly that factor. Both total exchange
   morphisms stay original. There is no new hypothesis, weakened conclusion,
   arbitrary witness choice, hollow definition, or Challenge edit. Verdict: pass.
2. Independently compiled both modules through `lcompile.py --all`, then compiled
   scratch copies with `#print axioms` for the main theorem, all three aliases,
   all six equations, and the factorization theorem. These show only `propext`,
   `Classical.choice`, `Quot.sound`, and the already imported `sorryAx`.
   Neither delivered file contains a `sorry` or forbidden declaration. The axiom
   checks took 21.5 seconds for the item and 11.2 seconds for the interface, under
   the unchanged 60-second limit. Compiled unchanged scratch copies of
   `FiniteDiscreteCoefficientExchange` and `FiniteDiscreteExchangeRealization`
   against the delivered overlay; both passed without warnings. Verdict: pass;
   the imported open obligations mean this is local closure, not an axiom-complete
   target proof.
3. No statements were split off and no holes were added. Read the new alias
   definitions and equations against the original `MorphismDefs` constructions:
   their equalities follow by unfolding, and the factorization follows from the
   existing specified factorization theorem. Empty schemes, zero objects, and
   non-Cartesian squares introduce no exception, since these are formal
   adjunction identities and no cancellation of the exchange map occurs.
   Verdict: pass; no new mathematical premise or search obligation is hidden.
4. Read the argument from the main theorem through its component helpers, the
   existing `threeStepComparison`, and the original restricted exchange formulas.
   Searched both library roots for the comparison and factorization declarations;
   the proof uses the existing categorical comparison rather than restating it.
   Checked the retained import chain and the unit
   `dag/units/sk-thm-properbasechange.json`, including `realized`: all three old
   proof dependencies are used, no protected unit step is bypassed, and no whole
   module becomes unnecessary. The explicit interface import records a sibling
   dependency needed by the delivery compiler's import ordering. Verdict: pass
   after correcting the report's omitted direct-import removals.
5. Compared the node as parsed JSON: only `proof` and `proof_origin` differ.
   Its three steps now describe the actual comparison, restricted component
   identifications, cache certificates, and total factorizations. The union of
   their `uses` is exactly the unchanged `proof_deps`; statement, source,
   `stmt_deps`, unit, and Lean signature record are unchanged. No new nodes are
   required for the definitional implementation equations. Verdict: pass.

Second-reading changes: corrected `## No longer needed` to list the two removed
redundant direct proof imports, and restored the existing node's JSON indentation
so its diff contains only the intended proof updates. No Lean proof or definition
needed repair. Removed all scratch copies before delivery. Closure count remains
one original hole closed, zero added, zero split off; no whole module pruned.
