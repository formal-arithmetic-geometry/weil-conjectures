## What changed

Proved `WeilConjectures.FiniteFieldDatum.frobenius_rootsOfUnity_power` in
`Sheaf.NumberTheory.FrobeniusRootsOfUnityPower`, preserving its statement and all public imports.
Added proof-only imports for the characteristic/cardinality theorem and the existing primitive-root
node. The proof explicitly supplies the divisibility and torsion-cardinality hypotheses of the
existing Tate-module rank theorem, proves the arithmetic scalar action on coordinates, and deduces
the geometric scalar action by cancellation with the inverse unit. Updated the existing node's proof
steps to describe these calculations.

## Proved and sorry left

Closed: `WeilConjectures.FiniteFieldDatum.frobenius_rootsOfUnity_power`
(node `lem-pur-frobenius-roots-of-unity-power`), the module's only original hole.
Holes added: none. Sorries left in the delivery: none. No split-offs or new declarations.

## No longer needed

No original imports, declared dependencies, nodes, or modules were removed: the proof follows all
four steps of the declared route. The coordinatewise inverse action needs no additional theorem
constructing compatible inverse residues; it follows from the inverse field automorphism and unit
cancellation. The unused trial import `Mathlib.Algebra.CharP.Invertible` was removed before delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition needed repair. The finite-field datum does not register
characteristic p directly; the proof recovers it from its cardinality and transfers it to the closure.
The unit record `sk-def-purity-conv` has no realized proof steps to bypass. The proof includes N=1,
negative inverse exponents, and the Tate module's zero coordinate without extra hypotheses.

Validation: compilation and the delivery tool's declaration/axiom probe are recorded by delivery.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
