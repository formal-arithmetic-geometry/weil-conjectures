## What changed
Closed the original theorem by an explicit Lean reduction: expand
`rightDerivedBaseChange_app`, cancel the source classical single-complex comparison,
rewrite the identity homology comparison, combine homology maps, and apply the total
derived comparison. All original signatures are unchanged.

Added two modules. `DerivedUnitClassicalPullbackCoherence` is proved for arbitrary
bounded below derived objects using `derivedCohomologyPullback_eq_derivedUnit` and
`rightDerived_ext`. Its proof moves the identity comparison through the unit by
naturality, applies `rightDerivedFunctorPlusBaseChange_fac`, cancels the identity
factorization, and identifies the remaining underived section maps.
`IdentityDerivedHomologyComparison` states the remaining general identity coherence
lemma, separately from schemes, sections, base change, and classical comparisons.

## Proved and sorry left
Closed: `AlgebraicGeometry.derivedUnit_classicalPullback` (one original hole).
Also proved: `AlgebraicGeometry.derivedUnit_classicalPullback_coherence`.
Added one hole: `CategoryTheory.Functor.identityDerivedHomologyComparison`, node
`lem-weil-pbc-identity-derived-homology-comparison`. This is a decomposition with net
zero holes closed, rather than a complete sorry-free proof of the target closure.
There are no other sorries in the delivery.

All three modules compile without warnings using lcompile.py. The identity lemma
has been checked on the zero object and on single complexes in arbitrary degree:
it asserts the canonical identity comparison, so neither imposes an additional
hypothesis nor changes the map. Its remaining work is localization coherence for
the concrete homology comparison construction.

## No longer needed
Removed the direct proof import `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
from the original module. Its node and module remain needed through the new proved
coherence module; no original DAG dependency is pruned from the transitive closure.
No further imports, nodes, or modules are pruned.

## Where the brief, the DAG or earlier work was wrong
The original second proof step described identity comparisons cancelling without
an interface theorem for the canonical homology comparison. The new general lemma
makes that exact obligation visible. The DAG now distinguishes this remaining
coherence from the total derived-unit comparison, which has been proved.
LeanSearch was unavailable (HTTP Internal Server Error); actual search logs record
this, while LeanFinder and grep found no exact comparison. The blueprint search
found no existing node for identity-functor homology coherence. The unit's realized
statements and steps are preserved; these are tools for its existing stalk-map route.

## New nodes
`lem-weil-pbc-derived-unit-classical-pullback-coherence`: proved total derived
comparison for any bounded below object, with the existing derived-unit formula as
its dependency. Module: `Sheaf.AlgebraicGeometry.DerivedUnitClassicalPullbackCoherence`.

`lem-weil-pbc-identity-derived-homology-comparison`: the identity functor's canonical
homology comparison equals homology of its inverse derived identity comparison.
Module: `Sheaf.CategoryTheory.IdentityDerivedHomologyComparison`. It is strictly
one coherence step and does not restate the classical pullback theorem.

## Second reading by W2

1. I compared the delivered target module with the repository version. The theorem signature is unchanged byte for byte; the proof only replaces the original `sorry`, and the proof-only imports are correctly plain `import`s. I restored the target node's reformatted statement fields to the repository text.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors. The target theorem has no `sorry`; the one remaining `sorry` is the named split-off theorem `CategoryTheory.Functor.identityDerivedHomologyComparison`, with its node and source proof supplied. No forbidden declarations or hollow definitions occur.

3. The split-off identity comparison is a true, strictly simpler coherence statement: it concerns only the identity exact functor and homology, and is checked on zero objects and single complexes. It is not already present under another declaration in the project or searched Mathlib sources. Its docstring, node statement, proof steps, and imports agree.

4. The proof follows the unit route through `derivedUnit_classicalPullback_coherence`; it does not bypass the realized unit steps. The coherence module uses the existing derived-unit formula and the target uses the identity comparison only to pass from total derived maps to homology. The removed direct import is no longer needed by the target proof.

5. The DAG proof, proof dependencies, proof origin, and Lean declarations agree after restoring the unchanged statement text. The unit record is untouched.

Changed during second reading: restored the target node statement serialization and added this review section. No mathematical declarations were changed.

Axiom probes confirm that `AlgebraicGeometry.derivedUnit_classicalPullback_coherence`
uses only `propext`, `Classical.choice`, and `Quot.sound`; the target theorem and
`identityDerivedHomologyComparison` additionally use `sorryAx`, exactly from the
reported open identity-comparison theorem. These probes were scratch copies and
are not delivered. Independent second-reader searches used Loogle for the complex
homology comparison and LeanFinder for identity-complex/homology coherence, plus
local searches for the derived identity and homology comparison names. They found
no existing theorem closing the general identity comparison. The remaining step
requires descent through localization, rather than a direct simp identity; I left
the documented, strictly smaller obligation unchanged.
