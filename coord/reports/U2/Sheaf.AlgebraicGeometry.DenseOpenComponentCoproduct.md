## What changed

Proved `AlgebraicGeometry.exists_dense_open_component_coproduct` in
`Sheaf.AlgebraicGeometry.DenseOpenComponentCoproduct`. The proof constructs the open
complement of the other irreducible components, restricts each closed immersion,
uses Mathlib's reduced-target surjective closed-immersion isomorphism theorem,
shrinks by the prescribed dense opens, and glues the resulting disjoint open
immersions through the universal finite coproduct property. The existing signature
and docstring are unchanged. The second reading removed an unused local integrality binding.
All public imports are retained: they supply declarations used in the signature.
The existing node's proof, proof_deps and proof_origin now describe the written proof.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_dense_open_component_coproduct`.
Added zero holes. No `sorry` remains in the delivered module, and no declarations
or split-off statements were added. A scratch-copy `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports removed. The public imports supply signature declarations:
`ClosedImmersion` for `IsClosedImmersion`, `Limits` for scheme coproducts, and
`Properties` for `IsReduced` and `IsIntegral`. They are not merely proof-only imports.
Although Properties is transitively available, removing its public import requires
an interface change record; this proof delivery preserves that public interface.
Removed `def-pc-integral-scheme` from the node's proof dependencies: irreducibility
of the images already suffices for the density argument. It remains a statement
dependency because the unchanged signature assumes integral components. No Sheaf
module was removed, and no global import-closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan was mathematically sound but described generic-point arguments
rather than the closure argument actually used. Its integrality proof dependency
was unnecessary. The first report did not record this difference; it is repaired in this delivery. The concrete categorical
gluing is supplied directly using Mathlib's universal finite coproduct and disjoint
open-immersion cover theorems.

## Second reading by U2

1. Compared the whole module with the repository version using `diff`. Verdict:
   the existing theorem signature and docstring are byte-for-byte unchanged; there
   are no definitions or new declarations. Only the proof differs.
   No statement change or change record is required.
2. Compiled the module locally and compiled a scratch copy with `#print axioms`.
   Verdict: no errors or warnings; no sorry or forbidden declaration mechanism;
   the theorem uses only propext, Classical.choice and Quot.sound.
3. Read every local step. Verdict: no split-off statements or new nodes exist.
   Checked the empty family (the cover forces X empty), the single-component case,
   and intersecting components (their intersections are excluded from W_i).
   The reduced-target hypothesis is used in the closed-immersion isomorphism step.
4. Searched lean/ and Mathlib with alternate component/coproduct terms and used
   LeanFinder for disjoint-open covers and coproduct restriction. Verdict: the
   existing proof already uses the applicable Mathlib results; no shorter combined
   geometric result was found. The related SigmaDescRestrictIsIso module has a
   private restriction comparison, not an available public replacement here.
   Removed the unused local integrality binding. The three public imports
   supply signature declarations; no proof-only public imports were added.
   Read dag/units/sk-thm-p1.json: this is below its realized steps, and the unit's
   curve-calculation and normalization route is preserved.
5. Read the existing node against the complete Lean proof. Verdict: its statement
   agrees with the unchanged signature; repaired proof, proof_deps and proof_origin
   to record the component-closure proof, nonempty dense intersections, universal
   coproduct comparison and disjoint-open cover. The proof dependency union matches
   the steps; no new node fields are needed.

Second reading changed only the unused proof binding, existing node proof metadata,
and this report; it retained the sound proof construction and public imports.
