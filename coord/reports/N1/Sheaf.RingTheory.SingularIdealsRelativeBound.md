## What changed

Proved `Algebra.singularIdeal_map_le_relative_of_annihilator_bound` in
`Sheaf.RingTheory.SingularIdealsRelativeBound`, with its full original signature and visibility.
Added two proved private helpers: `Algebra.annihilator_eq_of_flat` transports the equality
of the first and second annihilators through flat base change, and
`Algebra.exists_uniform_power` clears localization denominators uniformly on a finite
spanning set. Proof-only imports are `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
and `Mathlib.RingTheory.Smooth.Flat`. Added the missing file header and module docstring.
Updated the item's DAG proof, proof dependencies and proof origin to follow this proof.

The source was read at https://stacks.math.columbia.edu/tag/07CT because this clone has no
`literature/stacks-project/smoothing.tex`. The argument follows its flat-annihilator and
Noetherian finite-generation argument on smooth principal localizations. It then uses
span and radical containment directly. The stated finite-presentation hypothesis on B
is preserved, although the mathematical argument does not need it.

## Proved and sorry left

Closed the one original hole:
`Algebra.singularIdeal_map_le_relative_of_annihilator_bound`
(node `lem-weil-pbc-singular-ideals-relative-bound`).
There are no sorries left in the item's module, no new holes, and no split-off statements.
The two private helpers are completely proved. The imported
`RingHom.annihilator_element_flat_base_change` is already proved in the library.
The final dry run checks the transitive axioms of every delivered declaration.

Edge cases: the finite-set induction covers the empty spanning set with exponent zero;
no nonzero-element or nontrivial-ring hypothesis is introduced. The radical membership
argument permits exponent zero, in which case the bound says 1 belongs to the target
ideal. The proofs work for π = 0, units π, g = 0, zero rings and arbitrary dB.

## No longer needed

Removed the trial proof import `Mathlib.RingTheory.FiniteType`: its theorem is already
available from the retained imports. No original imports were removed.
The argument does not need `lem-weil-pbc-finite-module-support-annihilator`
(Mathlib `Module.mem_support_iff_of_finite` / `Module.support_eq_zeroLocus`) or
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`
(Mathlib `PrimeSpectrum.zeroLocus_eq_iff`). They occur in the parent node's planned route,
but are not dependencies of this relative component. No quotient module, localized
quotient-module support, prime avoidance, or additional smooth-locus theorem is needed.
These are route-level omissions; no claim is made that the whole project's closure
ceases to need these nodes elsewhere. No Sheaf module is pruned from the original
import closure of this item.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG had one non-elementary step with no proof dependencies.
The updated node explicitly records the proved flat base-change dependency and the
Mathlib smooth-flat and finite-type-Noetherian leaves, and explains the finite-generator
argument. No mathematical error was found, no existing statement or definition was
changed, and no other module was adapted. The unit's realized statements and steps
remain untouched. The natural-language node mentions both relative and absolute
containments, whereas this component's Lean declaration proves only the relative one;
the absolute component remains the existing separate module and is not claimed here.

## Second reading by N1

1. **Visible declarations:** Compared the delivered module with the repository version. The theorem signature and visibility are byte-for-byte unchanged; only the proof, proof-only imports, header, and docstrings differ. The DAG node records the corresponding proof route and dependencies.
2. **Proof correctness:** Compiled the module with `lcompile.py`; it succeeds with no errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof uses only the existing flat-annihilator theorem, smooth-flatness, localization's zero criterion, and finite generation. Its private helpers are fully proved.
3. **Statements and dependencies:** No new public statement was added. The theorem proves exactly the relative containment in its existing Lean signature. The finite-generation helper is private and strictly intermediate. The imported annihilator theorem was searched and reused; no duplicate library statement was introduced.
4. **Route and pruning:** The unit's realized route is untouched. The direct smooth-localization route remains below the unit level. The removed trial import is unnecessary; the proof does not use the planned support, zero-locus, quotient, or prime-avoidance nodes for this relative component.
5. **DAG agreement:** The node's proof steps, `proof_deps`, and `proof_origin` now match the Lean proof. No new nodes or split-off holes were required.

Changed in this second reading: added this review record only; no Lean declaration or statement was changed.
