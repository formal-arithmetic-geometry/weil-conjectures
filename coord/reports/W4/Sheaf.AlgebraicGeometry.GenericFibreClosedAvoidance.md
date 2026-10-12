## What changed

Proved `AlgebraicGeometry.exists_open_generic_fibre_closed_avoidance` in
`Sheaf.AlgebraicGeometry.GenericFibreClosedAvoidance`, preserving its complete signature
and visibility. Added proof-only imports of
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

Construct the reduced closed subscheme supported on
`D = C ∩ g ⁻¹' closure {y}`. Its composite map to T is quasi-compact. If y were in
the closure of its range, the existing specialization theorem would produce an
image point specializing to y. That image point is already a specialization of y;
T0 antisymmetry forces equality, contradicting the empty-fibre hypothesis. The
complement of the closure of the range is the desired neighbourhood. The final
disjointness proof uses the concrete range identity of the constructed subscheme.

Updated the existing node's proof, proof_deps and proof_origin to record this route.
The original source docstring is preserved; an inline comment identifies the
alternative argument. The unit record `sk-prop-normal-form` has no realized node
steps bypassed by this replacement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_open_generic_fibre_closed_avoidance`
(node `lem-sbc-generic-fibre-closed-avoidance`). No holes remain in the item;
no holes or new declarations were added. This is a proof, not a decomposition.
The used `AlgebraicGeometry.exists_specializes_of_mem_closure_range` is already
proved, with its existing node `lem-sc-picard-closure-specialization`.

The original signature compiles cleanly with lcompile.py. The proof uniformly
handles empty C or D, closed y, nonclosed y, and non-quasi-separated schemes.
It uses quasi-compactness alone; the original locally finite type hypothesis
is retained. No object is selected from an unproved theorem.

## No longer needed

No imports removed; no named dependency nodes or modules pruned (the original
node had no proof dependencies and the module had no proof-only imports).
The planned reduction to an integral closed base, scheme-theoretic generic
fibres, and finite-type empty-generic-fibre spreading via Tags 054W/055N is
unnecessary. These steps had no separate dependency nodes to prune. Both
existing public Mathlib imports remain required by the unchanged signature.

## Where the brief, the DAG or earlier work was wrong

The original DAG supplied a complete source argument but no named dependencies
for its non-elementary step. A shorter existing-library route is available:
`lem-sc-picard-closure-specialization`, realized by the source library's proved
quasi-compact image specialization theorem. No statement or definition was
wrong and none changed. Semantic and pattern searches via msearch.py found no
exact theorem; reading and ripgrep search of the source library found the
usable stronger specialization theorem. Its proof and the supporting prime
spectrum theorem were read before use.

## Second reading by W4

1. **Repository comparison.** Compared the delivered module with the repository version. The theorem
   signature, visibility, and docstring are unchanged; only proof-only imports and the proof body
   differ. Verdict: pass.
2. **Compilation and axioms.** Compiled the module with `lcompile.py` and checked the theorem's
   axioms. There are no `sorry`s, forbidden declarations, or warnings; the axioms are exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Split statements and reuse.** No statements were split off and no declarations were added.
   The proof uses the existing sorry-free `exists_specializes_of_mem_closure_range`; no duplicate
   theorem was introduced. Verdict: pass.
4. **Pruning and imports.** The two added imports are proof-only and necessary: the first supplies
   the reduced closed-subscheme construction and range identity, and the second supplies the
   quasi-compact image specialization theorem. The existing public imports remain required by the
   unchanged signature. The proof dependency and node record agree with the proof. Verdict: pass.
5. **Mathematical route and unit.** The constructed vanishing-ideal subscheme has exactly the
   closed subset `C ∩ g ⁻¹' closure {y}` as its underlying range. Quasi-compact image
   specialization plus the T0 antisymmetry of a scheme proves the neighbourhood and disjointness,
   including empty-set cases. No realized unit step is bypassed and the target statement is
   unchanged. Verdict: pass.

Changed only the proof body, proof-only imports, and the existing node's proof metadata; no
statement or definition was changed.
