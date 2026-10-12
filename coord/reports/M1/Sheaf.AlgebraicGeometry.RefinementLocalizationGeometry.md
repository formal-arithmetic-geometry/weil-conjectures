## What changed

Proved `refinement_localization_geometry` in
`Sheaf.AlgebraicGeometry.RefinementLocalizationGeometry` without changing its signature
or existing docstrings. Added the proved private helper `localized_factor_homeomorph`.
Added proof-only imports `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.RingTheory.RingHom.Etale`, and `Mathlib.AlgebraicGeometry.PullbackCarrier`.

The proof follows all four steps of
`lem-weil-pbc-refinement-localization-geometry` directly from Mathlib. Spectrum
surjectivity bounds the kernel by the nilradical, giving injectivity over the domain.
Localization base-change instances show each factor ring is a domain. Finite and
etale base change and composition give the cover properties over U. The helper
constructs the maps from the individual localizations, checks their compatibility
using localization extensionality, and cancels the upper pushout square from the
outer tensor-product pushout. Applying Spec produces the required base-change
square. Universal homeomorphisms persist under base change, and their ordinary
homeomorphism property implies surjectivity.

Validation: single-file compilation passes without warnings. The original theorem
signature was compared verbatim. Every line has at most 100 characters. Empty Fin r
is covered by the empty-product identity; no nonempty index-set assumption is used.
The helper needs only invertibility of s in T and works for arbitrary rings,
including the zero ring. No data is selected from an unproved theorem.

## Proved and sorry left

Closed one original hole: `refinement_localization_geometry`
(node `lem-weil-pbc-refinement-localization-geometry`).
`localized_factor_homeomorph` is also proved. No holes remain and no holes were added.
This is a proof, not a decomposition; no Sheaf or WeilConjectures theorem with sorry
is used. The delivery dry run checks the theorem's axioms.

## No longer needed

None. No existing imports, nodes, or modules were removed. The node originally had
no proof dependencies; the four-step argument is now implemented using Mathlib.
All three added proof-only imports provide infrastructure used in the proof.
No reduced tensor-product splitting theorem is needed, as already specified by
the original node and docstring.

## Where the brief, the DAG or earlier work was wrong

None. The existing four-step plan is sufficient and the unit route is preserved.
The localization base-change and pushout-cancellation infrastructure in Mathlib
closes the previously unformalized geometry. No statement or definition changes,
forced adaptations, or new nodes are required.

## Second reading by M1

1. Compared the delivered module with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only
   proof-only imports, a private helper, and proofs were added. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked its axioms. It compiles
   without warnings, has no `sorry`, forbidden declarations, or hollow
   definitions, and the target depends only on `propext`, `Classical.choice`,
   and `Quot.sound`. Verdict: pass.
3. Searched the repository and Mathlib-facing declarations for duplicates and
   checked edge cases, including `r = 0` and the zero localization ring. The
   private helper is a genuine intermediate result and no statement was split
   off. Verdict: pass.
4. Read the proof from the target downward. It uses the shortest available
   localization, pushout, base-change, and universal-homeomorphism lemmas; all
   three added imports are proof-only and necessary. No old import or proof
   dependency can be pruned. Verdict: pass.
5. Compared the implementation with the node's four proof steps and unit
   route. The node's statement, proof plan, and `proof_deps` remain accurate,
   and `sk-prop-sf-cbc` is preserved. Verdict: pass.

Changed only this report section; no Lean declarations, statements, nodes, or
imports were changed during second reading.
