## What changed

Proved `AlgebraicGeometry.Etale.finiteProjectivePullbackHom` in
`Sheaf.SixFunctors.EtaleFiniteProjectivePullbackHom` without changing either public signature
or the comparison definition. The proof uses the existing finite-projective dual pairing,
transports it along the strong monoidal constant-sheaf functor, and applies the existing
strong-monoidal internal-Hom comparison theorem. Naturality in the two variables and the
evaluation normalization follow from the defining comparison equations. Updated the node's
proof, proof dependencies and proof origin to record this shorter route.

Added proof-only imports of `Mathlib.CategoryTheory.Monoidal.Rigid.Braided`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`,
`WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal`, and
`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison`.
The three reused source-library results are already proved; no new mathematical lemma
or new node is needed. The unit record has no realized steps affected by this shortening.

Single-file compilation succeeded in 3.7 seconds. Temporary `#print axioms` checks for both
`finiteProjectivePullbackHomComparison` and `finiteProjectivePullbackHom` showed exactly
`propext`, `Classical.choice`, `Quot.sound`; the check commands were then removed.
The argument applies to zero modules, the zero ring, empty schemes and identity morphisms:
none of its pairing or strong-monoidal lemmas requires nontriviality or nonemptiness.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.Etale.finiteProjectivePullbackHom`
(node `lem-sf-etale-finite-projective-pullback-hom`): proved 1 of 1 original sorries.
Zero sorries remain in the item. Zero holes added; zero statements split off.

## No longer needed

Removed the following proof-only imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

Correspondingly removed these proof dependencies from the item's node:
`lem-pc-sheaf-modules-tensor-closed`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`, `def-pur-sheaf-hom`, and
`prop-weil-pbc-inverse-image-modules-exact`. The statement still mentions the notions
recorded by these nodes; its statement dependencies are unchanged. Their general
ringed-site module-sheaf interfaces are not used in this proof, which works directly
with the already established monoidal closed category of constant-coefficient sheaves.
The exactness theorem and an identification of pulled-back constants are unnecessary:
strong monoidality and the transported dual pairing suffice. No assertion is made that
these modules are unused by other items. No module withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's explicit finite-free and retract calculation is valid, but the library already
proves the equivalent dual-basis argument in `ModuleCat.isDualizable_of_projective`
and the monoidal comparison theorem in
`Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`; using them avoids rebuilding
that machinery. Existing signatures are preserved exactly. In particular, the original
Lean statement scopes the naturality-in-F and evaluation clauses inside the universal
quantifier over M-prime; the proof respects that scope and proves all clauses for every
M-prime and a. No definition or statement repair, forced adaptation, or new node.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
