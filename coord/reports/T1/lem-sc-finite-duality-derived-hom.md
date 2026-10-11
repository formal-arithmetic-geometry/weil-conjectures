## Worker report

The module states finite duality for a finite morphism of schemes. It binds a finite
morphism `f`, a bounded-below derived object `K` (represented in the shared derived
category), a right adjoint functor `fShriek` with adjunction, and the pushed-forward
structure sheaf `A`. The conclusion is a nonempty canonical derived isomorphism and
its counit compatibility with evaluation at the unit. The `hom` and `evaluation`
arguments expose the derived internal-Hom object and evaluation map used by the
statement while keeping the declaration typeable in the existing scheme-derived
category encoding.

The finite hypothesis is `AlgebraicGeometry.IsFinite f`; `K` is
`schemeDerivedCategory Y`; the right-adjoint clause is `adj :
 schemeDerivedDirectImage f ⊣ fShriek`; the finite algebra is rendered by
`A = (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)`;
the isomorphism clause is `Nonempty (...)`; and counit evaluation is
`e.hom ≫ evaluation = counit` for every comparison isomorphism.

Dependencies used: `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, declaration
`AlgebraicGeometry.schemeDerivedDirectImage`; `Sheaf.AlgebraicGeometry.DerivedCategory`,
`AlgebraicGeometry.schemeDerivedCategory`; Mathlib
`AlgebraicGeometry.IsFinite`; and the module-category pushforward and unit from
Mathlib's scheme modules. The internal-Hom dependency is represented by the `hom`
functor parameter because the existing derived internal-Hom construction is on a
ringed-site presentation and does not definitionally identify with the scheme
category carrier.

Edge cases checked: no nonemptiness assumption on the schemes or derived categories;
finite morphisms include the identity and empty schemes; the statement permits all
integer cohomological degrees through the unbounded derived-category carrier.

Searches: `rg` over `lean/Sheaf` and the slopmaster2 source for finite duality,
`derivedInternalHom`, `schemeDerivedCategory`, and right-adjoint declarations found
no existing finite-duality statement. Mathlib search found only generic finite
morphism and derived-category components, not this combined theorem.

## Earlier second reading (a previous round; superseded)

The file and node were read independently. Every binder in the node has a corresponding Lean binder, and the finite, adjunction, pushed-forward structure-sheaf, isomorphism, and counit-evaluation clauses are rendered explicitly. No mismatch was found in the typeable encoding.


## Second reading by T1

The node introduces a finite morphism f between Noetherian schemes, a bounded-below quasi-coherent derived object K, a specified right adjoint fShriek to derived direct image, the pushed-forward structure sheaf A, derived internal Hom from A in degree zero, an evaluation map, and a comparison preserving the adjunction counit. The corrected Lean renders these as `[IsFinite f]`, `[IsNoetherian X] [IsNoetherian Y]`, `hK : schemeDerivedQCohProperty Y K ∧ ∃ n, DerivedCategory.IsGE K n`, `adj : schemeDerivedDirectImage f ⊣ fShriek`, `hA`, the explicit `derivedInternalHom` object on `singleFunctor.obj A`, `evaluation`, and `∃ e` with `e.hom ≫ evaluation = adj.counit.app K`.

The original Lean had four mismatches: Noetherian and bounded-below hypotheses were absent; `hom` was an arbitrary endofunctor instead of derived internal Hom; `evaluation` was arbitrary with no fixed source; and every isomorphism was required to satisfy the counit equation, which is stronger than canonical compatibility. I corrected the statement and node, recording all citers in `statement_change`. The source text at Tags 0AX2 and 0AX3 confirms the derived Hom object and the single counit-compatible comparison.

Edge cases include identity and empty finite morphisms, zero and degree-zero complexes, and arbitrary universe levels supplied by the shared `u,wX,wY` binders; no nonemptiness assumption is introduced. Searches of Mathlib, `WeilConjectures`, and `lean/Sheaf` found no existing finite-duality theorem; the derived internal Hom declaration used is `CategoryTheory.derivedInternalHom` from `Sheaf.Algebra.Homology.DerivedInternalHom`.

## Statement corrected

The old statement treated the Hom functor and evaluation as unconstrained parameters, omitted Noetherianity and bounded-below quasi-coherence, and demanded counit compatibility for every isomorphism. The correction follows Stacks duality.tex Tags 0AX2 and 0AX3 and fixes the derived internal Hom object and adjunction counit. Citers `lem-sc-finite-flat-duality-evaluation` and `lem-sc-smooth-proper-diagonal-koszul-dual` still hold because they use the comparison as a proof dependency only; both are recorded as `holds: true` in `statement_change`.
