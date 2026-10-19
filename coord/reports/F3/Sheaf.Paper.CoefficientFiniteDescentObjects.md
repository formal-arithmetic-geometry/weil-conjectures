## What changed

Proved `AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects` with its
signature, universes, visibility, public imports and existing documentation unchanged.
The private helpers `free_hasConstantModel` and `constantModel_eq_of_localFree` prove
that the paper's finite constant local models and the source library's constructibility
predicates agree over the two rational coefficient rings on Noetherian schemes.
The first helper uses an explicit free-cover hypothesis and needs no additional lisse
predicate import. These are the same finite-free comparison calculations already used
in `FiniteCoefficientDescentTwoColimit`, which imports this item and therefore cannot
be imported here. They introduce no new notion or unproved result.

After this comparison, reuse the existing same-unit theorem
`constructibleCocone_essSurjObj` and map its model isomorphism into the ambient derived
category. Persistence uses `boundedConstructible_derivedExtendScalarsSubfield_obj`
and `derivedExtendScalarsCompIso`. The proof handles arbitrary finite enlargements;
the input model is not reconstructed. Added proof imports of
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` (with `all` for its proved private
transport/local-triviality helpers) and `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
Updated the item's node proof, proof dependencies and proof origin to this shorter route.
No definitions or existing statements changed; no consumer adaptations are necessary.
The preflight-required change record is
`coord/changes/coefficient-finite-descent-objects-proof-commands.md`. It documents the
additional proof namespace openings and lists all 335 unchanged downstream consumers;
the only outside textual user is `FiniteCoefficientDescentTwoColimit`.

Validation: `lcompile.py` compiled the completed module, then compiled it again after
removing the trial imports of `Sheaf.CategoryTheory.SheafTensor` and
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; both compiles were clean. After
resumption the completed module compiled cleanly again. The first resumed dry run
requested a change record for the proof namespace openings; the record has been added.
A subsequent direct compile took 12.3 seconds, while delivery's appended axiom scan
exceeded the limit. Diagnostics verified the source descent and local-triviality
lemmas use only the three permitted axioms, and the completed theorem's axiom scan
also succeeded (its transitive dependencies still include their recorded holes).
Replaced the rewrite that generated `IsConstantModelConstructible.eq_1` by an explicit
`if_pos` equality, avoiding that unnecessary generated declaration and its repeated
axiom traversal in the delivery probe.
All new helpers are complete proofs. Import-direction checks found no cycle, and a
source DAG traversal found that every newly used descent/comparison node does not
reach the item. The unchanged proof also covers empty schemes and strata, zero rank,
the zero complex, the base coefficient field, and enlargement E = F.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`
(node `det-lem-coefficient-finite-descent-objects`), including both conjuncts.
Proved both private helpers. Holes closed: 1; holes added: 0; split off: 0.
There are zero `sorry`s left in the delivered Lean module and no new Lean modules.
Existing dependency theorems retain their own proof status; this delivery makes no
claim of eliminating their transitive holes.

## No longer needed

Removed these direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CoefficientFiniteDescentHom`
- `Sheaf.Paper.CoefficientFiniteDescentLisse`
- `Sheaf.Paper.CoefficientHeartGeneration`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.SixFunctors.ScalarSixPullback`

The local proof no longer separately invokes the following planned nodes:

- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-sfb-subfield-flat`
- `lem-sfb-qlbar-flat`
- `det-cor-coefficient-heart-ii-triangulated`
- `def-weil-finite-subextension-directed-set`
- `sk-def-sfb-change-of-scalars`
- `sk-def-sfb-derived-categories`
- `det-lem-coefficient-finite-descent-hom`
- `def-weil-triangulated-category`
- `lem-sf-triangle-morphism-iso`
- `det-lem-coefficient-finite-descent-lisse`
- `det-cor-coefficient-heart-ii-generation`
- `det-prop-scalar-six-pullback`

Their separate cone/shift/generator argument is replaced by the existing same-unit
`lem-sfb-constructible-cocone-obj` implementation, whose statement supplies precisely
the source bounded-constructible model. This does not remove any unit statement or
unit proof step. Some of the listed results remain transitive dependencies or are
needed by other modules; these are local dependency removals, not a claim that all
are globally unreachable. Removed the obsolete top-level tool-use entry
`det-prop-scalar-six-pullback`, which this argument does not invoke.
The four original public imports remain unchanged. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's five-step direct proof was a valid plan, but the source library already
proves object descent for its constructibility convention. What remained was the
comparison with the paper's finite constant local models, not another independent
proof of cone descent. Finite-field and algebraic-closure local triviality on
Noetherian strata supply that comparison; no implication for arbitrary condensed
coefficient rings or arbitrary non-Noetherian schemes is asserted.

The interrupted compile log named an unimported `IsLisseCoefficientModule`; replacing
that private helper hypothesis by its explicit free-cover statement resolved the error
without adding a lisse-heart import. There was no pending delivery mutation to repeat.
The existing declarations and source statements are not disputed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
