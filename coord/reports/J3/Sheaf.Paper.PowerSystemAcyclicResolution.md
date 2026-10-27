## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_acyclic_resolution`
with its original signature. The proof constructs the resolution directly in abelian
towers: sheafified free abelian presheaves give epic torsion-free covers, the two-term
disk construction covers an arbitrary unbounded complex, and the kernel-cone map is
a quasi-isomorphism. Subobjects and finite biproducts preserve monicity of nonzero
integer multiplication.

The existing `powerSystem_ordinary_cokernel` theorem supplies a short exact sequence
on every complex with the required regularity. Its homology sequence, the existing
`PowerTransition.quasiIso_map`, and exact faithful forgetting show that ordinary
reduction preserves quasi-isomorphisms between these complexes. The existing
`Functor.leftDerived_from_resolvingClass` theorem then computes the universal
counit on them. Private, fully proved Kan-extension transport helpers carry the
homotopy universal pair to cochains; uniqueness compares its counit with the actual
supplied `Reduction.model.epsilon`. The section-map prescription proves faithfulness
of `Forget`; no faithfulness of derived forgetting is assumed.

The short-complex constructor and the homology-sequence argument are proved over
abstract categories before specialization. Profiling identified repeated kernel
checking of concrete sheaf-category structures in the original direct implementation;
these generic private helpers avoid that expansion without altering any shared API.

Only the assigned Lean module and its DAG node are changed. All new helpers are
private and proved. The public import and theorem statement are preserved. Proof
imports are ordinary-cokernel reduction, the resolving-class theorem, and the
Mathlib APIs for free abelian groups, short exact sequences, biproducts and Kan
extensions. The DAG records this route. The complete proof was checked by server `lcompile.py`.
Temporary profiler and trace options were removed from the final packet; the delivery
preflight supplies its final clean compile and declaration checks.

## Proved and sorry left

The original module contains one hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_acyclic_resolution`
(`lem-sfb-power-system-acyclic-resolution`). Its body has been replaced by the full
proof. No holes or split statements are added, and no `sorry` remains in the module.
The existing imported `powerSystem_ordinary_cokernel` is used as its stated theorem;
its independent proof remains an existing project obligation.

## No longer needed

No original import is removed: `Sheaf.Paper.TowerClassCoefficients` remains the public
statement import. The following former proof dependencies are not used by this proof:

- `lem-pc-kflat-resolution`, module
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `lem-pur-system-ringed-sequence-site`, module
  `Sheaf.CategoryTheory.SystemRingedSequenceSite`;
- `lem-cbc-constant-ring-module-sheaves`, module
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`;
- `lem-pur-derived-change-of-rings`, module
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.

The explicit free disk-cover/kernel-cone construction avoids the integer-module
and sequence-site equivalences. The short-exact quotient argument supplies the
resolving class directly, so no K-flat change-of-rings model comparison is needed.
These are removals from this node's proof route, not claims that the modules are
unused everywhere. No module is withdrawn. The unit's simultaneous derived
coefficient reduction route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is mathematically suitable but carries more transport than
this theorem needs. The existing ordinary-cokernel and resolving-class declarations
already permit a direct proof entirely in abelian towers. The general resolving-class
node `lem-pur-left-derived-from-kflat-class` is used as a tool: its statement applies
to arbitrary resolving classes, including the regular complexes constructed here.
The Mathlib leaf `lem-pc-cone-short-exact-quasi-iso` supplies the kernel-cone comparison.

The construction does not require boundedness, enough projective sheaves, invertibility
of l on the scheme, or nonemptiness of the site. It includes the empty scheme, zero
complex, l = 2, and level n = 0. Prime nonzeroness is used only for monicity of its
positive powers. All scalar and categorical statements retain their original meaning.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
