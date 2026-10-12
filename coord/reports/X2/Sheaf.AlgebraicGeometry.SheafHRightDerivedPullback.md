## What changed

Repair of return X-8d288: removed the duplicate private theorem
`AlgebraicGeometry.exists_resolution_comparison` from the item's module.
A proof-only `import all Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux`
makes the existing private `AlgebraicGeometry.Etale.exists_resolution_comparison`
callable. The target proof applies that existing theorem with the same arguments.
No module outside this delivery is adapted; no signature or visibility changes.
The item's node now records the module's degree-zero factor node as the dependency
containing the reused helper. The localization lemma remains a transitive dependency.

The delivery tool reconstructs the commit on fetched `origin/sheaf-dag`;
compilation uses the local compiled-library mirror and the delivery axiom probes.

The sole original `sorry` is replaced by a complete Lean composition proof using
the existing resolution comparison and two smaller resolution map computations.
The original signature is unchanged.

Added `SheafHExtResolutionSectionsIso`, a fully constructed Ext-to-resolution-sections
isomorphism: Ext/resolution equivalence, the homology-class identification, and evaluation
at 1 from the constant integer sheaf. This reuses the already proved private construction
in `EtaleSheafHExtDerivedComparison`; it exposes a new explicit construction in a separate
namespace because the public existence theorem does not specify the comparison needed
for the resolution formulas. No data are chosen from a holed existence theorem.

Added `ExtPullbackResolutionSections` and `ClassicalPullbackResolutionSections`, one named
intermediate theorem per module. Each computes only one side of the comparison, with a
supplied compatible resolution lift. The original theorem proves the lift exists and
combines the two computations by composition and cancellation of isomorphisms.

Validated all four modules in import order with `lcompile.py --all`, and the delivery dry
run with the maintainer's axiom probes. The target's dependencies still contain the two
new named holes; this is a decomposition, not an axiom-free proof of the mathematical result.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.sheafHRightDerivedIso_pullback`
(node `lem-weil-pbc-sheafH-right-derived-pullback`). No `sorry` remains in the item's module.
The duplicate private helper is removed; the proof uses the existing fully proved
`AlgebraicGeometry.Etale.exists_resolution_comparison`.

Holes added (two):
- `AlgebraicGeometry.extPullback_resolution_sections`
  (`lem-weil-pbc-ext-pullback-resolution-sections`). This compares Ext pullback with an
  explicitly supplied sections-complex map; it contains no classical derived map.
- `AlgebraicGeometry.classicalPullback_resolution_sections`
  (`lem-weil-pbc-classical-pullback-resolution-sections`). This computes classical base
  change on resolutions; it contains no Ext pullback or Ext/classical isomorphism.

The explicit comparison definition module has no holes. Both remaining statements have
full source-based proofs in their docstrings and matching DAG nodes. Net holes: one closed,
two added, a decomposition. Degree zero has the same resolution identity, and no hypothesis
on torsion, dimension, nonemptiness, preservation of injectives by inverse image, or
acyclicity of the pulled-back resolution is introduced.

## No longer needed

Removed the duplicate `AlgebraicGeometry.exists_resolution_comparison` theorem.
Removed the direct `Mathlib.Algebra.Homology.DerivedCategory.KInjective` import;
the reused helper's module supplies that interface transitively. Added the proof-only
`import all` of `EtaleCohomologyPullbackDegreeZeroAux`. This imports a fully proved
module and adds no hole. The K-injective localization node is now a transitive rather
than a direct proof dependency. No additional globally pruned module is claimed.

Removed the duplicated helper `SheafPullbackResolution.sectionsEquiv_naturality`;
Mathlib's adjunction naturality theorem supplies that proof directly within
`complexSectionsIso`. No additional import or node is needed for this repair.

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`:
  its public theorem `Scheme.nonempty_sheafH_extDerivedIso` is insufficiently explicit for
  this computation. Node `lem-weil-pbc-sheafH-ext-derived-comparison` is no longer a proof
  dependency of the item; its existing proved construction was reused explicitly.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`:
  Mathlib/source-library exactness instances suffice. Its theorem
  `Etale.upperStar_abelian_exact` is not applied. The mathematical node
  `prop-weil-pbc-inverse-image-exact` remains recorded because the exactness instances are
  needed for the quasi-isomorphism of the pulled-back augmentation and for the intermediate
  arguments. The wrapper module is not needed on this route.

The old direct proof dependencies `def-weil-pbc-cohomology-pullback` and
`lem-weil-pbc-ext-via-injective-resolution` also leave the item's `proof_deps`:
they are used by the new Ext computation and explicit comparison, respectively,
rather than directly by the composition proof. They remain transitive dependencies,
so neither is claimed as a globally pruned node.

Second reading also removed two unused imports from new modules:
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
  from `ExtPullbackResolutionSections` (the Ext computation does not mention it).
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
  from `SheafHExtResolutionSectionsIso` (the construction only uses Ext/resolution
  and evaluation, not classical right-derived sections).

No other original proof imports were removed. `lem-weil-pbc-ext-via-injective-resolution`
and `lem-weil-pbc-kinjective-hom-derived` remain used through their Mathlib matches. Both
original public imports remain because the statement needs their interfaces. New proof
imports are the three resolution modules and the existing degree-zero auxiliary module.
The unit's statement and realized steps are unchanged. This report makes no claim that
these two removed modules are unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The returned version duplicated an existing resolution comparison theorem. Its
private visibility is handled by Lean's `import all`; importing it this way compiles
and avoids both duplication and any interface adaptation. The earlier report's
assumption that private helpers cannot be called from an importer was too strong.
The current repair changes the proof rather than repeating the returned delivery.

The first delivery repeated a private naturality helper already stated in
`EtaleSheafHExtDerivedComparison`. The landing check correctly rejected that duplicate.
Its visibility prevents importing it by name; using Mathlib's underlying general
adjunction theorem directly removes the duplicate without adapting another group's file.

The plan's injective-resolution comparison and Ext/resolution ingredients exist in Mathlib,
but neither stated dependency supplies the needed pullback/resolution formula. The public
Ext comparison is an existence theorem about a natural isomorphism on a single scheme;
it supplies no compatibility between schemes. A proof cannot use its private construction
as if that were its public statement. The delivery supplies an explicit construction and
splits the two missing map computations.

An initial compiler experiment confirmed that the public Ext comparison lands in unbounded
derived cohomology rather than directly in classical right-derived sections. The final
proof uses the explicit resolution homology objects instead, avoiding arbitrary choices
of comparison isomorphisms.

## New nodes

`def-weil-pbc-ext-resolution-sections-iso` records the explicitly constructed comparison
in `Sheaf.AlgebraicGeometry.SheafHExtResolutionSectionsIso`; it introduces no hole. Its
construction is the existing Ext/resolution equivalence followed by the chain isomorphism
induced by evaluation at 1, not a witness of mere existence.

`lem-weil-pbc-ext-pullback-resolution-sections` records Ext pullback computed on the chosen
resolution sections, in `Sheaf.AlgebraicGeometry.ExtPullbackResolutionSections`. It is the
Ext half of the original node's second step; its lift is supplied, not asserted to exist.

`lem-weil-pbc-classical-pullback-resolution-sections` records classical right-derived base
change computed on the chosen resolution sections, in
`Sheaf.AlgebraicGeometry.ClassicalPullbackResolutionSections`. It is independent of the Ext
half. The two identities combine in the original module by a proved cancellation argument.

No existing definitions or statements were changed and no change records are needed.

## Second reading by X2

1. **Visible interface: PASS.** Diffed the original module against the repository.
   The existing `sheafHRightDerivedIso_pullback` signature is byte-for-byte identical;
   its visibility and both public imports are unchanged. All other delivered modules
   are new. No existing definition, target statement, or other group's module changes.
2. **Proof and axioms: PASS as a decomposition.** All four modules compile locally in
   dependency order, without warnings or errors. A separate scratch module printed
   the axioms of the original theorem, both open computations, all five construction
   declarations, and the reused resolution-comparison helper. The constructions and
   helper use only `propext`, `Classical.choice`, and `Quot.sound`; the three theorems
   additionally use `sorryAx`, as expected from the two named open computations.
   The only delivered holes are the complete proofs of
   `extPullback_resolution_sections` and `classicalPullback_resolution_sections`.
   No forbidden declarations, holed definitions, or arbitrary existence-witness data.
3. **Split statements: PASS.** Read both signatures, their docstring arguments, and
   nodes. The Ext identity contains no classical derived comparison, and the classical
   identity contains no Ext map, so each is strictly a part of the original argument.
   Checked degree zero (no incoming boundaries), zero sheaves and empty schemes
   (zero groups), and identity pullback (resolution comparison induces the identity).
   No inverse image preserving injectives or pulled-back resolution being acyclic is
   assumed. The supplied augmentation homotopy determines the localized map; the
   K-injective target and additive functors make the induced homology map independent
   of the lift. Checked Stacks Tags 01F8, 01F9, 01FA, 06XR and 08J6 and the actual
   `cohomologyMap` definition (exact inverse image followed by constant-sheaf comparison).
   Repeated searches using `leanfinder`, `loogle`, `grep`, and repository `rg` with
   different terms. Mathlib's `rightDerived_app_eq` and resolution naturality concern
   the same source category; they do not directly compute this cross-scheme base change.
   The resolution comparison is reused via `import all`, not duplicated. The explicit
   comparison duplicates no public construction; existing private definitions cannot
   occur in the exposed body of a public definition under this project's contract.
   Neither remaining hole has a short direct proof from the inspected candidates.
4. **Route and pruning: PASS.** Followed the lift, the two map identities, and the
   cancellation proof from the original theorem downward. Reviewed the import needs
   of all four modules. Public imports support their signatures or explicit definition
   bodies; proof-only imports remain plain, including `import all` for the helper.
   Every old direct proof dependency removed from the item's node is covered in
   `No longer needed`: Ext pullback and Ext/resolution move to the smaller nodes;
   K-injective comparison moves behind the reused helper; the old existential
   Ext/classical comparison is replaced by the explicit construction. Exactness stays.
   Read `dag/units/sk-thm-p1.json`: its statement and realized steps are unchanged;
   this reduction is below that route. No globally unreachable module is claimed.
5. **DAG agreement: PASS.** Checked all four nodes against the Lean declarations,
   the union of step uses against `proof_deps`, the source, creation/blueprint fields,
   and `proof_origin`. The original node records the helper's containing node and the
   two computations; the new definition has explicit data and no postponed proof.

Second-reading changes: corrected the report's obsolete server-compilation claim,
recorded independent searches in the new nodes, and appended this review. No Lean
repair was needed. One original hole is closed and two are added: net minus one,
a decomposition rather than an axiom-free proof. No additional hole was closed.
