## What changed

Proved both original theorem bodies in
`Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`, keeping all existing signatures,
definitions, docstrings and public imports unchanged. All helpers are private and proved.

The action construction first proves N-torsion of the actual abelian inverse image using
additivity of the left adjoint. It then restricts the canonical constant Z/N action along
the invertible coefficient comparison. Ring maps preserve integer constants, so the
existing torsion-sheaf uniqueness and morphism-linearity declarations prove both unit
normalization and uniqueness. The same scalar transport proves comparison semilinearity.
The transition and isomorphism clauses use explicit section calculations, adjunction
naturality, the tower constructor and the comma-normalized inverse-image identification.
No invertibility of N on the scheme is assumed. N=1 and empty objects are included;
the private isomorphism calculation also works at N=0.

## Proved and sorry left

Original holes: 2. Closed: 2. Added: 0. Split off: 0. Remaining holes in delivery: 0.

- `AlgebraicGeometry.Scheme.existsUnique_proEtaleRootsOfUnityInverseImageAction`
  (node `lem-pur-roots-of-unity-inverse-image-iso`): proved from existing declarations.
- `AlgebraicGeometry.Scheme.proEtaleRootsOfUnityInverseImageIso`
  (same node): all four conjunction components proved from existing declarations.

These proofs use existing theorem dependencies that may themselves have sorry;
no claim is made that the transitive dependency closure is sorry-free.
The earlier sandbox's new scalar-action hole was proved and incorporated as a private
helper. Its unsubmitted module and node were removed from the sandbox.

## No longer needed

Removed redundant direct proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf`,
`Sheaf.CategoryTheory.TorsionSheafConstantModule`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Mathlib.CategoryTheory.Sites.Sheafification`.
The required declarations remain available through the retained public root-sheaf APIs.
Added proof import `Mathlib.CategoryTheory.Adjunction.Additive` for inverse-image additivity.
Retained proof import `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, which is used.

Removed direct proof import
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`: the original public
`Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage` API already supplies the
comma-normalized identification at the coefficient universe used here. Its arbitrary
larger-coefficient-universe extension is unnecessary for this argument. The isomorphism
node remains needed through those original declarations.

Removed proof dependency `def-weil-sheaf-of-modules-category`: the argument uses families
of module structures and the existing torsion action API, without constructing a separate
module-sheaf category. Other declared dependencies remain needed. No existing module
is withdrawn; redundant direct imports are not claimed as globally pruned modules.

## Where the brief, the DAG or earlier work was wrong

The retained attempt unnecessarily left scalar compatibility as a new hole. Integer-cast
normalization is automatic for an action restricted along a ring morphism, and the existing
constant Z/N module uniqueness and linearity declarations finish the argument. The actual
inverse-image action can likewise be constructed without comparing a separate small-model
module inverse image: N-torsion follows by additivity of the actual left adjoint.
No mathematical statement or definition repair was needed. The unit has no realized proof
steps, and its route is unchanged. No target signature changed.

Fresh clean compilation through lcompile.py completed in 11.0 seconds without warnings
on 2026-10-19 at 09:05 after resuming the interrupted session. The fresh retry checked the
retained proof against the current published server build.
A separate signature check confirmed that all five existing signatures, all three definition
bodies and all existing docstrings are unchanged. The private module-action constructor has
the instance_reducible attribute. Delivery preflight is recorded by the delivery tool.
Some intermediate compile calls received no server answer; no tool or limit was modified.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
