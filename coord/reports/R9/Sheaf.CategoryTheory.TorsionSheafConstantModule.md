## What changed

In `Sheaf.CategoryTheory.TorsionSheafConstantModule`, proved the specification of the chosen
unique action, the converse annihilation assertion, and linearity of every additive sheaf
morphism. All existing signatures, universes, visibility, definitions and public imports stay
unchanged. The converse theorem moves before linearity because the new proof uses it.
A private, fully proved helper transports a normalized action by an additive automorphism;
uniqueness identifies it with the original action. The main proof applies this to the
square-zero shear on the module-sheaf biproduct and extracts the original map with its
inclusion and projection. No new import is needed: module transport,
finite module-sheaf limits and preadditive biproducts are already available through the
existing imports. Updated step 5 and proof origin
of the existing node to describe this route.

## Proved and sorry left

Closed 3 of the original 4 holes; added 0 holes and split off 0 statements.

- `CategoryTheory.torsionSheafModuleStructure_spec`: proved by the unique witness specification.
- `CategoryTheory.constantZModModuleSheaf_nsmul`: proved by mapping the zero residue of N
  through the ring sheafification unit and applying the scalar-action identity.
- `CategoryTheory.torsionSheaf_hom_linear`: proved from the original uniqueness theorem,
  the proved converse, and Mathlib finite limits/biproducts. Its private automorphism helper
  is fully proved and contains no sorry.

The sole remaining sorry is
`CategoryTheory.existsUnique_constantZModSheafModuleStructure`, node
`lem-pur-torsion-sheaf-constant-module`. Its original statement and complete proof docstring
are retained. Linearity and the chosen-action specification still depend on this original
hole; the converse annihilation proof does not. There are no new nodes or lower obligations.

## No longer needed

No original import, dependency node or module is pruned. The original sheafification and
ZMod ingredients remain needed for the open existence-and-uniqueness proof. The morphism
factorization clause of 03CY is no longer needed separately for the linearity proof:
uniqueness and finite biproduct algebra suffice. No experimental imports are retained.

## Where the brief, the DAG or earlier work was wrong

The direct Mathlib route in the existing plan has an interface gap at the generality of this
module. `PresheafOfModules.Sheafify.module` needs the ring unit locally injective and locally
surjective. The sole hypothesis `[HasSheafify J RingCat.{w}]` does not synthesize either
instance for the constant ring presheaf on arbitrary independent site/value universes.
Mathlib's small-etale-site proof in `Sheaf.Paper.SheavesKilledByNZmodModules` has additional
site instances, so it cannot simply be generalized by copying its construction. No extra
hypothesis was added and no claim of mathematical falsity is made. The remaining existence
proof needs to bridge this gap or use another construction. The completed linearity proof
avoids these local-bijectivity assumptions by using the existing uniqueness theorem.
The empty site and N=1 cause no exception in the three proofs: the arguments use only the
ring/module laws, uniqueness, and finite biproduct identities, without choosing sections
or points. No unit statement or unit proof step is bypassed.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
