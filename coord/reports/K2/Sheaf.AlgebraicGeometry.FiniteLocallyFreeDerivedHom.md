## What changed

Proved `AlgebraicGeometry.finiteLocallyFree_derivedInternalHom_single` without changing its
signature or existing docstring. Its exactness argument uses the original
`dual_tensor_hom_iso` and `finiteLocallyFree_tensorLeft_exact`, together with the existing
`Scheme.Modules.IsFiniteLocallyFree.dual`. A natural isomorphism transports both preservation
properties to sheaf Hom. The K-injective representative comparison, exact-functor preservation
of quasi-isomorphisms, and the single-complex comparison then give the derived isomorphism.
Positive cohomology vanishes by Mathlib's derived single-object `IsLE 0` instance and transport
through this isomorphism.

Added `Sheaf.AlgebraicGeometry.HomComplexSingle`, proving
`AlgebraicGeometry.sheafHomFunctor_additive` and `AlgebraicGeometry.homComplex_single_iso`.
The latter explicitly constructs the sole-surviving-factor product isomorphism from the
specification of `homComplex_exists`, checks the differential formula, and supplies the complex isomorphism.
The private product helper `soleFactorIso` is completely proved. No local freeness, exactness,
or boundedness assumptions occur in this comparison. It is a reusable construction, not a
renaming of the original derived theorem.

The item's proof adds non-public imports of the new module and
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`. The second reading removed redundant
direct imports of `WeilConjectures.AlgebraicGeometry.Modules.Dual` and
`Mathlib.Algebra.Homology.QuasiIso`: the retained imports already expose their declarations.
Updated the item's proof steps and dependencies to describe the actual argument.

## Proved and sorry left

Proved the item's sole sorry:
`AlgebraicGeometry.finiteLocallyFree_derivedInternalHom_single`
(node `lem-sc-finite-locally-free-derived-hom`).

Also proved `AlgebraicGeometry.homComplex_single_iso` and the additive instance
`AlgebraicGeometry.sheafHomFunctor_additive` in the new module
(node `lem-sc-hom-complex-single`). No sorry remains in either delivered module, and no
new postponed theorem is introduced. The proof intentionally uses the existing stated
`dual_tensor_hom_iso`, `finiteLocallyFree_tensorLeft_exact`, `homComplex_exists`, and
`derivedInternalHom_obj_iso`; proving these dependencies is subsequent stage-3 work.

The sandbox modules compile in import order through `lcompile.py`. The delivery dry run is the final validation. Small cases checked in the argument: rank zero, zero coefficient sheaf,
empty scheme, and unbounded coefficient complexes. The product comparison only uses one
surviving factor, so it does not assume exactness of arbitrary products.

## No longer needed

Removed the item's redundant direct proof import of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`. Its definitions remain needed
and available through the retained public imports and the comparison module. The second reading also removed redundant direct imports of
`WeilConjectures.AlgebraicGeometry.Modules.Dual` and `Mathlib.Algebra.Homology.QuasiIso`
from the item, and `Mathlib.Algebra.Homology.Additive` from the new comparison module.
Their declarations remain available through retained imports. No node or module is claimed
pruned from the targets' closure.

All original mathematical dependencies, including evaluation and finite locally free tensor
exactness, remain needed. No unit statement or realized proof step is bypassed. The truncation
construction in the old plan is unnecessary: the explicit quasi-isomorphism followed by the
Mathlib single-complex comparison already constructs the required derived isomorphism.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no statement or definition was changed. The old plan called
the entire passage from the Hom-complex product to exact-functor cohomology elementary, but
its Lean interface supplied no single-source comparison. The new node supplies that
construction with a complete proof. The remaining exact-functor and single-object steps use
existing Mathlib declarations.

LeanSearch was attempted and returned an unavailable-service error; no verdict was inferred
from that failure. LeanFinder, Loogle, Mathlib/source grep, and blueprint-node searches found
no existing internal sheaf-valued single-source comparison. The relevant Stacks sections were
read from the available local Stacks checkout: sites-cohomology Section 0A8X and cohomology
Lemma 20.50.5 / Tag 08DQ.

## New nodes

`lem-sc-hom-complex-single`, at
`dag/nodes/sec-picard-framework/lem-sc-hom-complex-single.json`, records the isomorphism of complexes
from internal Hom out of a sheaf in degree zero to degreewise ordinary internal sheaf Hom.
It uses only `def-pur-hom-complex` and `def-pur-sheaf-hom`, inherits the item's chapter and unit,
and records the source product and differential formulas together with the performed
searches. Its Lean realization is `Sheaf.AlgebraicGeometry.HomComplexSingle`. Both its main
theorem and its additive instance are proved. No change record is needed: no existing public
interface changed.

## Second reading by K2

1. Compared the complete item module with the repository version using `diff`. The only
   changes are proof imports and the original theorem's proof body: its signature and
   existing docstring are byte for byte unchanged. There is no definition or statement
   change and no change record is required. The sole additional module introduces a
   proved comparison theorem and an additive instance. Verdict: pass.
2. Compiled both delivered modules in import order using `lcompile.py`, cleanly, including
   after import cleanup. Neither module contains `sorry` or a forbidden declaration.
   Scratch copies print axioms for the original theorem, the new comparison and additive
   instance; upstream `sorryAx` is expected only through the explicitly retained open
   dependencies. The delivery tool also probes all declarations. Verdict: pass.
3. No postponed statement was split off. Read the new theorem and its product helper
   against Stacks sites-cohomology `section-hom-complexes` (Tag 0A8X), product and
   differential formulas, in the local Stacks checkout. In degree n, nonzero source
   indices give zero factors; the product projection at zero is an isomorphism by its
   universal property, and the source differential vanishes. Checked arbitrary P,
   P=0, coefficient term zero, the empty scheme, and unbounded K: none needs finite
   rank or exactness of infinite products. Repeated LeanFinder with a differently
   phrased single-source internal-Hom query, Loogle for sheaf Hom (unknown identifier,
   no conclusion inferred), and grep in Mathlib, both library roots and slopmaster2.
   Only group-valued Hom-complex computations and the already-used degreewise single
   comparison were found. The new theorem is strictly a complex-level intermediate,
   has no local-freeness hypothesis or derived conclusion, and is fully proved.
   Verdict: pass.
4. Read the original proof plan, actual dependency statements, and unit record
   `dag/units/sk-thm-picard-duality.json`. The proof retains both evaluation and tensor
   exactness, transports exactness to Hom, applies it to the K-injective resolution,
   and uses the proved single-source comparison; the final IsLE argument proves the
   positive-degree clause through the constructed isomorphism. This is the original
   exactness route below the unit level. No realized unit step is bypassed and no old
   proof dependency is unused. Removed three redundant imports listed above; retained
   public imports supply names used in signatures, and newly needed proof imports are
   plain imports. Verdict: pass.
5. Compared the old and delivered node JSON. Only `proof`, `proof_deps`, and
   `proof_origin` change on the existing node, describing the actual Lean argument.
   The new node's dependencies are the product/differential specification and sheaf
   Hom, exactly what the comparison uses; its chapter, unit, source, blueprint,
   searches and Lean record are present. No new node restates the original target.
   Verdict: pass.

Changed only the three redundant imports and this report; the proofs were retained.
