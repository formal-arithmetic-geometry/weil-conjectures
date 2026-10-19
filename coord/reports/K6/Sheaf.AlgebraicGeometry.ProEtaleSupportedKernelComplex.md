## What changed

Proved all five original holes of
Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex. Kernel inclusions and
monomorphism cancellation prove the four kernel functor laws. The main theorem
uses kernel preservation to prove open vanishing of the kernels, constructs the
natural closed-unit isomorphism, applies NatIso.mapHomologicalComplex, and
transports the degreewise kernel short exact sequences along its components.
Mathlib's degreewise criterion proves short exactness in the complex category.

Completed the retained helper module
Sheaf.AlgebraicGeometry.ProEtaleSupportedModuleUnits without sorry. Applying
finiteScalarUnitComparison to the identity coefficient homomorphism gives the
unit-compatible abelian forgetful comparison. The existing abelian_closed_support
then proves supported module-unit invertibility. Adjunction uniqueness transfers
this to the actual finiteModuleAdjunction. The proved source vanishing on disjoint
ranges gives zero open restriction of closed direct images. Full faithfulness of
abelian open direct image and the adjunction triangle identities give the module
counit invertibility and hence invertibility of the restricted actual open unit.
All auxiliary categorical helpers are private and proved.

Final lcompile.py --all passed cleanly: 17.6 seconds for the module-unit
module and 7.6 seconds for the kernel-complex module.

No existing signature, definition, or public import changed. The commutative
criterion remains a hypothesis of the original theorem unchanged. No target or
blueprint unit step changed. DAG proof records now follow the implemented route.

## Proved and sorry left

Five original holes closed:
- AlgebraicGeometry.ProEtale.finiteSupportedKernelMap_id.
- AlgebraicGeometry.ProEtale.finiteSupportedKernelMap_comp.
- AlgebraicGeometry.ProEtale.finiteSupportedKernel_additive.
- AlgebraicGeometry.ProEtale.finiteSupportedKernelInclusion_naturality.
- AlgebraicGeometry.ProEtale.finiteSupportedKernelComplex_shortExact.

The new helper AlgebraicGeometry.ProEtale.finiteSupportedModuleUnits
(node lem-exc-proetale-finite-supported-module-units) is also proved.
Zero holes added; zero sorry declarations remain in either delivered module.
The proof uses existing library declarations as intended by stage 3; their own
axiom and sorry closure is not claimed to be closed by this delivery.

## No longer needed

Removed direct proof imports from the item:
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: no direct use in the
  kernel or complex calculation; module infrastructure is already reexported.
- Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation: its commutative open-unit
  calculation is replaced by full faithfulness of abelian open direct image and
  the unit-preserving comparison for arbitrary finite coefficients.
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact: retained transitively through
  ProEtaleFiniteModuleAdjunction and still used for kernel preservation.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison: imported by the
  new proved helper module, so the item's direct import is unnecessary.
- Sheaf.CategoryTheory.RingedSiteModules: already exported by the retained
  ProEtaleClosedEssentialImage import; no direct use in this proof.

The proof does not use lem-pur-proetale-open-unit-evaluation, the coefficient
transfer through Z/n, def-pc-sheaf-restrict-scalars as a separate geometric input,
or the commutative presentation comparison of
prop-weil-pbc-proetale-constant-ring-map. The unit-preserving comparison with
abelian sheaves gives a shorter route, including for noncommutative A. These
nodes may remain necessary elsewhere; no global withdrawal is claimed.
The assumed lem-exc-proetale-closed-essential-image is retained in the original
statement but its commutative criterion is not used: the existing abelian support
result supplies the required unit invertibility directly. Its public import
remains necessary to express the unchanged hypothesis. Removed the obsolete
closed-essential-image and open-unit-evaluation tool_uses approvals from the
item's node; retained the constant-exact approval used in the kernel proof.

No whole module is withdrawn, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report described one unresolved geometric split. That split is now
proved using the existing abelian support declaration and the full comparison
already supplied by finiteScalarUnitComparison; no additional coefficient
presentation theorem is needed. The prior proof spent its heartbeat budget on
large concrete categorical cancellation terms. Proving the cancellation and
adjunction-uniqueness argument once for abstract categories avoids that unfolding
without changing library definitions or increasing limits.

The existing lem-weil-pbc-proetale-abelian-closed-support is used as a tool
from another unit: it supplies exactly the underlying abelian supported-unit
assertion needed by the comparison. The current unit has no separate
noncommutative module support declaration other than the item; its commutative
criterion would require unnecessary coefficient-presentation transport. The
maintainer may record the cross-unit tool approval.

The new theorem is valid for the zero ring, empty schemes, and noncommutative
finite rings: forgetting module structure reflects isomorphisms, and no division,
commutativity, or nonzero element is used. Complementary ranges give empty base
changes in all cases. No arbitrary object is chosen from an unproved existence
statement. No mathematical statement is disputed or weakened.

## New nodes

lem-exc-proetale-finite-supported-module-units: the now-proved individual-module
input used before kernel and complex formation. Its module is
Sheaf.AlgebraicGeometry.ProEtaleSupportedModuleUnits and its declaration is
AlgebraicGeometry.ProEtale.finiteSupportedModuleUnits. It records the source,
complete argument, searches, Lean statement, and inherited chapter/unit. Its
proof dependencies now include the existing abelian closed-support theorem and
the unit-compatible scalar comparison. No new sorry is introduced. No change
record is required because all existing signatures, definitions, and public
imports are unchanged.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
