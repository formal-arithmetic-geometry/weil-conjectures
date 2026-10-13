## What changed

Repaired the returned delivery of
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore` by removing all four
duplicate private helpers: `Scheme.Modules.hom_zero_of_affine`,
`Scheme.Modules.subobject_le_of_affine_range`, `Scheme.Modules.power_mono`, and
`Scheme.Modules.power_subobject` (all in namespace `AlgebraicGeometry`).

Added proof-only `import all Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`.
The private quotient comparison now uses that module's existing `power_mono` and
`power_subobject` directly. The two affine helpers are no longer needed locally;
the existing power-subobject proof uses their originals in
`ClosedImmersionIdealPowerImage`. No existing library module is adapted.

The remaining private helpers `tensor_unit_factor` and `power_quotient_iso` are fully
proved. They combine the kernel calculation, closed-immersion unit quotient and
unit-compatible conjugate-adjunction comparison to prove
`AlgebraicGeometry.formalFunctionsFinite_sheaf_quotient_iso` for arbitrary F.
All existing signatures, visibility, public imports, definitions and docstrings stay
unchanged. The isomorphism node's proof and proof dependencies now record the reused
power lemmas. The closedness node's earlier repaired route stays unchanged.

The repaired module compiles with lcompile.py without warnings. Import-direction check
permits the new dependency. No new modules or nodes were created.

## Proved and sorry left

Closed one baseline hole:
`AlgebraicGeometry.formalFunctionsFinite_sheaf_quotient_iso`
(node `lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso`).
No holes added or split off. No sorry remains in the item's module.
`AlgebraicGeometry.formalFunctionsFiniteι_isClosedImmersion` was already proved on the
current baseline and its proof is preserved unchanged. Thus this delivery proves one
of one baseline sorries, using existing library results.

## No longer needed

Removed the returned delivery's added proof-only imports:
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`,
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
Their declarations are no longer used locally after deleting the duplicate helpers.
The affine-sections node is no longer a direct proof dependency: the existing power
lemmas encapsulate that argument. Its module remains a transitive dependency.
The previously removed redundant imports `Mathlib.CategoryTheory.Subobject.Limits`
and `Mathlib.CategoryTheory.Adjunction.Mates` remain absent.
No baseline import is removed and no entire module is pruned from the final closure.
Relative to the current repository baseline, no old proof dependency is removed
from either node. The quotient-base-change-ideal and unit-quotient edges were
already absent from the baseline closedness node; both remain needed by the
isomorphism node.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily duplicated existing affine detection and ideal-power
helpers. All four duplicates named by import_prune_check.py have now been deleted,
and their existing library proofs are reused. The prior report's claim that the
restriction-zero module was unnecessary was incorrect for the repaired route.
Its private power lemmas are used; its restriction-zero theorem itself is not used.

The isomorphism argument still requires explicit quotient transport and compatibility
between independently chosen tensor-pullback adjunctions. Those local categorical
proofs are retained. No statement is disputed, no interface change or forced
adaptation is needed, and the unit route is unchanged.


## Second reading by C1

1. Compared the sole delivered Lean module with the repository using diff. Both
existing theorem signatures are byte for byte unchanged; the closedness proof,
public imports, visibility and docstrings are unchanged. Only proof bodies,
proof-scoped elaborator options, two proved private helpers and one proof-only
`import all` are added. No definition or target statement changes. Verdict: pass.

2. Compiled the delivered module locally through lcompile.py, with no errors or
warnings. Compiled a scratch copy of the current module with `#print axioms` for
both public theorems and both private helpers: each uses exactly propext,
Classical.choice and Quot.sound, with no sorryAx. The module contains no sorry,
axiom, unsafe, opaque, implemented_by, extern or kernel-check bypass. The
isomorphisms are constructed from subobject and cokernel universal properties
and conjugateIsoEquiv; no arbitrary data is extracted from an unproved existence
theorem. Verdict: pass.

3. No statement is split off and no new hole or node is added. Read both private
helper proofs. The power quotient comparison works for arbitrary F without a
flatness or quasi-coherence assumption on F: it tensors an isomorphism of ideal
inclusions before comparing multiplication images. For n=0 the ideal is the
unit ideal and both quotients are zero; J=0, J=top and F=0 cause no exception.
The tensor comparison handles identity morphisms and empty schemes and permits
an arbitrary adjI, by conjugating the actual adjunctions. No stronger compatibility
of independently chosen adjunctions is assumed. Verdict: pass.

4. Read the proof from the quotient target downward and checked the reused
power_mono/power_subobject proofs and closedImmersion_unit_quotient interface.
Searched lean/Sheaf and lean/WeilConjectures for quotient comparisons, power
subobjects, tensorPullback composition and unit conjugation; also searched Loogle
through msearch.py for adjunction/functor isomorphisms. The existing composition
isomorphisms alone do not give the needed equation for the arbitrary adjI; the
retained helper directly applies Mathlib conjugateIsoEquiv and its unit equation.
The duplicated power helpers have already been removed. Each direct proof-only
import supplies a used declaration; public imports support the unchanged
interfaces. Read sk-thm-p1.json realized: this local reduction bypasses no unit
statement or step and changes no unit record. No baseline module is pruned.
Verdict: pass.

5. Compared both node JSON files against the repository: only proof, proof_deps
and proof_origin change. The dependency sets are the unions of the steps' uses
and describe the actual pullback, kernel, power-subobject, unit-quotient and
adjunction transport arguments. The restriction-zero node is used for its
module's proved private power helpers, as explicitly recorded, rather than its
restriction-zero theorem. No baseline dependency is removed. Verdict: pass.

Second-reading changes: corrected the closedness node's proof_origin place to
mention only its actual pullback/closedness route, and clarified that the
closedness edges mentioned under No longer needed were already absent from the
current baseline. Refreshed the scratch axiom check to the delivered module and
added this review. No Lean proof repair was needed.
