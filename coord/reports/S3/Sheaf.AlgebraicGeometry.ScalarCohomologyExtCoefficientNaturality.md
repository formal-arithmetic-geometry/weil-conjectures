## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtEquiv_map` in
`Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality`, preserving its statement
and visibility. Added a proved private helper `moduleExtEquiv_map_aux` for the O-module
comparison before scalar restriction. Added the proof-only import
`Mathlib.Algebra.Homology.ConcreteCategory` for concrete cycles and homology naturality.
Private instances select the same small Ext universe as `moduleExtEquiv`; the existing
local attribute on `HasExt.standard` supplies Ext for scalar sheaves. These private
instances add no importer-visible declarations.

The helper chooses injective resolutions and a comparison lifting the coefficient map.
Represent `moduleExtEquiv F n a` by `InjectiveResolution.extMk_surjective`, evaluate its
cocycle at 1, and build the corresponding global-sections cycle with `cyclesMk`.
The existing `exists_moduleExtEquiv` specification and injectivity identify its derived
class with `a`. Naturality of cycles, homology projection, and `isoRightDerivedObj` gives
the target class; the same specification and `extMk_comp_mk₀` identify its Ext image.
Finally, `mapExactFunctor_comp`, `mapExactFunctor_mk₀`, and Ext associativity transport
this equality through scalar restriction and precomposition by `scalarUnitMorphism`.

This realizes the original node's proof without changing its route or dependency list.
The unit `sk-prop-av-cube` has no realized statement or steps attached to this node;
its prescribed route is preserved. The sources read are Stacks Tags 01DZ (module
cohomology) and 01F7 (resolution comparison for functoriality), on their official pages.
LeanFinder, Loogle, logged grep searches, and local library searches found the generic
resolution and Ext lemmas used, but no existing theorem for this recorded comparison.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtEquiv_map`
(node `lem-sc-scalar-cohomology-ext-coefficient-naturality`).
Added zero holes; split off zero statements. No `sorry` remains in the delivered module.
The private helper is fully proved. Existing dependencies of the operations module,
including `exists_moduleExtEquiv` and exactness of scalar restriction, remain as before;
this is a proof from those recorded declarations, not a claim that the entire import
closure is sorry-free.

Local compilation passed without errors or warnings. The argument uses `n + 1` only
as the outgoing differential degree and hence also covers degree zero, zero coefficients,
and the empty scheme. No nonzero, nonempty, finiteness, or local-freeness hypothesis is
introduced.

## No longer needed

None. No imports were removed and no planned dependency node or module was bypassed.
The new concrete homology import is used by the private helper. No auxiliary
Ext/right-derived comparison module is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. `moduleExtEquiv` is marked irreducible, so its
existing cocycle specification must be accessed by explicitly unfolding it in the helper.
The small universe of O-module Ext requires a private specialized `HasExt` instance
and an explicit small-universe Ext composition in the helper signature. These are proof elaboration details; all existing
statements and definitions are unchanged. No new nodes or forced adaptations.

## Second reading by S3

1. PASS: Compared the sole delivered module with the repository using `diff -u`.
   The existing theorem signature, docstring, visibility, options and namespace are
   unchanged byte for byte. Only its proof, the private proved helper and instances,
   and the plain proof-only ConcreteCategory import were added. No definition or
   target statement changed; no change record or forced adaptation is needed.
2. PASS: Independently compiled the delivered file with lcompile.py: exit 0, no
   warnings (31.4 seconds). A scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtEquiv_map` also compiled
   and printed exactly propext, Classical.choice, Quot.sound and sorryAx. The latter
   comes from existing open imported statements, including exists_moduleExtEquiv
   and the scalar-functor exactness and comparison facts; the delivery contains no
   sorry, forbidden declaration, or new chosen data. The private instances use the
   same enough-injectives theorem and small Ext universe as the operations module.
3. PASS: Zero split-off statements and zero added holes. Read the private helper
   in full: extMk_surjective supplies a cocycle, evaluation at 1 supplies its cycle,
   and the existing comparison specification plus injectivity identifies the class.
   cyclesMap_i, homologyπ_naturality, isoRightDerivedObj_inv_naturality and
   extMk_comp_mk₀ give its coefficient image. All are used with their actual
   hypotheses, with no positive-degree assumption: n = 0, zero coefficients and
   the empty scheme are included. No arbitrary witness of an unproved existence
   theorem is introduced.
4. PASS: Searched the library for moduleExtEquiv naturality and cohomology/Ext
   comparisons, and inspected upstream Modules/Ext.lean and the Mathlib injective
   Ext lemmas. The upstream comparison concerns the abelian-sheaf cohomology
   definition, whereas this theorem uses the recorded O-module right derived
   functor; it does not supply a shorter replacement. The proof already uses the
   generic Mathlib naturality and Ext-composition lemmas. The sole original import
   is required by the signature and the sole additional import supplies concrete
   cycles. The old proof_deps contains only the operations node, still used, so
   `No longer needed: None` is complete. Read sk-prop-av-cube.json: its realized
   statement and step lists are empty; this proof replaces no unit step or route.
5. PASS: Read lem-sc-scalar-cohomology-ext-coefficient-naturality.json and its
   operations dependency. Its proof describes exactly the resolution comparison,
   evaluation at 1, scalar restriction and Ext associativity implemented here.
   Its existing proof_deps and proof_origin remain accurate; no node edits or new
   nodes are required.

Second reading changed only this report by recording the independent review.
No Lean repair was necessary. Closed one original hole, added zero holes.
