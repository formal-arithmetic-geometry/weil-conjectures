## What changed

Proved `CategoryTheory.exists_cartanEilenberg_comparison_cycle_stage` in
`Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage`, without changing its signature
or visibility. All row preparation is implemented by proved private definitions and lemmas
in the same module. These construct the short exact boundary/cycle/homology rows, their
naturality under an exact functor, their degree-zero presentations, and the augmented
boundary square obtained by cancelling the coefficient boundary epimorphism.

The homology endpoint uses the already proved source-library
`CategoryTheory.InjectiveResolution.descOfQuasiIso` and its commutation theorem. The
existing exact-source horseshoe theorem then supplies the middle map, and the final
composition and cancellation arguments prove both original formulas.

Added proof-only imports
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images`.
Updated only the proof route fields of the assigned DAG node. No public definitions,
new public statements, new nodes, statement changes or forced adaptations are delivered.

Validation: the module compiles with the required local compiler and no warnings.
The source support argument covers the all-zero complex, vanishing boundary/homology
objects and arbitrary horizontal degree p; it never chooses a least nonzero degree.
The functor is only assumed additive and exact, and no source injectivity is used.

## Proved and sorry left

Closed the sole local hole:
`CategoryTheory.exists_cartanEilenberg_comparison_cycle_stage`
(node `lem-weil-pbc-ce-comparison-cycle-stage`).

No `sorry` remains in the assigned module, and no new holes are added. This is a proof
from existing named dependencies, rather than a decomposition into new holed statements.
The imported dependency
`CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`
(node `lem-weil-pbc-horseshoe-morphism-lift-exact-source`) is used unchanged. At second
reading the compiled dependency is proved: its axiom check, and that of the delivered
target, show only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the unused proof import `Mathlib.Algebra.Homology.ModelCategory.Injective`.
The node `lem-weil-pbc-lift-along-injective-quasi-iso` is no longer a proof dependency:
its general bounded-below model-category lifting route is replaced by the source-library
single-source resolution construction `descOfQuasiIso`. Its source map need not have
injective terms. No other node or existing import is removed by this delivery.
The preparatory theorem is private and fully proved in the assigned file; no additional
Sheaf statement module is needed.

## Where the brief, the DAG or earlier work was wrong

The plan's first step called the row normalization elementary, but it requires explicit
kernel/image/homology preservation, row naturality and support arguments. These are now
proved, rather than assumed or split off. Evaluation at zero plus the proved supportedIso
construction avoids having to identify every single-bicomplex column with a single complex
on a separately chosen model of the coefficient object.

The planned general monomorphic-quasi-isomorphism lifting theorem is stronger than needed:
`descOfQuasiIso` already handles the source resolution of a single coefficient object.
The unit record `sk-prop-h2` is unchanged; this work is entirely below the unit level.
The source tex file is absent from this read-only checkout; the cited Stacks statements
were read from the official pages for Tags 015I, 015K and 013P.


## Second reading by V3

1. Compared the sole delivered module against the repository with `diff`. The only existing
   declaration is `CategoryTheory.exists_cartanEilenberg_comparison_cycle_stage`; after
   restoring one extra space before its proof, its signature is byte-for-byte identical.
   Visibility and all hypotheses and conclusions are unchanged. No existing definitions
   or other modules are changed, and no change record is required. Verdict: passes.
2. Independently compiled the module without errors or warnings. Searched the delivered
   Lean sources for sorry and prohibited declarations: none occur. Compiled a scratch copy
   with `#print axioms` for the target, row presentation theorem, constructed row data,
   support isomorphism, single comparison, descOfQuasiIso and horseshoe theorem. Each uses
   only propext, Classical.choice and Quot.sound. The coefficient data is constructed
   explicitly in a fully proved theorem; no arbitrary witness from an unproved existence
   theorem is selected to define an object. Verdict: passes.
3. There are no split-off statements, new public declarations, new holes or new nodes.
   Read the private row presentation and its construction: it supplies row preparation,
   not the desired comparison. Checked zero columns, vanishing boundary/homology objects,
   p = 0 and negative horizontal p: the support argument uses only positive resolution
   degrees, and image epi cancellation and kernel inclusions work for zero objects.
   Re-searched the library and Mathlib for row preservation, supportedIso, homology
   cokernels and descOfQuasiIso. Existing preservation/cokernel/lifting lemmas are used;
   no duplicate holed statement is introduced. Verdict: passes.
4. Read the proof downward: explicit row normalization, coefficient boundary cancellation,
   existing descOfQuasiIso, existing exact-source horseshoe comparison, then the two
   requested compositions. No shorter applicable replacement was found. Removing the
   Images proof import in a scratch copy loses PreservesImage.iso and its identities.
   Demoting the existing public Resolution import loses QuasiIso and the cycles/homology
   API in the public signature, so it is required for statements, not only proofs. Both
   new imports are proof-only. No longer needed lists the sole removed import and the
   sole removed old proof dependency. The sk-prop-h2 realized record is unchanged; no
   unit realization is bypassed. Verdict: passes.
5. Compared both versions of the existing node: only proof, proof_deps and proof_origin
   differ. Read every new step against the implementation: the sole remaining DAG proof
   dependency is the exact-source horseshoe node, and the proved upstream homology lift
   is explicitly named in the route. No node statements, Lean records, units or sources
   were altered. Verdict: passes.

Second reading changed the extra signature whitespace back to the repository's spelling
and corrected the stale report claim that the horseshoe dependency remained unproved.
The proof itself needed no repair. Closed one original hole; added zero holes.
