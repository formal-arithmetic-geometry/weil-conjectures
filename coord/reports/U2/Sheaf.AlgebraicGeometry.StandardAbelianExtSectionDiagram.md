## What changed

Replaced the sole sorry in `StandardAbelianExtSectionDiagram` by a complete Lean proof
from two strictly smaller statements. The existing declarations, signatures, definitions,
public imports and docstrings of the assigned module are unchanged. Its only added import,
`AbelianReplacementSectionHomotopies`, is a proof import.

The proof checks the explicit lift's augmentation, obtains a quasi-isomorphism of section
complexes and two homotopies, applies homology to both homotopies, and cancels the resulting
isomorphism. Extensionality then applies the counit computation to each source class.
There are no holes in this combining proof.

`AbelianCounitResolutionCalculation` constructs the forgotten augmentations, their explicit
`descOfQuasiIso` lifts, a fixed standard abelian injective resolution, the direct-image
section identification, and the adjoint counit section map. All these definitions contain
real constructions, with their required augmentation quasi-isomorphisms proved. Several
constructed maps are irreducible so later elaboration does not expand their recursive data.
The remaining theorem computes inverse image followed by the counit on this fixed abelian
resolution; it has no replacement complex K, map l, or section identification a.

`AbelianReplacementSectionHomotopies` states existence of one quasi-isomorphism of section
complexes and two chain homotopies. It contains no Ext/cohomology comparison, no degree p,
and applies to any augmentation-compatible module lift, not just the standard lift.
Its existential map is used only inside the theorem proof, never selected as definition data.

The assigned DAG node now records this combining argument. Two new nodes record the two
remaining parts with their sources and complete proof plans. The unit's statement and
realized steps are preserved; this is a refinement below that level.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_abelian_ext_section_diagram`
(node `new-standard-abelian-ext-section-diagram`). The assigned module has no sorry left.

Added and left as whole named theorem proofs:

- `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_counit_resolution_calculation`,
  node `new-abelian-counit-resolution-calculation`, in
  `Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation`.
- `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_replacement_section_homotopies`,
  node `new-abelian-replacement-section-homotopies`, in
  `Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopies`.

This is a decomposition, not a sorry-free proof of the mathematical result: one upper hole
is closed and two lower holes are added (net -1). The Ext calculation and the chain-homotopy
comparison are independent parts of the argument. The former does not quantify the module
replacement; the latter does not assert an Ext-map equality.

All three delivered modules compiled locally in import order, with each file below the
60-second limit. The last complete run took 33.8, 3.4 and 38.4 seconds respectively before
the final documentation/import cleanup. No axiom, unsafe declaration or hollow definition
is introduced. The dry run supplies the final local compile and axiom/preflight checks;
the maintainer's global build remains the final integration check.

## No longer needed

Removed the unused proof import `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
from both new modules, together with their unused local instance attributes. No original import was removed. No original node or module is claimed to leave the target's
import closure. The original direct proof-dependency edges to the flat comparison,
normalization and forgotten-injective acyclicity have moved into the two new argument parts;
their statements/definitions remain needed there. Specifically the removed direct edges are
`def-pc-flat-cohomology-comparison`, `new-module-cohomology-ext-resolution-normalization`,
and `lem-sc-injective-module-abelian-acyclic-zariski`; none is globally pruned.
No unit-level route is bypassed.

The proof does not need a new comparison isomorphism from Ext to the standard abelian
resolution: the counit theorem's target is already written using the module resolution and
its explicit map to that abelian resolution. No separate normalization hole was introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG correctly described the mathematical route, but its stated dependencies
only supplied definitions and acyclic normalization; none states the counit calculation or
the two replacement-comparison homotopies. Those two parts are now explicit worker items.

Searches used LeanFinder, Loogle, msearch grep and local rg. The source library's
`mapExtCounit` API defines the Ext operation but does not compute its section map.
The existing acyclic-comparison naturality theorem handles one-site resolution changes,
not this inverse-image/counit calculation. LeanSearch returned Internal Server Error;
this is recorded as unavailable without a mathematical verdict.

The new constructions initially incurred expensive conversion between module and abelian
resolution types. Profiling and explicit fixed resolution/map interfaces identified and
removed that expansion from the combining proof; no timeout limit was raised and no file
was split to evade the limit. The final two modules correspond to mathematical subarguments.

The sources read were Stacks 01FB (common section diagram), 01F7 (functoriality),
013P part (1) (lifting up to homotopy), 03FD and 06XR. The 013S uniqueness statement
was also read in the existing project node/module. In particular l need not be a
monomorphism: the replacement comparison uses the up-to-homotopy version of 013P,
with the mapping-cylinder reduction to its monomorphism version made explicit in the node.
No acyclicity of f_*F or exactness of module pullback is assumed. The new statements
include degree zero (where applicable), zero coefficients, and empty schemes.

## New nodes

`new-abelian-counit-resolution-calculation`: the pointwise Ext counit formula on a
concretely constructed abelian resolution, normalized through the supplied target module
resolution. Source: Stacks 01F7, 06XR, 03FD and 015E. Its module contains one remaining theorem.

`new-abelian-replacement-section-homotopies`: a purely section-complex comparison of a
module replacement with the fixed abelian counit lift. Source: Stacks 01FB, 013P and 013S;
quasi-isomorphism of sections uses 03FD and the acyclic comparison. Its module contains
one remaining theorem. No change record or forced adaptation is needed.


## Second reading by U2

1. PASS: diffed the assigned module against the repository. Every existing signature,
   definition body, visibility, public import and docstring is unchanged. The only original
   declaration edit is the target theorem's proof; the new import is private. The two other
   Lean modules are new. The existing node changes only proof, proof_deps and proof_origin.
2. PASS: compiled all three files in import order (32.1 s, 3.6 s, 37.5 s), then compiled
   both import cleanups (the counit module in 35.1 s). Exactly the two reported whole named theorem proofs contain sorry;
   no forbidden declaration or hollow definition occurs. Explicit descOfQuasiIso maps
   construct the data; the existential q is used only inside a proposition proof.
   A scratch copy with #print axioms checked all delivered public declarations: every
   construction has only propext, Classical.choice and Quot.sound; the combining theorem
   and the two lower holes additionally have sorryAx. No other axiom occurs;
   this delivery does not claim a sorry-free target proof.
3. PASS: checked both lower statements against their complete docstring arguments and
   matching verbatim Lean node records. The counit calculation has no K,l,a; the homotopy
   comparison has no Ext equality or degree p. They are distinct proper subarguments,
   not renamed copies of the item. For identity f the comparison reduces to resolution
   comparison, p=0 to the ordinary coefficient counit, and zero coefficients or empty
   schemes to zero cohomology; augmentation-compatible arbitrary beta is legitimate by
   uniqueness up to homotopy. Independently searched Loogle for homologyMap_eq, LeanFinder
   for sections of acyclic resolutions, msearch grep for derived adjunction/section counit,
   and local Lean sources for counit and acyclic comparison APIs. These give ingredients,
   not either full statement. Neither lower theorem is a few-minute corollary.
4. PASS: read the homology cancellation proof from the target downward and checked the
   shortest available ingredient route. Original public imports remain required by existing
   declarations. Removed the unused private enough-injectives imports and attributes from
   both new modules. All three old dependency edges are explicitly accounted for
   above, with no claim of globally pruned modules. sk-thm-p1's realized statement and four
   steps are unchanged; the refinement is below the unit level. Stacks 01FB, 013P(1),
   013S support the common-section and homotopy route.
5. PASS AFTER REPAIR: node statement strings match Lean verbatim, proof_deps equal each
   proof step's uses union, and new nodes have source, searches, created, blueprint,
   chapter, unit and Lean records. The top node describes exactly the written combining
   proof. Replaced lemma-weil-pbc-leray-acyclicity in both new proof plans with
   lem-weil-pbc-leray-acyclicity-quasi-iso: the former's Lean declaration is a long-exact
   sequence connecting morphism, whereas the latter is the needed preservation of
   quasi-isomorphisms between acyclic complexes.

Second reading changed only two unused private imports/local attributes, the two acyclicity
proof-dependency citations, and this review/pruning documentation. No statement or
construction was changed. The result remains a decomposition: one original hole closed,
two lower holes added, net minus one, with no globally pruned module.
