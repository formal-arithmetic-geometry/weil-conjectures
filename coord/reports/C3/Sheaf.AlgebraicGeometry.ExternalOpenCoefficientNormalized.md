## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_externalOpenCoefficient_normalized`
with its existing signature unchanged. Added two proved generic factor comparisons,
`exists_tensorPullback_openTriangle` and `exists_tensorPullback_openSquare`, each in its
own new module. The first uses the unit-normalized restriction and composition
comparisons; the second conjugates the pushforward comparison under two composite
adjunctions. The main proof composes the existing proved restriction-tensor comparison
with the tensor of these factor isomorphisms and checks its section formula.

Added proof-only imports of `Modules.RestrictionTensorComparison`,
`TensorPullbackOpenTriangle` and `TensorPullbackOpenSquare`. Updated the parent node's
proof route and added matching nodes for both proved helper modules. No definition,
existing public signature, target, or other group's module was changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.exists_externalOpenCoefficient_normalized`.
Also proved `AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_openTriangle`
(node `lem-sc-tensor-pullback-open-triangle`) and
`AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_openSquare`
(node `lem-sc-tensor-pullback-open-square`). The private tensor section helper is proved.
No `sorry` remains in any delivered module; zero holes were added or split off.
Independent `#print axioms` checks of all three public theorems show only
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. Thus the proved
declarations themselves have no remaining proof holes in their dependencies.
No claim is made about pruning the full targets import closure.

All three modules compile without warnings via `lcompile.py --all`.
Empty opens, zero modules and identity cases require no additional hypotheses:
the comparisons are isomorphisms of adjoints, and their formulas follow from units
and naturality rather than generation by global sections.

## No longer needed

No original import was removed: the existing public import
`ScalarGlobalSectionsComparison` is needed for the statement. The original planned
application of `lem-weil-pbc-module-pullback-tensor` / `ModulePullbackTensor` is no
longer used for the coefficient comparison; the already proved
`lem-weil-pbc-module-restriction-tensor-comparison` supplies exactly the needed
restriction-tensor formula. `ModulePullbackTensor` still occurs through the public
statement dependency, so no whole module is claimed to leave the target closure.

The parent's former direct proof dependencies
`def-weil-pbc-composite-adjunction`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`lem-weil-pbc-conjugate-iso-unit-equation` and
`lem-sc-etale-qcoherent-presheaf-functorial` now belong to the proved factor lemmas;
they are retained there, not globally pruned. The square proof does not use
`EtaleTensorSections` or `tensorSectionsComp`; its only additional proof import is
Mathlib's `CategoryTheory.Adjunction.Mates`.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the already proved restriction-tensor comparison.
The square factor can be constructed directly as the conjugate of a pushforward
comparison, so separate pullback composition and inverse restriction comparisons
are unnecessary there. This is a shorter route below the unit level; the theorem
of cube unit and its realized route remain unchanged.

The repository's literature source files are absent on this machine. The cited
Stacks Tags 0096, 0097, 01CD and 0BED were read on the official Stacks website.
LeanSearch returned Internal Server Error; this is recorded as unavailable, and
LeanFinder, Loogle and Mathlib source searches supplied the comparison tools.

## New nodes

`lem-sc-tensor-pullback-open-triangle`: the generic first-factor isomorphism with its
global-unit section equation, completely proved in `TensorPullbackOpenTriangle`.

`lem-sc-tensor-pullback-open-square`: the generic second-factor isomorphism for an
open inverse-image square, with its local-unit section equation, completely proved
in `TensorPullbackOpenSquare`. Neither new node leaves a proof obligation.

## Second reading by C3

1. PASS: compared the existing module with the repository using `diff` and checked
   the full original theorem signature byte for byte. It is unchanged. The only
   existing-module edits are the proof, its explanation, a proved private helper,
   scoped elaboration limits and proof-only imports. The two other modules are new;
   there are no changed definitions, existing signatures or forced adaptations.
2. PASS: independently compiled all three files in import order with `lcompile.py
   --all`, without errors or warnings. Scanned delivered Lean for forbidden trust
   mechanisms and holes: none. Compiled a scratch copy with `#print axioms` for
   `exists_externalOpenCoefficient_normalized`, `exists_tensorPullback_openTriangle`
   and `exists_tensorPullback_openSquare`: each uses exactly `propext`,
   `Classical.choice`, `Quot.sound`; no `sorryAx`. The temporary source was removed.
   The private helper follows from tensor-section naturality and the inverse-hom
   identity. No data is selected from an unproved mere-existence theorem.
3. PASS: zero statements are split off with `sorry`. Read both new proved factor
   statements and their complete docstring arguments. They isolate separate factors
   and do not restate the external tensor-product result. Empty source and empty V,
   zero modules, identity triangles and identity squares require no missing
   hypotheses: all constructions are comparisons of the indicated adjunctions,
   with equality transports retained. Renewed searches used Loogle
   `CategoryTheory.conjugateIsoEquiv`, LeanFinder "An open subscheme restriction of
   inverse image module sheaves commutes with base change and preserves the
   adjunction unit on sections", and source searches for restriction/tensor and
   pullback-unit comparisons. They confirm the generic tools used here, with no
   exact assembled theorem. Upstream `PullbackUnit` addresses Mathlib's different
   pullback functor; changing functors would still need comparison and normalization.
4. PASS: the main proof first uses the proved restriction-tensor comparison, then
   the two fully proved generic factors. The triangle uses the existing normalized
   `tensorSectionsComp`; the square directly conjugates pushforward comparisons.
   Each added plain import supplies a proof tool, and the retained public import
   supplies statement definitions. The report accounts for every former direct
   proof dependency no longer used directly; none is claimed globally pruned.
   The change stays below the theorem-of-cube unit route. Read
   `dag/units/sk-prop-av-cube.json`: its existing empty `realized.statement` and
   `realized.steps` lists remain unchanged; this delivery neither supplies nor
   bypasses a unit realization.
5. PASS: read all three node records against the Lean proofs. Checked each recorded
   Lean statement verbatim and checked that `proof_deps` equals the union of step
   `uses`. The parent's restriction/tensor and factor steps match its proof; the
   new nodes record the adjunction, restriction, composition and unit steps actually
   used, with source, search, creation, blueprint, chapter, unit and Lean fields.
   No existing node field outside the permitted proof/Lean fields was changed.

Second reading changed only this report: recorded the independent review and replaced
its provisional dependency caveat with the actual axiom-check result. No Lean or node
repair was necessary. One original hole closed, zero holes added, zero split off;
the two additional factor theorems are also fully proved. No whole module is pruned.
