## What changed

Proved `AlgebraicGeometry.Etale.exists_restricted_affine_complex_system_natural`
from a natural coefficient-system construction and the existing
`rawAffineComplex_system_map_coherence`. The existing theorem signature, docstring and
public imports are unchanged. Added two plain proof imports.

The proof constructs the cohomology functor T and cocone B explicitly. Stage and vertex
boundedness let the existing coherence theorem prove the functor and cocone laws. The
presentation uses identity cohomology isomorphisms and the prescribed pullback formula
using a private reflexivity lemma that keeps the derived-functor formula folded.
Proved private helpers package the presentation and simplify its identity comparisons;
these remain in the same module and have no holes. Evaluating the two coefficient comparison equalities proves both requested
compatibilities independently.

The new module `RestrictedAffineNaturalCoefficientSystem` states the geometric/coefficient
construction only, with both stage and cone-leg comparison equalities. It supplies no T, B,
cohomology functor laws, or EtaleComplexCohomologyPresentation. It is strictly the coefficient
part of the argument; the parent constructs and combines the remaining data in Lean.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.exists_restricted_affine_complex_system_natural`
(node `lem-sbc-restricted-affine-complex-system-natural`).

Added one named hole:
`AlgebraicGeometry.Etale.exists_restricted_affine_natural_coefficient_system`
(node `lem-sbc-restricted-affine-natural-coefficient-system`). Its proof is exactly `by sorry`;
its docstring gives its source and full construction. This is a decomposition, one hole closed
and one added, with net zero holes. No definition or arbitrary witness selection was added.

Edge cases: for the empty affine etale object all pullback schemes are empty and the same
single-complex construction applies. Degree zero and zero coefficients require no extra
assumptions. Identity and composite arrows use the stated upperStarComp coherence. Constant
systems specialize to identity comparisons. The coefficient cocone vertex is a single complex,
so both stage and vertex lower bounds are zero. No cohomology-colimit conclusion is assumed.

## No longer needed

No original import was removed and no whole library module is pruned. The parent no longer
uses these original direct proof dependencies: `def-weil-pbc-inverse-image`,
`lem-weil-pbc-inverse-image-composition`, `def-pc-fibre-product`,
`def-weil-pbc-etale-cohomology`, `prop-weil-pbc-derived-inverse-image-adjunction`, and
`lem-weil-pbc-affine-morphism-permanence`. Their needed content remains below the coefficient
construction or the existing coherence theorem, or in public signature dependencies.
`def-sbc-raw-affine-restricted-cohomology` remains used directly.

`RestrictedAffineComplexSystem` and `RestrictedAffineCoefficientSystem` do not supply the
required stage comparison, so they are not imported as proof dependencies. They remain in
the library for their existing users. No claim is made that they leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempted to replace the already existing coefficient theorem with a
new interface and a colliding declaration/node name. This delivery leaves that module and
node unchanged and uses a new, distinct natural coefficient theorem. Its old concrete-data
and generic cohomology helper modules and nodes are not part of this delivery.

The earlier target reduction repeatedly exceeded 60 seconds during elaboration of the
concrete pullback/single-complex interfaces. The replacement keeps the coefficient witnesses
abstract and uses the existing bounded-below complex-map coherence theorem, while explicitly
constructing the cohomology diagram and cocone. It does not split a proof into modules to
bypass the time limit. It also retains boundedness of the coefficient cocone vertex, which
is needed by the existing coherence theorem.

Read Stacks Tags 09Z1 (affine-object restriction in lemma-relative-colimit) and 0EZM
(lemma-colimit-variant-complexes). Only their coefficient construction and canonical maps
are used; their continuity conclusions are not assumptions of the new theorem. The unit
`sk-lem-failure-field` has empty realized entries for this node, and its route is unchanged.
The existing non-natural coefficient statement has no stage comparison. Equality of cone
legs cannot imply stage equality without a monicity hypothesis, so that missing clause must
be supplied by the coefficient construction itself.

## New nodes

`lem-sbc-restricted-affine-natural-coefficient-system`, in
`lean/Sheaf/AlgebraicGeometry/RestrictedAffineNaturalCoefficientSystem.lean`, states the
restricted coefficient-complex construction with the two comparison morphism equations.
The node records the explicit pullback, single-complex, inverse-image coherence and
colimit-preservation argument. Search queries and results are recorded in the node and
sandbox search log. No existing signature or definition changes and no forced adaptation is required.
`coord/changes/restricted-affine-natural-local-transparency.md` records local-only
transparency attributes requested by the conservative preflight command check.
They prevent expensive unfolding during proof elaboration and are not exported.

Validation: the required deliver3.py --no-push dry run printed OK; nothing was pushed.
The local compilation and preflight passed, with only the expected second-reading
section left for the next worker. The separate axiom probe on the parent exceeded
60 seconds; deliver3.py reported that merge reruns it. This delivery contains no
forbidden declarations, and its only explicit hole is the new coefficient theorem.

## Second reading by N1

1. Compared the delivered parent with the repository version and checked the existing
theorem signature byte for byte by extraction: identical. Both original public imports
and the original docstring remain intact. The new imports are plain proof imports.
The local transparency attributes change no definition or exported interface.

2. Compiled both delivered modules separately through lcompile.py: no errors or
unexpected warnings (coefficient module 7.2 seconds, parent 55.9 seconds). An independent
scratch module imports the compiled delivery and prints the axioms of both public
theorems. The parent uses only propext, Classical.choice, Quot.sound and sorryAx.
The only explicit sorry is the named new coefficient theorem. There is no axiom,
unsafe, opaque, implemented_by, extern, holed definition, or arbitrary data choice.
The existential witnesses are eliminated locally in a proof of a proposition.

3. Read the whole split-off theorem and its construction docstring, and checked
Stacks Tags 09Z1 and 0EZM. Pullback base change, inverse-image coherence and the
degree-zero single functor give the asserted coefficient data; restriction and
the single functor preserve the coefficient colimit. The two comparison equations
are separately needed. For empty U all complexes are zero; for zero coefficients
the maps are zero; degree zero uses the same construction; identity and composite
arrows are precisely the stated coherence equations. No continuity conclusion is
assumed. This is a genuine coefficient-step decomposition: it provides no T, B,
functor laws or cohomology presentation, all constructed by the parent. Read the
existing non-natural coefficient theorem, which lacks stage compatibility. Fresh
leanfinder and loogle searches used inverse-image/single-complex colimit language
and mapCocone/IsColimit respectively: only general building blocks, no duplicate.
Local rg searches confirmed the non-natural coefficient theorem and existing map
coherence are the nearest statements. Closing the new coefficient hole requires
the geometric construction and is not a few-minute repair.

4. Read the proof from its conclusion back to its inputs. The existing complex-map
coherence supplies all functor/cocone laws; private helpers only package the
presentation and identity comparisons. All four imports are needed by signatures
or proofs. Checked the original proof_deps: the six removed dependencies are all
listed above under No longer needed; no module is claimed pruned. The unit
sk-lem-failure-field has empty realized statement/step entries, so no unit route
is bypassed. One upper hole is closed and one coefficient hole added: decomposition,
net zero, not a fully axiom-free proof.

5. Checked both DAG records against the Lean: the new lean.statement is verbatim,
its status is split, and its source, construction proof, searches, created, unit,
chapter and blueprint fields are present. The parent proof steps and proof_deps
match the coefficient construction, existing coherence, and explicit packaging.
The local transparency change record accurately describes a proof-only effect.

Changes by this second reader: added this independent review and an axiom scratch
check; no Lean proof, statement, definition, import, or DAG repair was needed.
