## What changed

Proved `AlgebraicGeometry.Scheme.affine_dual_restriction_comparison` without changing
its signature or its existing docstring. Added only private, fully proved helpers
to the original module. All new imports are proof-only imports.

The affine proof constructs the linear identification between the module dual and
global sections of the sheaf internal Hom. Its underlying bijection combines the
fully faithful tilde functor, tildeSelf, homObjSectionsEquiv, and an explicitly
proved equivalence between compatible sections and top-open sections. Scalar
linearity uses the existing proved tilde_scalar_section_action. The finite module
hypothesis gives finite presentation of tilde M; the existing quasi-coherence
of internal Hom theorem then makes the tilde-Gamma counit an isomorphism.
Finally restriction, overHomObjIso, the existing internalHom_overEquiv, and
restrictUnitIso give the requested open-subscheme isomorphism.

Updated the item's DAG proof, proof_deps and proof_origin to this route. No other
module, signature, definition exposed to importers, or target statement changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_dual_restriction_comparison`
(node `new-affine-dual-restriction-comparison`).

No sorry remains in the delivered module, and no holes were added or split off.
The proof uses the already stated
`AlgebraicGeometry.internalHom_overEquiv`
(node `lem-sc-internal-hom-over-equiv`), which currently has a sorry in the library;
this is an existing proof dependency, not a new hole or an axiom-free final proof.
The quasi-coherence and scalar-action declarations used here are already proved.

## No longer needed

No original imports were removed: the four original public imports support the
unchanged statement and definitions. No original proof dependency can be pruned,
since the original node had proof_deps = [].

The direct localization-Hom calculation, comparison on individual principal opens,
and gluing those local comparisons are not needed in this module. They are replaced
by the existing quasi-coherence theorem and affine tilde-Gamma equivalence. There
were no separate planned nodes or imported modules for these steps, so there is
no module to prune. No new localization, evaluation-map or slice-transport modules
are delivered.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof names no dependencies despite requiring nontrivial
localization and sheaf assembly. The library already supplies the needed affine
quasi-coherence result and the exact slice-site internal-Hom transport declaration;
using them avoids new intermediary statements. The replacement keeps the unit's
route: this node remains an affine dual restriction input to the depth-two
extension argument. Empty W, zero M, and the zero ring are included without adding
hypotheses. The linear global-sections construction itself does not use the
Noetherian or finite hypotheses; those enter precisely at finite presentation
and quasi-coherence of H.

The source tag on `lem-sc-internal-hom-over-equiv` is imprecise: Tag 08DL
states restriction compatibility for derived internal Hom. The underived
restriction fact is Tag 0E8H, and its realization through overEquiv is the
slice-category transport described in that node's proof. Its Lean statement
is the exact transport needed here and is not changed by this delivery.

## Second reading by V3

1. **Repository comparison and interfaces:** The delivered module was diffed against the
repository version. The public theorem signature and docstring are byte-for-byte unchanged;
only proof-only imports, private helpers, and the proof body were added. Verdict: pass.

2. **Compilation and axioms:** The module compiles with `lcompile.py` (77.5 seconds), and
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof
uses the existing `internalHom_overEquiv` dependency, whose open proof is recorded in the
library. Verdict: pass.

3. **Statements and search:** No new public statement or split-off theorem was added; all
helpers are private and fully proved. The target statement is unchanged and matches the
Stacks source. Searches found no existing affine-dual restriction comparison to replace it.
Verdict: pass.

4. **Route and pruning:** The proof follows the affine tilde equivalence, finite-presentation
quasi-coherence, and over-equivalence restriction route. The unit input remains used, and
the original public imports remain needed for the statement. The five added imports are
proof-only and no unused planned dependency is retained. Verdict: pass.

5. **DAG agreement:** The node proof, proof dependencies, and proof origin were updated to
describe the actual route; no new nodes or holes were introduced. Verdict: pass.

Changed after second reading: added this review record only; no Lean declarations or node
statements were changed.
