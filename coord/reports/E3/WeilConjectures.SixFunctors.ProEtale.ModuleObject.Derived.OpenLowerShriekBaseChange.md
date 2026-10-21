## What changed

Restored the assigned source module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`
from its authoritative quarantine path recorded in coord/rework.tsv, then proved its only hole.
Every existing declaration signature, attribute, public import and non-theorem body is preserved.
There are three new proved private helpers and three private proof imports:
OpenImmersionEssImage, finite-coefficient Open.BaseChange, and Sheaf.Paper.ProfinitePointPullback.

The proof follows the support/counit argument already recorded in the same-unit component nodes.
Ordinary abelian-sheaf cartesian base change and the module forgetful-pullback comparison show
that the pullback of an extension by zero has underlying sheaf in the extension-by-zero
essential image. The existing module essential-image lemma lifts this to module objects,
so the module adjunction counit is invertible. Derive this counit isomorphism, transport it
through the restricted-functor compatibility isomorphisms, and reflect it through the
bounded-constructible inclusion. Full faithfulness gives the invertible unit. Each component
of the original unit-square-counit exchange is therefore a composite of isomorphisms.
NatIso.isIso_of_isIso_app assembles the result. No inverse chosen from an unproved existence
statement is used.

The restored module compiles on the remote server in 9.9 seconds, without errors or warnings.
The Lean declaration parser compared it to the archive: no changed statements, no removed
public declarations, no new public declarations, no public-import changes, and the only
changed existing body is the theorem proved here. All lines satisfy the 100-character limit.
The import-direction tool approved all three proof imports. Two file-local linter options
suppress only inherited unused-section-variable and duplicate-coefficient-instance warnings;
keeping those original binders preserves the upstream interface.

Change record: coord/changes/E3-restore-open-lower-shriek-base-change.md.

## Proved and sorry left

Closed one of one archived holes:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'`.
Its original statement and all coefficient hypotheses are unchanged.
Zero sorry declarations remain in the delivered module; zero holes are added; zero are split off.
The private helpers cartesianModuleCounit, cartesianDerivedCounit and boundedCartesianCounit
are fully proved. This is a proof from existing library results, not a decomposition.

## No longer needed

No existing import, declaration, node or module is removed or withdrawn. No modules are
claimed pruned. The proof does not import or restore the quarantined ExchangeMono,
ExchangeSection or CondensedOpenClosedRecollement modules. Those modules may still be needed
by the older unprimed upstream API or other parents, so this delivery does not remove their
Lean attachments or DAG dependencies. The module's original public import stays verbatim.

## Where the brief, the DAG or earlier work was wrong

The live source is absent because of the recorded cluster-restore rollback; it was not
withdrawn. Its archive has one sorry, and restoration is accompanied by the actual proof.
There is no current DAG node whose lean.module attaches this primed upstream module;
searching both its module name and its primed theorem name found none. The related blueprint
unit and thm-sfb-dc-open-base-change-iso describe the older unprimed unrestricted-coefficient
API. Their existing component nodes describe the support/counit argument reused here.
No such node is repointed to this coefficient-restricted primed theorem, and no unrestricted
statement is weakened to match it. No DAG node field or unit route is changed.
The archival module docstring still labels the theorem as a sorried input; it is retained
verbatim with the other existing docstrings under the source-library editing boundary.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
