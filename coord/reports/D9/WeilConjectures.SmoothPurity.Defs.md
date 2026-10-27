## What changed

Filled AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived
from the existing general theorem boundedConstructible_tateTwistDerived_of_invertible
in Sheaf.Targets.PoincareTateBoundedConstructible, added as a private proof import.
Mathlib CharP.cast_ne_zero_of_ne_of_prime proves that ell is a unit in the base
field. Map that unit through the inverse affine global-section comparison,
X.hom.appTop and evaluation in each residue field. These instances discharge the
invertibility hypothesis of the general theorem, for every integer twist and shift.
The empty scheme is included, since the residue-field condition is then vacuous.

Only the theorem proof and its private import change. Every original signature,
attribute, public import, docstring and non-theorem body is preserved. Explicit
proof-local references retain the original section parameters without warnings.
The import-direction check confirms no cycle. No interface change or consumer
adaptation is needed. The final single-file compile passed through lcompile.py.
The direct mathematical consumers are WeilConjectures.PoincareDuality.Poincare
and WeilConjectures.TraceFormula.Dualizing; their unchanged sources are checked
in a scratch overlay with the delivered module.

## Proved and sorry left

Closed 1 of 5 original direct holes:
AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived.
Added zero holes; split off zero statements. This proof uses an already stated
upstream-generalization theorem that still has sorry; no transitive axiom-free
completion of Tate constructibility is claimed.

Four original direct holes remain unchanged:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace
  (node def-route-smooth-trace; original definition-data hole).
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap
  (node lem-route-is-iso-smooth-purity-map; original instance hole).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion
  (node lem-route-smooth-purity-iso-zero-of-is-open-immersion).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion
  (node lem-route-smooth-purity-iso-comp-open-immersion).

No definition data is chosen from an arbitrary existence theorem. The existing
smooth-purity construction attachment remains def-pur-condensed-smooth-purity-iso.

## No longer needed

None. No original import, declaration, module, node or dependency is removed.
The existing general Tate-constructibility theorem supplies the argument without
repeating its integral/root/tensor/internal-Hom construction in this source file.
No pruning of the smooth-purity reconstruction or unit route is claimed.

## Where the brief, the DAG or earlier work was wrong

The retained report treated an old restoration assignment as requiring this item
to remain byte-identical to its archive. On this attempt the current rework.tsv
has no row for WeilConjectures.SmoothPurity.Defs, returns/D9.md has no open return,
and queue.md lists it as an ordinary five-hole proof item. Therefore that historical
restriction is no longer a current reason to suppress the retained proof. The
required first deliver3.py run rejected the unchanged restoration packet because
the item was absent from its source diff. This delivery repairs that diagnostic
with an actual proof, under the current source-library boundary.

The old reconciliation report and the earlier proof remain in scratchpad.
The current public Tate-constructibility theorem still states the needed general
invertible-residue-field result. Its historical DAG attachment now points to an
upstream Poincare declaration absent from that live file; this packet uses the
existing general theorem by its actual module and name and does not rewrite that
other node or duplicate its statement.

The remaining trace reconstruction needs actual supplied Context and compact-support
comparison families. CondensedTateIntegralTower reconstructs normalized AdicTower
data, while CondensedExceptionalReconstruction takes ordinary strict-system Context
data as inputs. These are not interchangeable by applying its theorem. The existing
exists_normalizedSmoothPurityMaps only asserts existence of inverse maps and does
not determine a unique normalized trace, so selecting its arbitrary witness would
violate the data-construction rule. No such shortcut is used here.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
