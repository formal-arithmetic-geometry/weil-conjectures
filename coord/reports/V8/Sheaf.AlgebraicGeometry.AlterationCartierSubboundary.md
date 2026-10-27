## What changed

Proved `AlgebraicGeometry.exists_alteration_cartier_subboundary` in
`Sheaf.AlgebraicGeometry.AlterationCartierSubboundary`. Its complete public signature and
public imports are unchanged. No definition or consumer was changed.

Apply the existing global Gabber alteration to the nowhere dense Cartier support.
Use `regular_normal_and_normal_decomposition` to select a clopen integral component.
Its generic residue-field finiteness transfers to the canonical function-field algebra
through the proved generic-stalk/residue-field degree comparison. Properness, regularity,
separatedness and finite type follow on this component. The fully proved private helper
`snc_comap_clopen` restricts the SNC boundary directly: discard components missing the
clopen range, keep the remaining whole integral components, and use open-immersion stalk
isomorphisms for regularity and the intersection dimension formulas. The comap/map Galois
connection transports the sums defining intersections; affine appIso maps preserve
radicality; flat pullback preserves the Cartier condition. Schematic dominance and
the nonzero locally-principal Cartier criterion prove both pullbacks Cartier.

For the smaller support use the already proved
`Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support` (Stacks 0BJG/0BJH).
A point of this support has positive stalk dimension because it cannot be generic.
A dimension-one generalization lies on a boundary component. The SNC singleton codimension
equality makes its stalk on that integral component dimension zero, so it is that
component's generic point. Closedness contains the whole component in the smaller support;
specialization puts the original point on it. Selecting all contained components proves
the required finite union equality. Taking complements proves the last two assertions.

All new helpers are private and proved. The existing node and theorem proof docstring
now describe this route. The unit's alteration route is preserved. The added dependency
from smooth-base-change is a generic, already proved principal-support dimension lemma;
no smooth-base-change theorem or blueprint unit step is used. Import directions were
checked. The final clean compile took 9.8 seconds with no warnings.

## Proved and sorry left

Closed the original one hole in `AlgebraicGeometry.exists_alteration_cartier_subboundary`
(node `lem-sfb-alteration-cartier-subboundary`). The item contains zero `sorry`.
Added zero holes; split off zero statements. All private helpers are fully proved.
This proves the item from existing declarations, including the separately assigned
Gabber alteration; its existing hole is not claimed closed. No SNC parameter criterion
or other new holed dependency is used.

The public theorem signature was compared verbatim with the repository original and is
unchanged. Every Lean line is at most 100 characters. No new public declaration, definition,
module, axiom, or arbitrary witness-based public data construction was added.

## No longer needed

Removed the original private imports:

- `Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`: dimension-one detection and
  singleton SNC codimension replace the local UFD factorization and spreading argument.
  Removed this item's direct dependency `lem-trf-regular-local-ufd-boundary-factorization`
  and its obsolete top-level `tool_uses` approval.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: generic finiteness is a finite ring
  homomorphism statement; no finite scheme morphism is used.
- `Mathlib.AlgebraicGeometry.Noetherian` and
  `WeilConjectures.AlgebraicGeometry.Regular`: these APIs are already publicly imported
  through the unchanged statement imports, so the repeated private imports are redundant.

Removed the planned direct dependencies
`lem-weil-pbc-smooth-scheme-over-field-regular` (the alteration statement supplies regularity)
and `lem-sc-integral-scheme-stalks-in-function-field` (Cartier pullback follows from schematic
dominance and the nonzero locally-principal criterion). Removed the former's obsolete
top-level `tool_uses` entry. Retained the regular-normal decomposition and finite-type-over-
Noetherian dependencies, which the final proof uses.

These are direct dependency removals for this item, not withdrawals of modules or source
library declarations. The removed modules may remain needed by other consumers; no whole
module is claimed pruned from the targets' closure. No Lean file or DAG node is deleted.

The attempted private import `Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion` was
removed after preflight identified it on the route-pivot exclusion list. The final proof
checks every SNC clause under clopen restriction directly; that criterion and its
`lem-sfb-snc-boundary-parameter-criterion` dependency are not used.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The original six-step plan is valid,
but local UFD factorization is unnecessary for the subboundary assertion. The existing
proved dimension-one support detection lemma and the stated SNC codimension equality give
a shorter argument. The updated DAG and docstring record the actual proof.

The interrupted sandbox report described an earlier pure-dimension approach. That report
and the corresponding node proof have been replaced by the dimension-one argument that
actually compiled. No pure-dimension dependency is imported or delivered.


The first delivery preflight rejected the temporary SNC parameter-criterion import and
file-wide elaborator options. The import has been removed by proving clopen SNC restriction
in full, and each elaborator option is scoped to a single declaration. The project's
`leanindex.interface_changes` reports no interface differences. The signature and public
imports remain unchanged, so no consumer adaptation or change record is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
