## What changed

Replaced the hole in WeilConjectures.finite_coefficient_verdier by a complete assembly
from two strictly smaller statements: finiteVerdier_coefficient_diagrams (all morphism
laws, with constant-True interval predicates), and finiteVerdier_proEtale_left_tor (one
numerical bound on the pro-etale left endpoint). The etale left endpoint bound is proved
from verdier_preservation_strata and finiteHomDomain_flatModel. A generic proved helper
retains the comparison diagrams and carries each left endpoint bound through its
comparison isomorphism to obtain the right endpoint bound. Tor invariance is proved
separately for etale tensor/homology and intrinsic pro-etale K-flat representatives.

Moved the existing 25 definitions/instances verbatim to
Sheaf.SixFunctors.FiniteCoefficientVerdierData and publicly re-exported them from the
original item. The two new statement modules import Data, avoiding a circular import.
This relocation was made to support the split, before any compiler timeout. All original
public imports remain available through the public re-export; names, signatures,
visibility, attributes and data bodies are preserved.
The definition block was checked byte for byte. No other existing Lean module is edited.

Change record: coord/changes/Q2-finite-verdier-definition-relocation.md. It lists the
complete 65-module transitive consumer inventory; no consumer needs adaptation.

## Proved and sorry left

Original hole closed by decomposition: WeilConjectures.finite_coefficient_verdier
(blueprint cor-coef-finite-verdier). Its body has no sorry. This is a decomposition,
not a proof free of new assumptions: 1 old hole closed, 2 new holes added, net -1.

New holes, each in its own new module with a complete source proof and DAG node:

- WeilConjectures.finiteVerdier_coefficient_diagrams;
  lem-coef-finite-verdier-coefficient-diagrams.
- WeilConjectures.finiteVerdier_proEtale_left_tor;
  lem-coef-finite-verdier-proetale-left-tor.

Proved private glue: coherent_with_left_bounds, etale_tor_of_iso,
proEtale_tor_of_iso and etale_left_tor_bound. Data has zero holes. No definition
contains sorry and no data is selected from a new existence theorem.

## No longer needed

Removed the old private proof imports Sheaf.Paper.ComparisonTorAmplitude,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
WeilConjectures.ConstructibleSheaf.KernelCokernel,
Sheaf.Paper.ProEtaleConstructibleOrigin, Sheaf.Paper.FiniteCoefficientFlatModel,
Sheaf.Paper.BasicOperationsCoefficientReduction and
Sheaf.Paper.FiniteCoefficientHomChange from the item. The old
Sheaf.Paper.WeilVerdierPreservationStrata import remains, and
Sheaf.Paper.FiniteHomDomainCalculus supplies the scalar Tor bound.
All old public imports remain through Data; none is pruned.

At the parent node the direct proof dependencies are now the two new nodes,
lem-weil-verdier-preservation-strata and lem-coef-finite-hom-domain-calculus. The former
proof dependencies def-pur-derived-internal-hom, def-weil-finite-tor-amplitude,
lem-coef-finite-dualizing, lem-coef-finite-target-change-coherence,
lem-coef-finite-bidual-transpose, lem-coef-finite-hom-site-descent,
lem-coef-finite-site-hom-transport and lem-weil-finite-duality-site-comparison are used
below the new claims or by the unchanged definitions. They are not globally obsolete.
Likewise the removed legacy imports may remain needed transitively. No module or
mathematical dependency is claimed globally pruned; no withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies are available, but several use normalized closed records and
intrinsic ringed-site modules while the parent uses fixed ModuleCat sheaves and curried
Hom. These interfaces require real normalization and realization arguments, retained in
the diagram node and the pro-etale bound node rather than assumed definitional.
The first preflight required a new definition node for the relocated Data module;
def-coef-finite-verdier-comparison-data now records its unchanged construction.
The parent statement and its mathematical content are unchanged. The unit realized
record is empty and its route has not been bypassed. The latest blueprint proof is the
source; older snapshot paths in existing documentation were not used as authority.

Edge cases checked mathematically: exponent one, identity quotient, nonflat quotient,
zero input, empty scheme, a=b and d=0. The generic assembly does not assume biduality
is invertible. The numerical dual interval is ordered by a<=b and d>=0. Pro-etale Tor
invariance composes representative isomorphisms; it retains all module-sheaf tests.
The diagram claim omits numerical bounds and the left-bound claim contains no comparison
morphism, so neither is the parent statement under another name.

## New nodes

lem-coef-finite-verdier-coefficient-diagrams records the normalized natural comparisons,
evaluation and biduality squares, identity and cocycle on both sites without numerical
estimates. It retains the target-family, bidual-transpose and site-descent route of the
existing plan and explicitly accounts for fixed-module realization.

lem-coef-finite-verdier-proetale-left-tor records only the reduced pro-etale dual's
interval. Its proof uses etale origin, Verdier preservation, scalar flat-model interval
preservation and the scalar/site comparison. It does not include the right bound or
any coefficient diagram. Both nodes record LeanSearch, LeanFinder, Loogle and Mathlib
source searches; only generic module duality and Verdier localization lemmas were found.


def-coef-finite-verdier-comparison-data attaches the unchanged comparison predicate
and its 24 helpers to their new Data module. It packages the conclusion, without
asserting it. It adds no hole, axiom, data choice or mathematical hypothesis.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
