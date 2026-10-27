## What changed

Replaced the hole in `AlgebraicGeometry.Etale.DualizingOpenMate.restriction` with
an adjunct calculation using the existing scalar/open composition theorem.
All existing public declarations, definitions and signatures are unchanged.
Local elaboration options enable the existing derived-category definitional
equalities used by the private proof calculations.
Six proved private helpers handle the fixed compactification, inverse naturality,
local inverse, and the two adjunct equations. Proof imports add
`Sheaf.Paper.EtaleCompactScalarCoherence` (including its proved private open
normalization bridge) and `Sheaf.Paper.OpenScalarSiteCoherence`.
The node proof now records the actual open-composition argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.DualizingOpenMate.restriction` (one original hole).
Added: none. Remaining in the delivered module: none. No split-off modules.
Server single-file compilation passed in 23.6 seconds with exit code 0 and no
warnings. The delivery tool performs its independent compile and axiom probe.
The theorem is proved from existing library declarations; its transitive
dependencies still include unfinished project theorems.

## No longer needed

The proof no longer uses `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`;
its proof import is removed. The redundant proof import
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` is also removed;
the definitions retain its required API through their existing public imports.
The old proof dependencies
`lem-coef-dualizing-open-adjoint`, `lem-coef-dualizing-open-tensor`,
`lem-fix-compact-support-coefficient-change`, `lem-sf-compact-coefficient-composition`,
and `thm-amb-etale-exceptional-adjoint` are unnecessary for this proof. Their
statements and modules remain available to other consumers. In particular the
public import of `CompactCoefficientComposition` stays because the statement
uses its coefficient quotient map and positive-level finiteness instances.
The old two proof tool approvals are removed from the node because neither
result is used in the new proof.

## Where the brief, the DAG or earlier work was wrong

The previous plan required bounded finite-Tor domain bookkeeping and the general
compact-support composition theorem, whose published ordinary-etale statement
uses different coefficient tensor models and bounded-below coordinates. The
open compactification here has exactly the same proper part as the global
compactification. Its required composition equation therefore follows directly
from the proved ordinary scalar/open composition law and naturality of the proper
scalar mate. Proper finite coefficient extension makes the specified comparison
invertible on all inputs over the Noetherian base. Consequently the original
hypotheses remain verbatim but the proof needs no finite-Tor bookkeeping.

The new proof uses the generic results owned by
`lem-pur-etale-compact-scalar-coherence`,
`lem-pur-etale-open-scalar-composition`, and
`lem-asd-proper-finite-coefficient-extension`. These are tools for the fixed open
calculation, preserving the local/global adjunction route; the independent
reader can record any required tool approvals. No exceptional coefficient mate
comparison theorem is used. The original theorem docstring is preserved as API;
the node and this report record the shorter implementation.

The private calculations hold for arbitrary open immersions and arbitrary derived
inputs over a Noetherian base with finite coefficients. Thus the edge cases of
the empty open, the whole open, zero objects, and equal coefficient levels need
no separate non-emptiness or strict-inequality arguments. The proof never cancels
the global dualizing mate and never assumes flatness of the coefficient quotient.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
