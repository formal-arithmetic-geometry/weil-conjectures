## What changed

Completed the proof of `AlgebraicGeometry.qcqsProjectionMate_of_affine` without changing
its signature or any existing definition. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ProjectionMateAffineChartCertificate` and
`Sheaf.Topology.SheafIsomorphismLocalOpenCover`. The proof obtains a certificate for each
affine open, installs its standard localization instances, applies the given affine
hypothesis, proves invertibility of every cohomology map using the sheaf cover criterion,
and applies Mathlib `DerivedCategory.isIso_iff`.

Added one module and node for the local comparison certificate. It has no affine-case
hypothesis: it produces an actual chart square and the transported affine data, together
with the implication to cohomology restricted to that chart. It does not assert the global
mate is invertible. The remaining work is the localization transport of the supplied
adjunction and arbitrary tensor comparison, the substantive content of parent steps 1--3.
The new docstring and node give that argument. Both modules compile through lcompile.py.
No definitions or other modules were adapted; no object is defined by an arbitrary choice
from an unproved existence statement. Certificate witnesses are eliminated only inside
the theorem proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.qcqsProjectionMate_of_affine`
(node `lem-pc-qcqs-projection-mate-affine-descent`), 1 of the item's 1 holes.
The item now has no sorry.

Added and still sorry: `AlgebraicGeometry.exists_projectionMate_affineChart_certificate`
(node `lem-pc-projection-mate-affine-chart-certificate`), in the new module
`Sheaf.AlgebraicGeometry.ProjectionMateAffineChartCertificate`.

This is a decomposition: one upper hole closed and one strictly local comparison hole
added, net zero holes. The cohomological and open-cover detection part is fully proved
from Mathlib and the existing sheaf locality theorem. The certificate's conclusion is
not the original conclusion under a different name: no affine theorem is assumed, the
geometry is a single commuting affine chart, and its conclusion is an implication from
one transported affine mate to cohomology on that chart.

## No longer needed

No imports or modules are pruned from the library closure. The five old direct parent
proof dependencies now absent from its `proof_deps` are:
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-restrict-derived-direct-image-open`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-derived-pullback`, and
`def-pc-derived-direct-image`. They remain in the certificate's proof plan; the three
definition imports also remain necessary for the parent's unchanged signature.
`def-pc-derived-category` and `lem-weil-pbc-sheaf-isomorphism-local-open-cover` are
still used directly. The certificate's remaining dependencies are planned obligations,
not claims that its sorry proof already uses them. No blueprint unit or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original planned declarations supply natural functor comparisons, but none states
the descent of the arbitrary supplied p and t or the resulting mate identification.
This is the missing glue isolated by the new certificate. It is not an obstacle that
the planned declarations have sorry: the new obligation concerns what their signatures
do not yet state. The existing main theorem's signature and meaning are unchanged.

The local source file literature/stacks-project/perfect.tex is absent on this machine.
The Stacks Tag 08EU page was read directly: its first proof sentence gives affine
locality for the canonical projection map. Its extension to arbitrary supplied p and t
is the agent-written localization argument already present in the parent node, not a
claim that Stacks explicitly proves that generalization. LeanSearch was unavailable;
LeanFinder, Loogle and Mathlib source searches were run and recorded. The blueprint
ancestor helper could not resolve this existing node, so the new node retains the
parent's recorded ancestor and extends its via chain.

## New nodes

`lem-pc-projection-mate-affine-chart-certificate`, module
`Sheaf.AlgebraicGeometry.ProjectionMateAffineChartCertificate`: one affine chart's
comparison certificate, covering the parent's localization and universe/chart transport
steps before the affine-case hypothesis is applied. It includes the actual chart square,
standard localizations and transported quasi-coherent objects. There are no change records
because existing interfaces are unchanged.

## Second reading by R1

1. Pass: diff against the repository shows only two private imports and the proof body
changed in the existing module. Its declaration signature and existing docstring are
byte-for-byte unchanged. There is no definition or target edit, forced adaptation, or
change record. The new certificate is a theorem, not a data definition.
2. Pass: both modules compile with lcompile.py. The sole remaining local sorry is
`AlgebraicGeometry.exists_projectionMate_affineChart_certificate`, as reported above.
No forbidden declaration or attribute is present. The explicit axiom probes show only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is expected from
this certificate and existing imported obligations. This is not an axiom-free proof.
3. Pass with documentation repair: checked the actual chart square, compactness of the
inverse image of an affine open, arbitrary supplied p and t, standard universe u+1,
and quasi-coherence under exact restriction. The empty chart uses the zero ring and
empty inverse-image scheme; the full chart uses identity restriction. For f equal to
an identity or M or L zero the same localized adjunction argument applies. In particular,
no monoidal coherence of arbitrary t is assumed: its naturality and invertibility allow
its descent through the product localization. Expanded the docstring and node to explain
preservation of inverted morphisms, localization of the adjunction, and counit/mate
compatibility. Read Stacks Tag 08EU; its locality argument concerns the canonical map,
while the explicitly agent-written transport extends it to supplied p and t. Independent
LeanFinder and Loogle searches found Mathlib lift₂NatIso and localization uniqueness;
rg in Sheaf and upstream found ProjectionMapCompat/ProjectionMapMate. They are generic
ingredients, not an existing theorem constructing the scheme restriction certificate.
The new obligation is strictly local and assumes no affine-case theorem, so this is a
real decomposition rather than a renaming of the original conclusion. Closing it needs
substantial scheme/localization comparison construction, not a few-minute application.
4. Pass: the parent uses Mathlib cohomology detection and affine coverage, then the
existing proved sheaf cover criterion. Its two new imports are proof-only. Existing
public imports are required for its signature; no unused proof import remains. Corrected
No longer needed to enumerate every removed direct proof dependency without claiming
that their modules are globally pruned. Read sk-thm-picard-duality's realized record
(empty statement and step lists) and unit text; this lower comparison changes no unit
statement, route, or realization.
5. Pass: checked both node statements and Lean records, exact new signature, source,
creation and blueprint fields, and equality of proof_deps with the union of step uses.
The parent now records its actual cohomology/cover reduction. The certificate retains
its explicit localization proof plan and named source; its full Lean proof remains open.
No other existing node field is changed. Recorded the independent successful searches
on the new node and in searches.jsonl.

Second reading changed the new certificate's proof docstring and DAG proof explanation,
added independent search records, and corrected the report's dependency accounting.
No Lean statement, definition, import, or proved proof body required repair.
