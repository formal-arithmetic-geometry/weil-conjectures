## What changed

Completed the reduction of `AlgebraicGeometry.gabber_h0_zariski_top_unit_equation`
without changing its signature. Function extensionality turns beta's top-open
unit equation into an equality of functions. Composition with the comparison,
transitivity with the canonical étale identity, and evaluation at the input
section give the original conclusion. The proof compiles in 23.4 seconds.

The saved intermediate is now a function equality in the new module
`Sheaf.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation`. Its statement has
no beta, no Zariski inverse-image unit and no compatibility hypothesis. It isolates
the canonical étale naturality computation; the original theorem supplies the
separate beta-to-canonical-unit step. Repaired its header, proof docstring and
complete DAG record, and updated the original node's proof dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.gabber_h0_zariski_top_unit_equation` (node
`lem-weil-pbc-gabber-h0-zariski-top-unit-equation`). Added one hole in
`AlgebraicGeometry.gabber_h0_zariski_section_unit_equation` (node
`lem-weil-pbc-gabber-h0-zariski-section-unit-equation`). Its proof is exactly
`:= by sorry`. This is a decomposition, not a net decrease in holes.
No other Lean declaration is changed and no definition contains a hole.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` from the original
module; it is used in the canonical identity's proof plan and remains available
through the public construction imports. The original node no longer directly
uses `lem-weil-pbc-sets-etale-inverse-image-composition-units` or
`def-pc-fibre-product`; those belong to the intermediate identity's argument.
Also removed the redundant direct proof import of
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` from the new
module: the public construction import already supplies everything its statement
needs. No globally unreachable module is claimed as pruned, and the unit's route stays.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the original hole and did not complete a reduction.
Its new node lacked statement dependencies, searches, the verbatim Lean signature
and complete blueprint provenance. Those omissions are repaired.

Pointwise composition of the two equalities triggers expensive kernel conversion
of the étale adjunction unit. The completed proof composes equalities of functions
before evaluation and compiles within the existing limit, without changing any
definition, splitting a proof to bypass the limit or increasing the limit.

Checked the source online at Stacks Tag 09ZF: its pullback-functoriality paragraph
and the fourth paragraph introduce the comparison used here. The detailed
naturality argument in the new docstring fills in that categorical computation.
The empty scheme and identity maps require no exceptional hypothesis: the proof
plan uses functoriality, naturality and uniqueness of pullbacks throughout.
LeanSearch returned Internal Server Error and is recorded as unavailable;
LeanFinder, Loogle and grep supplied generic naturality lemmas but no complete
match. The blueprint search for 09ZF found no duplicate blueprint statement.

## New nodes

`lem-weil-pbc-gabber-h0-zariski-section-unit-equation` isolates the canonical
comparison's compatibility with the étale unit, independent of beta. Its proof
compares the preimage/top-open isomorphism with the identity-pullback presentation
by pullback uniqueness, applies unit naturality, then identifies the identical
composition and transport factors on both sides. No change record is needed:
existing signatures and definitions are unchanged.

## Second reading by X2

1. PASS: compared both delivered modules with the repository. The sole existing
   theorem signature and its docstring are byte-for-byte unchanged; the diff is
   confined to its proof and a private proof import. The new module is absent
   from the repository. No existing definition or target statement changes.
2. PASS: both modules compiled in import order (22.9 s and 20.0 s).
   Separate scratch probes for both declarations printed only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The sole new direct hole is
   `AlgebraicGeometry.gabber_h0_zariski_section_unit_equation`, exactly the
   named theorem listed above; no forbidden declaration or data hole is added.
3. PASS: read the canonical identity against all construction definitions and
   the actual descent comparison. Its factors coincide after unit naturality;
   its omitted beta step is independently supplied by the original proof.
   This is a strictly smaller intermediate argument, not a renamed restatement.
   Checked empty schemes, identity morphisms, and arbitrary sheaves: terminality
   and naturality require no nonemptiness, closedness or finiteness hypothesis.
   In a scratch file, terminal-object uniqueness and the resulting naturality
   function equality compiled. An attempt to compose the remaining factors
   exceeded the single-file limit; no experimental proof or options are delivered.
   Repeated searches with different queries: Loogle `CategoryTheory.Functor.map_comp`,
   LeanFinder on morphism uniqueness into preserved terminal objects, grep
   `pullback.*hom_ext|hom_ext.*pullback`, and rg on both library roots. These
   found generic tools but no existing canonical comparison identity.
   Checked the source at https://stacks.math.columbia.edu/tag/09ZF: it leaves
   pullback compatibility to the reader, so the expanded proof is agent-written.
4. PASS: the proof applies beta compatibility, then the canonical identity,
   with no alternative route above the node level. Read `dag/units/sk-thm-iff.json`,
   including its `realized` statement and step; neither is bypassed or changed.
   Every original proof dependency removed from the new direct dependency list
   is listed under No longer needed. No unreachable module is claimed as pruned.
   The new module's redundant direct composition-units import was removed.
5. PASS: the old node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its steps and dependencies match the completed Lean reduction. The new node
   has its source, complete natural-language proof, verbatim Lean signature,
   statement and proof dependencies, creation record, chapter/unit and blueprint
   provenance, and three successful kinds of recorded Mathlib searches.
   Corrected its proof-origin attribution to agent, since the detailed categorical
   computation is an expansion of compatibility left implicit in the source.

Changes by the second reader: removed one redundant proof import in the new
module, corrected new-node proof provenance, and recorded this independent
review. The established proof and the remaining theorem statement are unchanged.
The delivery closes one original hole and adds one strictly smaller hole:
net zero, a decomposition. No additional hole was closed during this reading.
