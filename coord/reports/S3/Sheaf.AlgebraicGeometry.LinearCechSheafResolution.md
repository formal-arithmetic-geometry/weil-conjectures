## What changed

Completed the earlier sandbox reduction of
`Sheaf.AlgebraicGeometry.LinearCechSheafResolution`. The existing declaration
`AlgebraicGeometry.exists_linear_cech_sheaf_resolution` keeps its signature and public
imports unchanged. It obtains the augmented complex and its scalar-compatible comparisons
from `Sheaf.AlgebraicGeometry.LinearCechSheafConstruction`, applies the existing
`AlgebraicGeometry.augmented_cech_sheaf_quasiIso_restrict` on each cover member, and proves
the global quasi-isomorphism in Lean.

Repair of the maintainer's duplicate-statement return: removed both private declarations
`AlgebraicGeometry.isIso_of_restrict` and `AlgebraicGeometry.quasiIso_of_restrict`.
The isomorphism argument now imports and applies the existing public theorem
`Scheme.Modules.isIso_of_isIso_pullback_map` from
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`, specialized to the covering
open immersions. Their flatness is inferred; their joint surjectivity follows from hU.
`restrictFunctorIsoPullback` converts the local restriction isomorphisms to pullback
isomorphisms. The remaining homology comparison is proved directly for the constructed
augmentation inside the final theorem; it declares no duplicate generic theorem.

Retained the proof import `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`:
it supplies `Scheme.Modules.preservesLimitsOfSize_restrictFunctor`, which is needed for
the short-complex homology comparisons. Compilation without that import fails to
synthesize PreservesLeftHomologyOf. No quasi-coherence hypothesis on F is introduced.
All added imports are private proof imports. No other module is adapted.

Added the missing construction node and updated the item's proof dependencies to match
its Lean reduction. The construction module contains exactly one public theorem, with
source and complete construction proof in its docstring. Its conclusion concerns only
construction and scalar compatibility, for any family of opens; it asserts no exactness.
Existential witnesses are consumed inside a proof and are not used to define data.

Validated both repaired modules together in import order with lcompile.py, with no errors
or warnings. The final theorem still depends on the named
construction hole and the existing local exactness dependencies, as intended in stage 3.

## Proved and sorry left

Closed the single original body hole:
`AlgebraicGeometry.exists_linear_cech_sheaf_resolution`
(node `lem-pc-linear-cech-sheaf-resolution`). There are no sorries in the item's module.

Added one hole:
`AlgebraicGeometry.exists_augmented_linear_cech_sheaf_complex`, in
`Sheaf.AlgebraicGeometry.LinearCechSheafConstruction`
(node `lem-pc-linear-cech-sheaf-construction`). Its entire proof is `:= by sorry`.

This is a decomposition: one upper hole closed, one lower construction hole added, with
zero net hole reduction from those two bodies. The proof also uses the existing, unchanged theorem
`AlgebraicGeometry.augmented_cech_sheaf_quasiIso_restrict`
(node `lem-pc-cech-sheaf-local-quasi-iso`). In the current repository that theorem has
a Lean proof using the still-open `AlgebraicGeometry.augmented_cech_sheaf_restrict_kernel`
and `AlgebraicGeometry.cech_sheaf_restrict_exact_positive`; these are existing holes,
not added by this delivery. This delivery adds no other holes.

The new statement is strictly a construction part of the argument. Without a cover the
augmentation need not be a quasi-isomorphism: an empty family on a nonempty scheme yields
a zero Cech complex, and a nonzero F has a noninvertible augmentation. The cover hypothesis
is used only in the fully proved global homology argument. Edge cases checked in words:
empty index types give empty products and vacuous coordinate equations; zero F gives zero
terms; empty opens and empty schemes have zero sections; infinite families use categorical
products, with no stalk-product interchange or finite-cover assumption.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.CechSheafConstruction`.
Its node `lem-pc-cech-sheaf-construction` and declaration
`AlgebraicGeometry.exists_augmented_cech_sheaf_complex` are no longer needed by this item's
proof. They do not guarantee the displayed local scalar equation. The new linear
construction replaces that dependency, rather than using an arbitrary comparison from the
old existence theorem. This does not claim that the old module is unreachable from every
other target branch.

Removed the two duplicate private helper declarations from this delivery. Their copies
in `Sheaf.AlgebraicGeometry.CechSheafResolution` are private, so importing that module
would not expose them. The ordinary resolution module is not needed by this proof;
isomorphism globalization uses the existing public flat-cover theorem instead. No helper
is renamed or restated, and no new node or hole replaces either helper.

Retained `Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso` and its node. Retained all three
public statement imports. No other original proof dependency is pruned. The unit record
`sk-thm-picard-coherence` has empty realized lists, and the Cech-to-derived route of its
proof is preserved: construction, local exactness, then global exactness.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private statements already present in
`CechSheafResolution`. Although those private declarations cannot be called by an
importer, their mathematical content should be reused through the existing public
flat-cover reflection theorem. This repair removes both duplicate declarations and
uses that theorem for the actual augmentation's homology maps. The earlier second
reading predates this proof repair and has been archived in the sandbox scratchpad;
a fresh second reading is needed before delivery.

The original proof plan's first step appealed to the construction inside
`lem-pc-cech-sheaf-construction`; its stated conclusion supplies only global-ring-linear
presheaf comparisons. Local scalar compatibility cannot be extracted from an arbitrary
such comparison. The additional construction assertion is therefore stated explicitly
and does not depend on the old theorem. Searches of both library roots and the DAG found
no existing theorem that supplies it. LeanFinder returned scalar-action/sheafification
results; Loogle identifies cechComplexFunctor, which requires an already constructed
sheaf-valued functor; grep confirms that the generic functor does not supply this
construction. LeanSearch was unavailable (Internal Server Error), recorded as unavailable.

The citation Tag 01FJ is a comparison of ordered and alternating Cech complexes, not the
full module-sheaf resolution. The delivered docstrings cite Stacks Tag 02FU instead, whose
construction and insertion-homotopy argument directly match this proof. Its construction
works without a cover; only its exactness proof uses the cover. No statement is disputed
or changed. The existing local exactness lemma lies in the semicon unit and is retained
as the same generic tool already used by the item's original plan.

## New nodes

`lem-pc-linear-cech-sheaf-construction`, at
`dag/nodes/sec-picard-framework/lem-pc-linear-cech-sheaf-construction.json`, records
`AlgebraicGeometry.exists_augmented_linear_cech_sheaf_complex`. Its source is the displayed
construction in blueprint lem-pc-cech-resolution and Stacks Tag 02FU. It inherits the
item's chapter and unit. Its proof spells out the opposite-opens module-sheaf functor,
product comparisons, augmentation, open-direct-image term identification and local scalar
formula, without an exactness claim. Searches and empty/zero/infinite edge cases are
recorded. The new node and theorem are absent from the library base. No existing signature,
definition or visibility is changed, and no change record or forced adaptation is needed.


## Second reading by S3

1. Compared the delivered resolution module with the repository using diff and an exact
   signature comparison: the existing theorem signature is byte-for-byte identical.
   The three public imports and visibility are unchanged. Only proof imports, source
   comments and the proof body differ. No definitions, adaptations or interface changes
   are delivered, so no change record is needed. Verdict: pass.
2. Compiled both delivered modules in import order through lcompile.py: no errors or
   warnings. Independently compiled a scratch copy of the repaired resolution with
   axiom probes for both delivered theorems and the flat-cover reflection theorem.
   The two delivered theorems use only propext, Classical.choice, Quot.sound and sorryAx;
   the reflection theorem uses only the three allowed axioms. The sole delivered sorry
   is the named construction theorem, with a source, full proof docstring and node.
   No forbidden declaration or hollow definition is present. Existential witnesses are
   eliminated only inside the theorem proof. Verdict: pass as a decomposition, not a
   completed axiom-free resolution.
3. Read the construction statement and docstring clause by clause. Checked empty index
   types (zero product terms and vacuous coordinates), empty opens/schemes, zero F,
   singleton families and infinite families; the construction needs no cover and
   asserts no exactness. It is strictly a construction part, not a renamed resolution.
   Verified the direct-image product construction and insertion argument against
   [Stacks Tag 02FU](https://stacks.math.columbia.edu/tag/02FU).
   Repeated LeanFinder, Loogle and grep searches with different construction terminology,
   and searched both library roots. The ordinary construction and its concrete functor
   exist, but the comparison theorem exports no local scalar equation and its canonical
   degree comparison and projection equation are private. Thus its arbitrary existential
   comparison cannot supply the new scalar clause; closing the new theorem is not a
   brief application of the existing interface. No exact duplicate was found. Verdict:
   the single split-off statement is true, needed and strictly simpler.
4. Read the proof from the resolution downward: construction, the existing local
   quasi-isomorphism theorem, restriction/homology naturality and the proved public
   flat-cover isomorphism reflection theorem. The covering hypothesis supplies joint
   surjectivity, including the empty-scheme case, and no quasi-coherence assumption is
   introduced. All added imports are proof imports; no duplicate generic helper remains.
   Compared the original proof_deps: only lem-pc-cech-sheaf-construction is removed, and
   it and its module are listed under No longer needed. Checked the unit's statement,
   step and empty realized lists: the Cech-to-derived route is retained. Verdict: pass.
5. Compared existing node records: only proof, proof_deps and proof_origin changed.
   Checked the declaration/module records of all six proof dependencies and the union
   of the proof-step uses. The new node has source, searches, creation, blueprint,
   chapter/unit and verbatim Lean statement records; its proof makes no exactness claim.
   The recorded dependencies match the actual reduction. Verdict: pass.

Second reading changed the report to reflect the current repository: the local
quasi-isomorphism theorem is now proved from two existing lower holes, rather than
itself being a body hole. Added this independent review and fresh search/axiom evidence.
No Lean proof or statement required repair. One original body hole is closed and one
construction hole is added: this remains a decomposition with zero net body-hole gain.
