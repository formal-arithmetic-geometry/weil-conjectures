## What changed

Replaced the sole sorry in
`Sheaf.Algebra.Homology.FirstLocalizationCohomologyBaseChange` with a complete
proof from two strictly smaller class-level localization assertions. The original
statement, universe parameters, public imports, and existing docstrings are unchanged.

Added `LocalizationModelSemilinear`: a real definition of the canonical B-linear
model comparison, a proved private first-factor scalar lemma, and the proved
`RingTensorCohomology.localizationModelMap_smul`. The proof establishes the unit's
scalar square termwise by tensor balancing, applies naturality of the universal
comparison, uses both models' `cohomologyIso_smul`, and extends from pure tensors
by tensor induction and B-linearity. There is no data choice from an unproved theorem.

Added `LocalizationModelKernel` and `LocalizationModelDenominators`, one remaining
public theorem in each. The first supplies an annihilator in S only for a class
mapped to zero. The second supplies a numerator and denominator for an arbitrary
target class. Neither asserts a tensor-extension isomorphism or the complete item.

The upper proof constructs the coefficient algebra along the actual tensor map,
proves that its target ring is a localization using
`IsLocalization.tensorProduct_tensorProduct`, and bundles the canonical map as a
linear map. Invertibility of denominator actions comes from the localized ring.
The two lower statements supply the surjectivity and equality-detection fields
of `IsLocalizedModule`; the latter is applied to x-y. Finally
`IsLocalizedModule.isBaseChange`, `IsBaseChange.equiv`, and `equiv_tmul` construct
the required isomorphism and establish its exact generator formula.

All four modules were checked through lcompile.py. The final deliver3.py dry run
checks the same modules with declaration/axiom probes. No global build was run.

## Proved and sorry left

Closed the item's one original hole:
`RingTensorCohomology.exists_firstLocalization_cohomology_baseChange`
(node `lem-pc-first-localization-cohomology-base-change`).

Additionally proved `RingTensorCohomology.localizationModelMap_smul`
(node `lem-pc-first-localization-cohomology-semilinear`) and its private helper
`localizationModelMap_left`.

Two holes added and left, each the entire proof of its public named theorem:

- `RingTensorCohomology.localizationModelMap_kernel`
  (`lem-pc-first-localization-cohomology-kernel`).
- `RingTensorCohomology.localizationModelMap_denominators`
  (`lem-pc-first-localization-cohomology-denominators`).

This is a decomposition, not a sorry-free proof of the complete mathematical
localization theorem: one upper hole is closed and two lower holes are added.
The canonical-map definition and all proofs combining the statements are complete.

## No longer needed

No original import removed, and no whole module claimed pruned. Removed the
unneeded Localization.Basic import from the new scalar-compatibility module;
the two new localization statements import it where their statements need it. The original
file had no proof-dependency imports of the balanced model or action-naturality
modules. These are now planned dependencies of the two smaller localization
statements, rather than direct dependencies of the upper proof.

The scalar-compatibility proof does not need
`lem-pc-balanced-derived-tensor-model` or
`lem-pc-derived-tensor-action-naturality`: it uses the supplied models' action
fields directly. Those nodes remain needed in the lower proof plans. Likewise
`lem-weil-pbc-localization-flat`, `lem-weil-pbc-localization-module-exact`, and
`lem-weil-pbc-localization-tensor-product` remain in those plans. Unused proposed
proof imports of their modules were removed from the two new sorry modules.
No import of any downstream FirstLocalizationMap/Comparison/Naturality module
was added; those modules depend on the item and would create cycles.

## Where the brief, the DAG or earlier work was wrong

The planned balanced-model/action-naturality declarations are already proved,
but their signatures concern derived tensor in the second variable with output
in D(A). They do not directly provide the first-variable scalar-extension
comparison for arbitrary universal-counit B-linear models. The missing interface
is made precise as the two class-level criteria. It is not a failure caused by
using dependencies that still have sorry.

Sources read: Stacks Project Tags 06Y6 and 0DJ8, especially the affine cohomology
localization identity in the latter's proof. The model-specific transport and the
separate class-level criteria are explicitly agent-written consequences of that
identity. LeanFinder and Loogle found module-localization interfaces and a
cotangent special case, not this arbitrary-model statement; repository/Mathlib
and blueprint searches found no duplicate. LeanSearch returned Internal Server
Error, recorded as unavailable.

Edge cases checked mathematically before stating the lower results: Q=0; B=0;
identity localization; S containing zero; and nonflat A over R. For zero in S,
the zero denominator supplies the kernel equation and the fraction equation
(the target is zero). Identity localization reduces to the invertible universal
model comparison. Resolving B over R avoids assuming that Q is R-K-flat or
that A is R-flat. There is no compatibility assumption on either map to D.
The unit record sk-thm-picard-semicon has no realized attachment for this node;
its statement and route are unchanged, as are all chapter/unit files.

## New nodes

`lem-pc-first-localization-cohomology-semilinear` records the canonical map and
its proved tensor-coefficient compatibility in
`Sheaf.Algebra.Homology.LocalizationModelSemilinear`. It requires no localization
hypothesis and contains no sorry.

`lem-pc-first-localization-cohomology-kernel` records the S-torsion conclusion for
a single class in the kernel, in
`Sheaf.Algebra.Homology.LocalizationModelKernel`. Its docstring and proof plan
explain the K-flat computation, exact localization of boundaries, and natural
transport to the supplied models.

`lem-pc-first-localization-cohomology-denominators` records the numerator and
denominator equation for a single target class, in
`Sheaf.Algebra.Homology.LocalizationModelDenominators`. Its proof plan explains
clearing a denominator in a term and a further denominator killing the
numerator's differential, then the same natural model transport.

The existing parent node now follows the actual Lean assembly. No change record
is needed: no existing definition, signature, or public-import visibility changes.

## Second reading by C2

1. Compared the delivered parent module with the repository version. Existing declarations and
   signatures are unchanged; the parent proof only replaces its original `sorry`, while the
   additional modules contain the newly declared split statements. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all` and recompiled the parent after
   dependency generation. The only remaining `sorry`s are the two named public split theorems;
   there are no axioms, unsafe declarations, hollow definitions, or forbidden implementation
   commands. Verdict: pass.
3. Checked the semilinear statement and the two localization criteria against the canonical map
   types and localization module interface, including zero and identity localizations. The new
   statements are strictly smaller than the parent and their docstrings give proof sources and
   complete proof plans. Repository searches found no duplicate declarations. Verdict: pass.
4. The parent follows the stated module-localization route: tensor-product localization,
   denominator surjectivity, kernel equality detection, and `IsLocalizedModule.isBaseChange`.
   The unit route remains unchanged; no downstream localization comparison module is imported.
   Verdict: pass.
5. DAG nodes, Lean declaration names and statements, proof dependencies, and proof origins were
   checked against the actual files. The report records the two split holes and the removed
   proof-only import rationale. Verdict: pass.

Changed only the parent proof, added the semilinear definition/theorem module and the two named
split-theorem modules, added their DAG nodes, and recorded this second reading. No existing
statement or public import was altered.
