## What changed

Replaced the stale sandbox restatement with a genuine two-obligation decomposition of
`AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_invariance`, preserving its complete
signature. The proof obtains cochain realizations for D and E, compares their actual derived
morphisms by the proved upstream H-zero injectivity theorem (using the existing connectivity
lemma), and rewrites the two output classes with the evaluation diagram and the assumed
input-class equalities. The original module contains no `sorry`.

Added `Sheaf.Paper.ModuleCupResolutionRealization`: explicitly extends complexes by zero,
constructs localized augmentations from the extension/single isomorphism, proves those
augmentations invertible, specifies the section formula for a cochain realization, and defines
its transported derived morphism as an actual composite. Its one deferred theorem constructs a
realization and normalizes its H-zero map. No object is chosen from a deferred existence proof.

Added `Sheaf.Paper.ModuleCupRealizationEvaluation`: its deferred theorem gives the bilinear
cohomology evaluation family for *every* derived morphism and evaluates every realized cochain
pairing. The family is obtained only as a local witness in the target's theorem proof; no public
definition chooses an arbitrary witness. The independent sheaf instances have explicit distinct
names to avoid the anonymous-instance collision with ModuleCupNaiveDerivedCompatibility.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_invariance`.
This is a decomposition, not a sorry-free proof: one original hole closed and two new holes added
(net holes +1, before any pruning).

New holes, each the complete proof of a public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_realization`
  (node `lem-sc-module-cup-resolution-realization`). This is the cochain realization and H-zero
  normalization, before any comparison of different resolutions or positive-degree products.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_realization_evaluation`
  (node `lem-sc-module-cup-realization-evaluation`). This is the global evaluation diagram for
  arbitrary derived morphisms, without H-zero normalization or input-class equality assumptions.

Also proved `CupAcyclicResolution.derivedAugmentation_isIso` from extension of quasi-isomorphisms
and localization. All new data definitions have actual constructions and no deferred proofs.
The target's real comparison step uses
`DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`, not a renamed invariance hole.

## No longer needed

Removed the direct proof imports of `Sheaf.Paper.ModuleCupHZeroIdentification`,
`Sheaf.Paper.ModuleCupCanonicalHZeroIdentification`, and
`Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` from the item's module. They are still needed
below the two new obligations and remain in the import closure; no existing mathematical module
or node is claimed globally pruned. The unchanged support files copied by the earlier worker
were removed from the delivered set, and the earlier same-statement `_core` and reflexivity
helpers are not delivered. The new argument does not depend on the stale
`lem-sc-module-cup-resolution-invariance-core` sandbox node.

The complete old direct `proof_deps` removed from the invariance node are
`def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product`,
`def-sc-module-cup-resolution-data`, `def-sc-ringed-space-module-cohomology`,
`lem-sc-module-cup-hzero-identification`, `lem-sc-module-cup-canonical-hzero-identification`,
and `lem-sc-module-cup-naive-derived-compatibility`. They remain below the new obligations
or in the statement dependencies; none is claimed globally pruned.
Removed redundant public imports of `Sheaf.AlgebraicGeometry.DerivedTensorStructure`
and `Mathlib.Algebra.Homology.Embedding.CochainComplex` from the new evaluation module:
its public realization import already exports both. The realization module explicitly
imports `ModuleCupHZeroIdentification` privately for its recorded proof plan.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox's `_core` had the same binders, hypotheses, and conclusion as the original
statement, and its report's claim of subtype extensionality did not match the code. The dry run
rejected it as a restatement. This delivery instead realizes the original node's three steps:
cochain realization/normalization, the actual proved H-zero injectivity step, and global evaluation.
Neither new obligation states cross-resolution invariance. No unit route, target statement,
existing definition, or support-module signature has changed.

Checked the new statements at p=q=0 (augmentation pairing gives ordinary tensor), at p=0 or q=0
(the tensor differential sign is +1 in the first degree-zero factor), for zero coefficients and
empty schemes (zero section modules), and without flat coefficient hypotheses (the comparison is
from derived tensor to ordinary tensor, never an assumed tensor quasi-isomorphism). Negative
integer-degree terms are extensions by zero. The evaluation theorem allows arbitrary f, including
the zero map; it does not assume H-zero normalization, and the realized map supplied by each D
is an explicit composite. These are mathematical edge-case checks, not additional axioms.

Mathlib searches were rerun through msearch.py (LeanSearch unavailable; LeanFinder, Loogle, and
source grep successful). The searches found tensor/extension and Ext machinery, but no existing
sheaf resolution-pairing realization/evaluation theorem. The existing H-zero injectivity theorem
was read and used directly. Compilation and the final deliver3.py dry run verify the complete set.

## New nodes

`lem-sc-module-cup-resolution-realization`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-resolution-realization.json`, records the explicit
integer extension and derived map and the missing construction/H-zero-normalization step.
Its module is `Sheaf.Paper.ModuleCupResolutionRealization`.

`lem-sc-module-cup-realization-evaluation`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-realization-evaluation.json`, records the global
cohomology evaluation family and the missing evaluation diagram. Its module is
`Sheaf.Paper.ModuleCupRealizationEvaluation`. Both nodes carry source, complete proof steps,
actual search records, and verbatim Lean signatures. The existing invariance node's proof fields
now follow the compiled argument. No change record is needed: only the item's proof/private
imports and new modules/nodes change; every existing public signature and definition is preserved.

## Second reading by F4

1. **Unchanged interface.** Compared the delivered invariance module with the repository
   version using diff, and compared the JSON records field by field. Its complete existing
   signature, all four hypotheses ha/hb/hc/hc', universe, visibility and original docstring
   are unchanged. The sole existing node changes only proof/proof_deps/proof_origin.
   The other two Lean modules and nodes are new; no existing definition or target changed.

2. **Proof and data.** Read every delivered declaration. The target uses the injective part
   of the upstream proved homologyFunctor_map_bijective_of_isLE_of_isGE at zero,
   hD₀.trans hE₀.symm, followed by the two evaluation equations and rewrites by ha/hb.
   The only two delivered sorries are exactly the named realization and evaluation theorems.
   integerComplex, derivedAugmentation, Realizes and derivedMap are actual constructions;
   no arbitrary existence witness enters a data definition. The existential witnesses tD,
   tE and evaluation are eliminated only inside the proposition proof. Checked forbidden
   declarations and line widths. Compiler and axiom results are recorded below.

3. **New obligations and sources.** Read Stacks Section 20.31 (0FKU), especially its
   shifted-unit construction, Lemmas 20.31.1/20.31.3 and the global cohomology diagram;
   also the flasque discussion in 0FKV and the derived tensor construction in 06YH.
   The realization lemma concerns one cochain map and its degree-zero normalization.
   Restriction gives sheaf morphisms, the signed Leibniz identity supplies the differential
   equation, and augmentation_pair supplies normalization. The evaluation lemma is a
   bilinear family indexed by an arbitrary derived morphism and the diagram for one
   realized cochain map. Neither assumes equality of input classes or concludes equality
   for two resolutions. Together with the independently proved H-zero injectivity step
   they give a real decomposition, not a restatement. Neither new hole is a few-minute
   exercise: realization requires tensor/sheaf/total-complex assembly, and evaluation
   requires the cohomology-to-derived-Hom comparisons.
   Checked p=q=0 against augmentation_pair, p=0 and q=0 against the signed differential,
   zero coefficients and the empty scheme, and nonflat coefficients: no inverse of a
   naive tensor of augmentations is used. Negative terms are zero by integer extension.
   A zero derived map gives zero evaluation in the shifted-unit construction.
   Independent LeanFinder, Loogle and source searches used different phrases from the
   first worker. They found presheaf tensor maps, ιTensorObj and mapBifunctorDesc,
   but no theorem with either new obligation's full statement. Source grep in both
   lean/Sheaf and the upstream algebraic-geometry/topology modules found no replacement.
   The complete word proofs and matching nodes are present.

4. **Route and pruning.** The three-step realization/comparison/evaluation route is kept.
   Read sk-prop-av-cube.json: its realized fields are empty and this item is a lower
   auxiliary node, so no realized unit step is bypassed or rewritten. Connectivity and
   the existing proved upstream H-zero injectivity remain used. All seven removed old
   direct proof_deps are now explicitly listed under No longer needed; those still in
   the transitive closure are not claimed pruned. Removed two redundant public imports
   from the new evaluation module and added a private import for the realization
   lemma's already recorded H-zero proof dependency.

5. **DAG agreement.** For all three nodes, the union of proof-step uses equals proof_deps.
   Checked new node ids, sources, creation records, chapter/unit, blueprint ancestry,
   search records and verbatim Lean signatures. The existing node describes exactly
   the two realization applications, connectivity/injectivity and the evaluation calc.
   Clarified the evaluation node's shifted degree as minus (p+q).

Changes in the second reading: completed the pruning inventory; removed redundant imports;
added missing module blueprint tags and the planned private H-zero import; clarified a
shift degree in the node; cleared stale sandbox support build outputs before validation.
Performance repairs and the final validation results follow below.

The realization module initially timed out. Kept type transparency for type checking,
made the existing local data instances instance-reducible, and cached the existing Qh
monoidal property and Q lax monoidal instance. The augmentation and derivedMap types
now use Q of the actual single complexes, definitionally the same objects as the
single derived functors. The new realization statement locally names F₀, G₀ and the
same canonical tensor comparison once; its obligation is unchanged by let reduction.
The node's verbatim signature was updated. No old declaration signature was changed.
The normalized full realization module compiles successfully with the prescribed tool.

The full-set compile caught an instance-indexing mismatch in the target proof after
normalizing the new helper types. Added a proof-only change of hLE to the definitionally
equal Q-single source before registering it as an instance; connectivity itself still
comes from the same existing proved theorem. Updated the node's step accordingly.

Final verdict for points 1–5: pass, with the two explicitly recorded open obligations.
All three modules compile against fresh local outputs. The scratch-copy #print axioms
checks show only propext, Classical.choice and Quot.sound for integerComplex,
derivedAugmentation, derivedAugmentation_isIso, Realizes and derivedMap. The two
new deferred theorems and moduleCup_resolution_invariance additionally show sorryAx,
as expected for this decomposition; no other axiom appears. The delivery tool's
all-declaration axiom probes and preflight also pass. The prescribed no-push dry run
printed OK at f7b562023f, with review class CODEX because it adds modules/nodes and
retains the two named obligations. One original hole closed, two added; net holes +1;
no globally pruned module. The independent reading changes the imports, module tags,
pruning inventory, shift-degree wording and elaboration of the new helper interfaces,
plus the target's proof-only connectivity-instance normalization.
