## What changed

Kept the signature and docstring of AlgebraicGeometry.algebraize_finite_over_proper unchanged.
Replaced its hole by a complete Lean proof: obtain the algebra reduction data, use the existing
exists_affine_structure_algebra to choose an affine realization, obtain its finite/proper
properties and the cartesian reduction squares, then construct e and q and prove both projection
equations and transition compatibility using the pullback API. All new imports in the original
module are proof-only. The second reader restored the proof-plan imports of the three
new holed modules as plain imports, retaining the lower dependencies in the closure. Three new modules state strictly separate parts of the Stacks 09ZT
argument; each contains one named theorem with a source and full proof in words. Updated the
original DAG proof and added the three corresponding nodes. No definitions, existing signatures,
public imports of the original module, or target statements changed.

## Proved and sorry left

Closed the original direct hole in AlgebraicGeometry.algebraize_finite_over_proper
(lem-weil-pbc-algebraize-finite-over-proper). Its combining proof has no sorry. This is a
DECOMPOSITION, not a completed proof of algebraization: one upper hole was replaced by three
lower holes, for a net increase of two direct holes in this delivery.

The delivery adds exactly these holes:

- `AlgebraicGeometry.algebraize_finite_structure_algebra` (lem-weil-pbc-algebraize-finite-structure-algebra), in `Sheaf.Paper.AlgebraizeFiniteStructureAlgebra`.
- `AlgebraicGeometry.coherent_algebra_affine_finite_proper` (lem-weil-pbc-coherent-algebra-affine-finite-proper), in `Sheaf.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper`.
- `AlgebraicGeometry.affine_algebra_reductions_cartesian` (lem-weil-pbc-affine-algebra-reductions-cartesian), in `Sheaf.AlgebraicGeometry.AffineAlgebraReductionsCartesian`.

The algebraization lemma concludes algebra-sheaf data only, without a global scheme, finite
morphism or proper global scheme. The finiteness/properness lemma concerns an already supplied
affine realization, with no completion, formal system or recovery conclusion. The recovery
lemma has no Noetherian, coherent, complete-base or properness assumptions and produces maps
and cartesian squares for an existing affine realization, not the target's finite proper scheme.
The construction of the relative spectrum reuses the already named theorem
AlgebraicGeometry.exists_affine_structure_algebra; its pre-existing hole is not added here.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`
- `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`
- `Sheaf.AlgebraicGeometry.GrothendieckExistence`
- `Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.TensorPullbackTilde`
- `Sheaf.Topology.PresheafModuleStalkFunctor`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`

These were removed from the upper combining proof, not asserted globally obsolete: their
mathematical roles remain in the three intermediate nodes' proof plans. The full relative-spec
anti-equivalence is unnecessary for choosing Y in the upper proof; the narrower existing
RelativeSpectrumAffineRealization theorem suffices there. AffineMorphismRelativeSpec remains
needed below for the affine chart and recovery arguments. No whole original dependency node
or module is established globally unnecessary by this decomposition, so global pruning is none.

The complete old `proof_deps` removed from the upper node (relocated into the new
intermediate plans, not globally pruned) are:

- `lem-pod-separated-finite-type-base-change`
- `def-pc-module-pullback`
- `lem-weil-pbc-affine-morphism-relative-spec`
- `lem-weil-pbc-finite-pushforward-coherent`
- `lem-weil-pbc-affine-pushforward-base-change`
- `prop-weil-pbc-grothendieck-existence`
- `lem-weil-pbc-finite-morphism-permanence`
- `def-weil-pbc-module-stalk`
- `lem-weil-pbc-closed-subset-proper-over-base-properties`
- `lem-weil-pbc-module-support-proper-over-base`
- `def-weil-pbc-closed-subset-proper-over-base`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-tilde-pullback-base-change`
- `lem-weil-pbc-module-tensor-symmetric-monoidal`

## Where the brief, the DAG or earlier work was wrong

No false original statement or source error was found. The existing proof plan is valid but
its current signatures expose module pullback and base-change multiplication/unit compatibility,
not a shared algebra-sheaf pullback functor. The new interface avoids inventing such a definition:
it records actual O_X-algebra maps to r_n,*O_Yn and pins their reductions by surjectivity and
an exact kernel formula on every affine open. Equality on all opens pins the transition maps.
The original support/unit argument is preserved: O_X need not have proper support, so algebraize
the unit through O_X/I_Z, not by applying full faithfulness directly to O_X.

Read Stacks coherent.tex from the available local source copy at
/home/ubuntu/c1-stacks-review/coherent.tex, especially Lemma 09ZT (lines 7887--7926),
Remark 088F (lines 7780--7817), and Lemma 0CYS. The repository's literature source tree is
not materialized on this machine; the available source copy supplies the cited text.
LeanSearch attempts returned HTTP 500 and are explicitly recorded as unavailable without an
absence verdict; LeanFinder and source grep returned no exact match. Searches of the whole
blueprint for algebra structure, coherent algebra, quotient algebra and relative spectrum found
no duplicate of these intermediate statements. The existing algebra and relative-spectrum
objects are reused, and no new definition node is introduced.

Edge cases checked mathematically: for empty X or an empty affine U all section rings are zero
and all formulas become the zero quotient; the zero algebra yields an empty relative spectrum,
finite and proper. For I = 0 the reductions are unchanged X and the algebra maps are isomorphisms
on every affine chart. For the generic recovery statement, j_n = identity gives kernel zero
and forces b_n(U) bijective; an empty closed subscheme gives the whole kernel ideal and an empty
reduction. Properness cannot be inferred merely from a proper special fibre (a component disjoint
from the special fibre would be invisible); the finiteness/properness intermediate retains the
proper-support condition and proves properness via a supporting closed subscheme.

The unit sk-thm-p1 and its realized statement/steps are unchanged. These new nodes inherit that
unit and group only the existing 09ZT proof steps below it.

## New nodes

`lem-weil-pbc-algebraize-finite-structure-algebra` is stated in `Sheaf.Paper.AlgebraizeFiniteStructureAlgebra` as `AlgebraicGeometry.algebraize_finite_structure_algebra`. It groups original proof steps 1--10 and the affine quotient characterization. Its source, statement, proof steps and dependencies, blueprint ancestor, three search attempts, and verbatim Lean signature are recorded in its node.

`lem-weil-pbc-coherent-algebra-affine-finite-proper` is stated in `Sheaf.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper` as `AlgebraicGeometry.coherent_algebra_affine_finite_proper`. It groups original proof steps 11 and 13 (finite and properness tests). Its source, statement, proof steps and dependencies, blueprint ancestor, three search attempts, and verbatim Lean signature are recorded in its node.

`lem-weil-pbc-affine-algebra-reductions-cartesian` is stated in `Sheaf.AlgebraicGeometry.AffineAlgebraReductionsCartesian` as `AlgebraicGeometry.affine_algebra_reductions_cartesian`. It groups original proof steps 12 (recovering the reductions from algebra maps). Its source, statement, proof steps and dependencies, blueprint ancestor, three search attempts, and verbatim Lean signature are recorded in its node.

No change record is needed: existing statements and definitions are unchanged.

## Second reading by X3

1. **Existing API preserved: pass.** Read the repository and sandbox modules with
   `diff -u`. The only changes in the original module are plain proof imports and the
   body of `AlgebraicGeometry.algebraize_finite_over_proper`. Independently compared
   its signature byte for byte through `:= by`: identical. Its docstring and public
   imports are unchanged. There are no changed definitions or target statements and
   therefore no statement-change record is required.

2. **Proof and trust check: pass as a decomposition.** Compiled all four modules in
   import order using `lcompile.py --all`, including after the import repair; all pass
   without errors or warnings. Read the combining proof: `hi` is the first projection
   of the transition map, `hw` follows from the original cartesian square, and the
   resulting `v` squares supply `isoPullback.inv`. The final `hom_ext` checks separately
   the Y projection (using `hvg`) and the Xn projection (using `hcart.w`), so it proves
   the full transition equation, not just that each reduction is isomorphic.
   Scratch copies with `#print axioms` for all four named declarations compile and
   show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter
   is expected from the three reported open intermediates and the existing affine
   realization theorem. The only source holes are the three public named theorems
   reported above; no forbidden declaration or hole in a definition occurs. Scratch
   copies were removed. This is one closed upper hole, three added lower holes,
   not a completed axiom-free algebraization theorem.

3. **New statements and sources: pass.** Read the local Stacks `coherent.tex`,
   Lemma 09ZT (`lemma-algebraize-formal-scheme-finite-over-proper`), Remark 088F
   (`remark-reformulate-existence-theorem`), and Lemma 0CYS
   (`lemma-module-support-proper-over-base`). Also read the actual signatures of
   `grothendieck_existence`, `affinePushforward_baseChange_algebra`,
   `isCoherent_pushforward_of_isFinite`, `isCoherent_unit_of_finite_to_locallyNoetherian`,
   `module_support_proper_over_base`, `affine_morphism_relative_spec`,
   `quasicoherent_finite_type_affine`, and
   `isCoherent_iff_isQuasicoherent_and_isFiniteType`.
   The algebra intermediate retains precisely the complete Noetherian base,
   separated finite-type X, finite system, cartesian transitions and proper first
   fibre of 09ZT. Its additional `hw` is a consequence of the given square, supplied
   by the combining proof. It concludes algebra data and quotient maps, not a scheme.
   The plan uses finite direct image for coherence, algebra base change for compatible
   products and units, and the existence theorem only on modules with proper support;
   the unit is lifted through O_X/I_Z. Tensor and tilde clauses supply the affine
   quotient kernel formula. The finite/proper intermediate instead starts with an
   existing affine realization and uses coherence for finite sections, then 0CYS for
   an annihilating proper Z. The quotient B/JB = B makes Y times_X Z -> Y an
   isomorphism; finite base change and composition give properness without assuming
   f separated or X globally Noetherian. The recovery intermediate needs only affine
   morphisms and closed immersions: b_n and α give chart morphisms, the kernel
   identifies their charts with the base change, and hcompat gives global equality.
   These are separate strict parts of the argument and none relabels the upper item.
   All have source/proof docstrings and matching nodes. Checked empty X, empty affine
   opens and zero algebras; identity j gives kernel zero and bijective section maps;
   empty closed reductions give the whole ideal. For I = 0 the reductions are
   unchanged. Properness is proved from proper support, not from proper special fibre
   alone. No hole is elementary enough to close in a few minutes with the present API.
   Independent LeanFinder searches used the phrases 'module finite direct image
   structure sheaf', 'surjections of sheaves of algebras whose kernel is the ideal
   of a closed immersion', and 'Lift multiplication and unit ... full faithfulness
   of completion'. Results were the affine finite criterion, closed-immersion
   section surjectivity, and ring-level adic lifts respectively, not exact matches.
   `rg` across lean/Sheaf, lean/WeilConjectures and the upstream checkout found the
   reused interfaces but no duplicate algebraization or cartesian recovery theorem.

4. **Route and pruning: repaired, pass.** The root proof takes the existing
   `exists_affine_structure_algebra` rather than introducing another relative Spec.
   Its four new imports are proof-only and each is used. The three open intermediate
   plans still require their existing lower lemmas, so restored those modules as
   plain imports in the appropriate new files. This avoids treating still-needed
   Grothendieck existence, affine correspondence or tensor machinery as pruned.
   Expanded `No longer needed` to enumerate every old root `proof_deps` absent from
   the new root proof, explicitly identifying them as relocated rather than globally
   obsolete. Read `dag/units/sk-thm-p1.json`: neither the root nor any old removed
   dependency is itself a realized statement or step of that unit; its realized
   curve-calculation and strict-local route is unchanged. Global pruning is none.

5. **DAG/Lean agreement: pass.** Read all four node files alongside their modules.
   Independently checked every recorded Lean signature against its module after
   whitespace normalization, and every `proof_deps` equals the union of step `uses`.
   Root steps correspond to `hi`/`hw`, algebraization and affine realization,
   finite/properness and closed immersion instances, reduction squares, and the
   pullback assembly. New nodes retain chapter/unit, sources, search attempts
   (the failed LeanSearch is recorded as unavailable), blueprint ancestor and exact
   proof-step place, created record, and complete Lean record. The proper-support
   and coherence hypotheses required by the cited statements are supplied in their
   respective plans. No changes to an existing node outside the allowed proof fields
   were made by this reading.

Second reading changed only proof-plan imports in the three new holed modules and
this report (complete relocated dependency list and this independent review).
