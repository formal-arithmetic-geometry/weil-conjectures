## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.FlatBaseChangeAffineSource with a
complete Lean proof from the existing cohomology source comparison, a new normalized
affine Leray comparison, ordinary higher-image quasi-coherence, and affine tensor-pullback
sections. The original theorem signature and docstring are unchanged. All four existing
public imports are preserved.

The proof obtains a natural family E from exists_moduleCohomology_source_comparison,
then constructs eH by composing its restricted-module component with H.mapLinearEquiv
for Mathlib restrictFunctorIsoPullback. The new affine Leray lemma takes this already
available natural family as input. It has no S', g, J, W, tensor product or flatness
hypothesis, and concludes only the A-linear identification before scalar extension.
The parent transports the existing affine sections map through tensor commutation,
proves its B-linearity using its scalar formula, extends the Leray equivalence by B with
TensorProduct.AlgebraTensorModule.congr, and composes the maps. Bijectivity follows from
three bijections; normalization follows from the two pure-tensor/class equations.

Added one module, Sheaf.AlgebraicGeometry.AffineCohomologySectionEquiv, and its node.
Updated new-flat-base-change-affine-source proof, proof_deps and proof_origin to match
these actual dependencies. The unit's statement and proof route are preserved.
The local transparency options and heartbeat allowance are scoped to the original
proof; the explicit class-map comparison expands several homology transports.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_source
(new-flat-base-change-affine-source). The original module has no sorry left.

Added and still sorry: AlgebraicGeometry.Scheme.Modules.exists_affine_cohomology_section_equiv
(new-affine-cohomology-section-equiv), in Sheaf.AlgebraicGeometry.AffineCohomologySectionEquiv.
This is exactly the normalized affine Leray step before base change. Its source and
complete mathematical proof are in its docstring and node. One hole closed, one added:
a decomposition, not a net reduction of the target closure's holes. Existing sorry-bearing
proof dependencies, including ordinaryHigherImage_isQuasicoherent and the affine sections
bijectivity infrastructure, are reused without editing their modules.

Both delivered modules compile through lcompile.py in import order. The original
signature was compared with the base using stage3_delivery.diff_module: no statement
changes. The natural source comparison is constructed from existing declarations;
no definition chooses arbitrary data from a new existence theorem, and no definition,
axiom or private sorry is added.

## No longer needed

Removed direct proof imports from the original module:
- Sheaf.AlgebraicGeometry.LerayDegenerateSections
- WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
- Sheaf.Paper.HigherDirectImagePresheaf
- Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural

The first three remain proof-plan dependencies of the new normalized Leray module;
they are relocated, not eliminated from the target closure. The natural abelian
comparison is already used transitively by ModuleCohomologySourceComparison, so its
separate direct import is redundant. No existing DAG node or module is claimed to
be globally pruned. The pullback-affine-sections-bijective node remains used through
ModulePullbackAffineSections; it was not bypassed. All other original dependencies
are retained by the new proof or its lower normalized Leray step.

Old direct proof_deps removed from the parent node, accounted for individually:
- def-weil-pbc-flat-base-change-open-choices: retained in the new normalized Leray
  node and in the parent's unchanged statement dependencies.
- lem-pc-affine-vanishing: retained in the new normalized Leray node.
- lem-pc-leray-degenerate-sections: retained in the new normalized Leray node.
- lem-sc-module-abelian-zariski-cohomology: retained transitively through
  ModuleCohomologySourceComparison -> ZariskiModuleAbelianCohomologyAgree ->
  ZariskiModuleAbelianCohomologyNatural.
- lem-weil-pbc-higher-direct-image-presheaf: retained in the new normalized Leray node.
- lem-weil-pbc-module-pullback-affine-sections-bijective: retained transitively through
  ModulePullbackAffineSections -> ModulePullbackAffineSectionsBijective.
Thus no module is globally pruned; removing a direct dependency is not a closure reduction.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change was required. The plan's cohomological
comparisons need additional glue: the current Leray theorem supplies a global
cocycle-normalized edge, while the target sourceClass uses a chosen restricted
resolution on an inverse-image affine open. Its normalization and scalar compatibility
are not the conclusion of an existing affine-open lemma. In particular,
nonempty_affineOpen_higherDirectImage_sections_iso is only an existential additive
isomorphism, with no naturality or equation tying it to resolutionSectionClass.
The source's DirectImage.Sections comparison also assumes IsSeparated f, whereas
this item assumes only QuasiSeparated f. Neither can replace the normalized step.

The new lemma is strictly one portion of the source dictionary: it contains neither
scalar extension nor sections of a pullback, and the parent supplies a real tensor
argument. Its naturality assumption is discharged by the existing source comparison.
Empty V, zero F and p=0 were checked mathematically: the relevant edges are respectively
zero-module equivalences and the degree-zero augmentation comparison. No cancellation
requires a nonzero ring, nonempty open or faithful scalar extension. No lower module was
adapted. LeanSearch returned HTTP Internal Server Error; this is recorded as unavailable,
not as an absence result. LeanFinder, Loogle and grep searches ran successfully.

## New nodes

new-affine-cohomology-section-equiv is the normalized affine Leray edge for qcqs f
and quasi-coherent F, with any augmentation-preserving RestrictedResolutionSections R
and any supplied natural module/Ext comparison E. It states a linear equivalence before
scalar extension, not the original base-change dictionary. Its module is
lean/Sheaf/AlgebraicGeometry/AffineCohomologySectionEquiv.lean. The node retains the
source unit and chapter and traces the affine dictionary's existing blueprint ancestor.
Its proof steps name the existing Leray, quasi-coherence, affine vanishing,
open-restriction and cohomology-presheaf nodes. No change record is needed: no existing
statement, definition or public import was changed.

## Second reading by P4

1. PASS: compared the parent module with the repository using diff and
   stage3_delivery.diff_module. Its sole existing declaration's signature, from
   `theorem` to `:= by`, is byte-identical, as is its original docstring. There are
   no new declarations in that module, no definition edits, and no change records
   or adapted modules. All four public imports stay identical; removed imports
   are proof-only. The existing node changes only proof, proof_deps, proof_origin.

2. PASS: independently compiled both delivered modules in import order with
   lcompile.py (5.1 s and 31.8 s), with no errors or warnings. A scratch module
   imported both compiled modules and printed axioms for both declarations:
   only propext, Classical.choice, Quot.sound and sorryAx occur. The new affine
   comparison is the sole direct sorry in this delivery; its whole proof is
   `by sorry`, in a public named theorem with a source, proof docstring and node.
   No definition or prohibited declaration is added. E and e are witnesses used
   inside a theorem proof, not arbitrary data installed in a definition.

3. PASS: read RestrictedResolutionSections, resolutionSectionClass, HOver and its
   scalar action, source comparison, LerayDegenerateSections, higher-image open
   restriction, ordinary quasi-coherence, and the affine pullback sections theorem.
   Read Stacks 01F4(2), 01XJ(1), 01E4 and 03FD at their canonical tag URLs.
   The new statement has only the pre-extension affine cohomology identification,
   with no g, S', B, W, J or flatness, and the parent supplies the substantive
   tensor-extension argument. Naturality hE for the multiplication endomorphism
   associated to a global function makes E linear; transporting through the
   open-immersion isomorphism respects that multiplication. The canonical edge
   therefore composes with eH inverse to give the asserted linear map. The
   augmentation and component equations on R identify its class map with that
   edge, independently of the chosen restricted resolution. Checked p=0 (the
   augmentation), empty V and F=0 (zero groups), and a noncanonical natural E
   given by negating a comparison (negating the inverse edge coordinates still
   satisfies the formula). No nonempty, separated, noetherian or nonzero-ring
   assumption is used. The source comparison for an arbitrary natural E does
   not assert compatibility between different degrees, nor does it need it.

   Repeated searches using different queries through msearch: LeanFinder
   `derived pushforward cohomology over an affine open computed by sections of
   a resolution`, Loogle `CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
   and grep `homology.*sheafification|sections.*rightDerived`. The first returns
   cohomology-presheaf and ordinary pushforward declarations; the second returns
   resolution computation/naturality, useful for the remaining proof but not an
   affine normalized edge. The grep search returns no hits. An initial Loogle
   query used an unqualified identifier and failed; no absence inference is made
   from it. Also searched both source roots with rg for resolutionSectionClass,
   sectionCohomologyTheta and affineOpen_higherDirectImage. Read the existing
   AffineOpenHigherDirectImageSectionsIso: its existential additive isomorphism
   supplies neither scalar compatibility nor the required class-map equation.
   Read DirectImage.Sections: its affine comparison requires IsSeparated and
   has no requested resolution normalization. LocalDirectImageStalkClassEquiv
   uses a local ring's closed point and does not apply to arbitrary affine V.
   The remaining normalization is not a short existing-lemma application.

4. PASS: the parent constructs eH from the existing natural comparison, uses
   only the new affine Leray step before scalar extension, swaps tensor factors
   to get k, proves B-linearity by hs, extends e by
   TensorProduct.AlgebraTensorModule.congr, and proves bijectivity by composition.
   The ht and he equations give precisely D.sourceClass in the pure-tensor
   normalization. All remaining imports either supply public signature types
   or declarations used by this proof/the new node's recorded proof plan.
   Checked dag/units/sk-thm-p1.json realized statement and all four step lists:
   unchanged, with no unit step bypassed. The old direct dependencies are all
   individually accounted for under No longer needed; none is globally pruned.

5. PASS: the parent node's two proof steps and six proof_deps match the source
   comparison, normalized affine edge, quasi-coherence and tensor-pullback proof.
   The new node's nine proof_deps are exactly the union of its three steps' uses.
   Its Lean record matches its declared signature, and its chapter/unit,
   blueprint origin, source, created record, status and actual searches are
   present. The open theorem's docstring and node agree about the normalized
   pre-extension conclusion and the natural E hypothesis.

Changes by the second reader: expanded No longer needed with all six removed
old direct DAG dependencies and their surviving uses; appended independent
searches to the new node and this review. No Lean proof or statement needed
repair. This remains one hole closed and one hole added, a decomposition with
zero net hole reduction, and no globally pruned modules.
