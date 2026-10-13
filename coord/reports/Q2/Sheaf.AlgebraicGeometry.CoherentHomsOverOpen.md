## What changed

Proved `AlgebraicGeometry.Scheme.coherent_homs_over_open_data` by constructing its
open, transition maps, Hom diagram, restriction cocone, and bijective colimit comparison.
The open and sectionwise ideal-power bijections come from
`sections_over_quasiCompact_open`. Finite type of the ideal module uses
`IdealSheafData.isFiniteType_toModules` and the locally Noetherian finite-type-ideal fact.
`formalModuleQuotient_factor` supplies the uniquely determined transition factors.
A private stalk argument proves that every product inclusion becomes an isomorphism
on the complement, including exponent zero. Cancellation proves the diagram laws
and cocone naturality. Mathlib finite-stage representatives, the additive kernel
criterion, and the two new geometric theorems prove the colimit comparison bijective.

Added the two new statement modules below. Updated the structural-data node and the
main theorem node to describe the actual proof. Existing public signatures, public
imports, definitions, and the already proved extension clause are unchanged.
All three delivered files compile with `lcompile.py --all`, without warnings.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.coherent_homs_over_open_data`
(node `lem-weil-pbc-coherent-homs-over-open-data`). There is no sorry left in the item.
The existing `coherent_homs_over_open_extension` and `coherent_homs_over_open`
remain proved.

Added exactly two holes, each the complete proof of a public named theorem:

- `AlgebraicGeometry.Scheme.coherent_hom_ideal_power_extension`
  (`lem-weil-pbc-coherent-hom-ideal-power-extension`), in
  `Sheaf.AlgebraicGeometry.CoherentHomIdealPowerExtension`: finite-stage extension
  only, on a prescribed open complement.
- `AlgebraicGeometry.Scheme.coherent_hom_ideal_power_eventually_zero`
  (`lem-weil-pbc-coherent-hom-ideal-power-eventually-zero`), in
  `Sheaf.AlgebraicGeometry.CoherentHomIdealPowerEventuallyZero`: eventual vanishing
  only, with no extension or diagram assertion.

This is a decomposition, not a sorry-free proof of Lemma 01YB: one hole closed and
two added, net -1 before accounting for import-closure pruning. The combination is
an explicit Lean construction and proof, not an application of a renamed data-existence
statement. Neither new theorem mentions CoherentHomsOverOpenData or asserts
existence of its geometric/diagram fields. Edge cases checked in the statements and
proof descriptions: exponent zero, zero modules, empty complement, unit ideal, and
empty scheme. All public signatures of the item retain their original universes.

## No longer needed

Removed these 16 direct proof imports from the item (public imports were retained):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.CoherentArtinRees`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules`
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom`
- `Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

Their geometric assertions are retained where needed in the new nodes' proof plans;
this is direct-import pruning, not a claim that all these modules are globally
unreachable or that the remaining geometric proofs can omit Artin--Rees, Hom, or support
annihilation. In particular the surjectivity proof still needs the scalar-case
annihilator argument and tensor--Hom argument. The eventual-vanishing proof needs
coherent image and support annihilation, but no proper-support definition.

The nodes attached to the removed direct imports are:

- `def-pur-sheaf-hom`
- `def-weil-pbc-closed-subset-proper-over-base`
- `lem-pc-quasicoherent-module-coproducts`
- `lem-pqf-kernel-finite-presentation-noetherian`
- `lem-weil-pbc-coherent-artin-rees`
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
- `lem-weil-pbc-coherent-support-power-ideal-kills`
- `lem-weil-pbc-module-finite-type-submodule-extension`
- `lem-weil-pbc-module-restriction-open-immersion-limits`
- `lem-weil-pbc-module-tensor-hom-adjunction`
- `lem-weil-pbc-noetherian-acc-quasi-coherent`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-quasi-coherent-module-coproduct-closure`
- `lem-weil-pbc-quasi-coherent-module-kernel`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-weil-pbc-quasicoherent-epi-affine-cover`
- `lem-weil-pbc-sections-annihilated-by-ideal`
- `lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent`
- `pqf-lem-coherent-ft-locnoeth`
- `pqf-lem-qcoh-principal-open-criterion`

None is asserted globally obsolete. The old main node's direct proof-dependency list
is replaced by the structural-data and extension nodes. The structural-data node now
uses only the two new geometric nodes and the existing ideal-product-stalk, finite-type
ideal-module, transition-factor, affine-product, and sections-comparison nodes.
The generic category-colimit and sheaf-of-modules definitions are supplied by retained
public imports; the filtered-colimit proof itself uses Mathlib directly.

For completeness, the other old direct proof dependencies removed from the main
node's plan are listed below. These are changes of direct dependency, not claims
of global obsolescence. Some remain statement dependencies or are used by the
structural-data node or the split geometric proof plans:

- `def-pc-scheme`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-module-finite-type-presentation`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-filtered-colimit-modules-elementwise`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-sections-over-quasi-compact-open`
- `pqf-def-coherent`

In particular, `def-pc-scheme` and
`lem-weil-pbc-filtered-colimit-modules-elementwise` are also removed from the
structural-data node's old direct proof dependencies. The colimit argument uses
Mathlib's finite-stage representatives and cocone equations directly.

## Where the brief, the DAG or earlier work was wrong

The assigned module has one remaining sorry, not the two recorded in older delivery
metadata: its extension-from-colimit clause is already proved by F4. The original
structural-data node's short plan omitted the general-G tensor--Hom and Artin--Rees
steps needed for its surjectivity assertion; these remain in the new extension node.
The previous main node still recorded its entire original geometric proof despite
its body merely combining the structural-data and extension declarations; its route
is now synchronized with that body.

`IdealPowerComplement` exists in the source but has no object file in the compiled
snapshot seen during this session. The proof therefore uses the available
`sections_over_quasiCompact_open` instead. No dependency was duplicated.
The local literature tree contains lists but no Stacks .tex files; checked the
primary source at https://stacks.math.columbia.edu/tag/01YB. LeanSearch returned
HTTP Internal Server Error, recorded as unavailable, while LeanFinder, Loogle and
grep ran successfully. No exact Mathlib or existing library match was found for the
two geometric assertions. Blueprint search found no matching imported node. The
item does not realize a unit statement or unit step, so its decomposition preserves
the fixed unit route. The finite-type-ideal-module result is a proved generic tool
from the abelian-varieties unit, not a replacement of any unit step.

## New nodes

`lem-weil-pbc-coherent-hom-ideal-power-extension`:
`lean/Sheaf/AlgebraicGeometry/CoherentHomIdealPowerExtension.lean`.
Retains only surjectivity on a fixed complement (Steps 2 and 4--12 of the old plan).
The proof in words includes the explicit affine tensor-kernel calculation omitted
by Stacks, and follows the existing scalar-case, Hom and Artin--Rees nodes.

`lem-weil-pbc-coherent-hom-ideal-power-eventually-zero`:
`lean/Sheaf/AlgebraicGeometry/CoherentHomIdealPowerEventuallyZero.lean`.
Retains only the eventual-zero criterion (Step 13), via the coherent image and the
support-power annihilation theorem. Both new nodes inherit the chapter/unit and
blueprint ancestry of the item. No interface change record or forced adaptation
is needed.

## Second reading by Q2

1. Compared every delivered source with the repository. The item changes only its
   structural-data proof, adds two private proof helpers, and changes plain proof
   imports. All existing declaration signatures are byte-for-byte unchanged;
   public imports, visibility, structure fields, and definitions are unchanged.
   The new modules introduce exactly the two reported theorem statements. No
   interface change or forced adaptation is present. Verdict: pass.
2. Compiled all three files with `lcompile.py --all`: no errors or warnings.
   Scanned the delivered sources: exactly two `sorry`s, both entire named public
   theorem proofs; no forbidden declaration mechanism or hollow definition.
   A scratch copy with `#print axioms` checked the structural-data theorem, the
   existing extension clause, the main theorem, and both new theorems. Only
   `propext`, `Classical.choice`, `Quot.sound`, and (for open dependencies)
   `sorryAx` occur. The existing extension clause uses no `sorryAx`. The data
   chosen from existence proofs is determined: U by its points, r by its
   factorization through a monomorphism. D and c are constructed explicitly.
   Verdict: pass as a decomposition, not as a sorry-free geometric proof.
3. Read both split statements against Stacks Tag 01YB and the support-power
   argument of Tag 01Y9. Extension asserts only finite-stage surjectivity;
   eventual vanishing asserts only the zero criterion, uniformly over the
   uniquely determined transition factor. Each is strictly part of the original
   argument and has a matching node and source/proof docstring. Checked exponent
   zero, zero modules, empty scheme/open, zero ideal, and unit ideal: no false
   edge case. Independently searched using LeanFinder (extension across a closed
   subset from an ideal multiple, and finite-type maps supported on V(J)),
   Loogle (`SheafOfModules.IsQuasicoherent`, only general quasicoherence results;
   also `Ideal.pow_smul`, no such identifier),
   the grep service (annihilator/support/extension/restriction), and `rg` in both
   library roots. The hits concern scalar basic-open sections, support
   annihilation, or unrelated derived/Koszul statements; none is either split
   theorem. The existing scalar ideal-power evaluation theorem does not cover
   a general coherent G. The geometric holes require substantial sheaf/image
   and tensor-Hom work, rather than a short application closing them. Verdict:
   pass. Expanded the extension docstring's scalar argument to specify E_N,
   stabilization, the Artin--Rees exponent, zero annihilator quotients, and the
   finite-stage representative.
4. Read the proof from the target down through the existing extension clause,
   structural data, and its actual imported dependencies. Diagram laws and
   cocone laws use cancellation, and colimit bijectivity uses Mathlib directly
   plus exactly the two split geometric assertions. No shorter existing general
   theorem was found. Proof-only imports are plain imports; the new modules'
   public imports provide the names/types in their signatures. The 16 removed
   direct imports are recorded; the report now names every removed old direct
   proof dependency, including those retained elsewhere in the route. Searched
   every unit's `realized` field: this item realizes no unit statement or step;
   no unit route or unit file is changed. Verdict: pass.
5. Checked all four node records. Existing nodes change only `proof`,
   `proof_deps`, and `proof_origin`. For every node the dependency list equals
   the union of the steps' `uses`; the structural-data route matches the Lean
   construction and the main route matches its existing combining proof.
   Both new records contain the required provenance, searches, ancestry,
   chapter/unit, and Lean record; their recorded Lean signatures are verbatim.
   Verdict: pass.

Second reading changed the extension theorem's proof docstring and completed
`## No longer needed`; no Lean proof, statement, definition, or node was changed.
The hole accounting remains one closed (`coherent_homs_over_open_data`) and two
added (`coherent_hom_ideal_power_extension`,
`coherent_hom_ideal_power_eventually_zero`), a decomposition with net -1 holes
before import-closure pruning.
