## What changed

`picardExternalRectangleSectionsMap_bijective` is now proved by composing the ordinary
projection-section tensor comparison with `quasiCoherent_tensor_product_affine_sections`
on the affine rectangle. Quasi-coherence is transported from the ordinary pullback
along uniqueness of left adjoints. Tensor induction identifies the composite with the
existing explicit map, using the new comparison's formula and `tensorSectionsMap_tmul`.
All existing signatures, definitions, visibility, and docstrings are unchanged.

The new module `Sheaf.AlgebraicGeometry.AffineRectangleProjectionSectionsTensor` proves
`exists_affine_rectangle_projection_sections_tensor`. It adapts the private, proved
whole-affine argument in `ExternalGlobalSectionsTensorAffine` to arbitrary affine opens.
It uses the affine ring-section pushout and existing affine pullback section comparisons,
then Mathlib tensor and pushout base-change cancellation. Its codomain is the tensor of
ordinary section modules, before applying sheaf tensor sections. The additive equivalence
is constructed from actual linear equivalences; its pure-tensor formula determines it.
There is no arbitrary witness chosen from an unproved existence theorem.

The target adds four plain proof imports: the new comparison module,
`QuasiCoherentTensorProductAffineSections`, the upstream `PullbackCarrier`, and upstream
`Modules.Tilde`. Existing public imports supply definitions used in public signatures.
The new module publicly imports `FieldLinearModuleCohomologyOperations` for its signature;
its affine pullback comparison, affine geometry, and tensor algebra imports are plain.

## Proved and sorry left

Original hole closed: `picardExternalRectangleSectionsMap_bijective`
(node `lem-sc-picard-external-rectangle-sections-bijective`): 1 of 1 original holes.
New theorem proved: `exists_affine_rectangle_projection_sections_tensor`
(node `lem-sc-affine-rectangle-projection-sections-tensor`). Holes added: none.
No `sorry` remains in either delivered module. This is a proof, not the first worker's
one-hole-to-two-holes decomposition. The explicit axiom checks of both public theorems and all original definitions show
only `propext`, `Classical.choice`, and `Quot.sound`, with no inherited `sorryAx`.
The global sorry ledger determines the net in the targets' import closure.

## No longer needed

No original import or library module is pruned. The old proof dependency
`lem-weil-pbc-module-pullback-affine-sections` is no longer a direct dependency of the
rectangle bijectivity proof: it is used by the new projection-section comparison and
remains a transitive dependency. All other original proof dependencies are retained.

The first worker's unlanded injectivity and surjectivity declarations and node files
were removed from this delivery. They are replaced by a proved geometric comparison,
not submitted as additional holes or reported as pruned library modules.

## Where the brief, the DAG or earlier work was wrong

The first worker's split nodes had proof dependencies back to their parent, which made
its proposed dependency graph circular. Their Lean statements were placeholders in JSON,
their comments were not declaration docstrings, and their searches were incomplete.
The original bijectivity docstring had also become attached to the injectivity theorem.
The report did not explicitly count the two new holes as a decomposition.

The whole-affine projection-section proof already present in the library supplies a
usable argument after replacing top opens with affine opens and using the ring-section
pushout theorem on those opens. The second reading completed this argument. Source read:
[Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED), affine case preceding
`equation-kunneth-on-cech`; the existing target docstring already expands this argument.
No mathematical statement or definition correction was required.

## New nodes

`lem-sc-affine-rectangle-projection-sections-tensor` records the ordinary section-tensor
comparison, with the complete argument, verbatim Lean signature, source, parent route,
and actual searches. LeanFinder found affine spectrum pullback formulas; Loogle found
`Algebra.IsPushout.cancelBaseChange`; grep found the tensor cancellation maps. LeanSearch
returned an internal server error, recorded as unavailable. None supplied the assembled
comparison for module sections on arbitrary affine opens. Library and upstream searches
found only the private whole-affine comparison; it is not accessible or applicable to
arbitrary opens without this adaptation. No change record is needed.

## Second reading by N4

1. Compared the target module against the repository with `diff`. Every existing signature,
   definition body, public import, visibility, and docstring remains byte for byte identical.
   The only changes to that module are plain proof imports and the bijectivity proof.
   Removed the first worker's unlanded intermediate declarations. Verdict: unchanged contract.
2. Both delivered modules compile locally through `lcompile.py` without errors or warnings.
   Inspected all terms: no `sorry`, axiom declaration, unsafe/opaque declaration, extern,
   implemented_by, or hollow definition. The private algebra equivalence is a composite
   of actual Mathlib equivalences. A scratch axiom check and the delivery probe check the
   public declarations and the new module's helpers. The scratch `#print axioms` checks
   of all five original declarations and the new public theorem show exactly `propext`,
   `Classical.choice`, and `Quot.sound`; none uses `sorryAx`. The delivery axiom probe
   passes too. Verdict: genuine proofs with only the three permitted standard axioms.
3. No statement is left split off with `sorry`. The new proved comparison has exactly the
   original affine-open and quasi-coherence assumptions and compares ordinary tensors,
   a strict part of the argument. Checked empty U or V (C and the corresponding modules
   are zero), zero coefficients, and top opens (the existing whole-affine computation).
   All maps and inverse identities work over zero rings, with no nontriviality requirement.
   Searches are described above; no existing public comparison was duplicated. Verdict: true.
4. Read the imported pullback and tensor comparisons and the proved whole-affine argument.
   The new route uses those comparisons and Mathlib cancellation directly; it does not
   posit injectivity or surjectivity of the original map. Public imports provide signature
   data, proof imports are plain, and no unused original import remains. The unit
   `sk-prop-av-cube` retains its theorem-of-the-cube route: this item is an affine Kunneth
   tool below the unit, not a realized unit statement or step. Its `realized` fields and
   the unit record are untouched. Verdict: top-down reduction, no unit bypass.
5. Read the existing and new node records against their Lean proofs. The parent records
   the naturality construction, quasi-coherence transport, and composition of the new
   ordinary section equivalence with affine tensor sections. The new node records the
   actual ring pushout, affine pullback equivalences, and five algebraic equivalences;
   `proof_deps` is exactly the union of the steps' uses. Its statement is self-contained,
   the Lean signature is verbatim, and all required provenance/search fields are present.
   There is no dependency back from the new node to the parent. Verdict: DAG agrees.

Second reading changed the attempted decomposition into a complete proof, removed its
circular nodes, restored the original docstring attachment, added one proved comparison
module/node, and rewrote the proof records and report to describe the final implementation.

Validation: `deliver3.py N4 Sheaf.AlgebraicGeometry.PicardExternalRectangleSections --no-push`
printed OK; review class CODEX because this delivery adds a proved module and node.
