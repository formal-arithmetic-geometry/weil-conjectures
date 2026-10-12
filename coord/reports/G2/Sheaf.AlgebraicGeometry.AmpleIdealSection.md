## What changed

Proved `exists_section_of_ample_ideal` by choosing the affine nonvanishing neighbourhood from
ampleness, lifting an ideal section, clearing its denominator, and multiplying by one extra ample
section. Quasi-coherence of the ideal is proved directly from closed-immersion pushforward and
kernel closure, avoiding the much larger HilbertPolynomial module. Added the proved bridge `mem_nonvanishingLocus_iff_generatesAt`, based on Stacks 01CY.

## Proved and sorry left

The item's `exists_section_of_ample_ideal` is proved. The bridge theorem
`mem_nonvanishingLocus_iff_generatesAt` is proved. Closed original hole: `AlgebraicGeometry.Scheme.IdealSheafData.exists_section_of_ample_ideal` (one of one). Added holes: none; split-off holes: none. No `sorry` remains in the delivered modules. The main theorem still depends on the existing open `AlgebraicGeometry.Scheme.Modules.isSeparated_of_isAmple`; its axiom print therefore includes `sorryAx`. The new bridge uses only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` (def-pur-sheaf-tensor-product):
  the source monoidal tensor and exponent-law APIs suffice; the notion remains in the DAG.
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`
  (lem-weil-pbc-quasi-coherent-ideal-zero-set-affine): Mathlib's affine support equality and the
  source's proved `range_toModulesι_app` suffice, avoiding its stalk-surjectivity theorem.
- `Sheaf.Paper.NonvanishingSectionTrivializes`
  (lem-weil-pbc-nonvanishing-section-trivializes): replaced by the fully proved bridge and the
  proved source free-generator/zero-locus API.

Removed DAG proof dependencies `lem-weil-pbc-affine-open-spec-points` and
`lem-weil-pbc-affine-open-stalk-localization`: Mathlib's support/basic-open facts suffice without
choosing prime-spectrum or stalk-localization identifications. Their Mathlib import paths were
never direct imports of this module. These are local pruning claims, not claims that the modules
are unreachable from every other target path.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted the necessary bridge between the stalk-based `nonvanishingLocus` predicate and the
existing `GeneratesAt` API. This delivery states and proves that bridge.

## New nodes

The bridge node `lem-sc-nonvanishing-iff-generates-at` records the additional proved declaration.
Its private helper proves that a section basis gives a bijective stalk basis by representing
stalk elements as germs and detecting equality on smaller neighbourhoods. The public proof
transports the maximal-ideal submodule along this bijective linear map and uses the basic-open
criterion. It assumes no compactness, separatedness or Noetherianity. Edge cases: an empty scheme
has no point to test, a zero section fails both predicates, and on a trivial module the equivalence
is the unit criterion in the local ring. For denominator clearing, m=0 is handled by the extra
factor, guaranteeing d*(m+1)>0. The ideal may be zero (then no y meets the hypothesis), or the
unit ideal (then the construction still works).

Searches ran through msearch: LeanSearch was unavailable; LeanFinder returned only structure-ring
nonvanishing/basic-open statements; grep returned no exact Mathlib bridge. The whole blueprint
search for nonvanishing section found no matching statement node. The existing definition node
`def-sc-section-generating-locus` mentions the mathematical equivalence but its recorded Lean
provides the definition only; this theorem supplies the missing proof. The unit's realized
statement `thm-sc-proper-cohomology` and its route are untouched. The change record is `coord/changes/ample-ideal-section-imports.md`;
no definitions or declaration signatures change.



## Second reading by G2

1. Compared the existing module against the repository with `diff`: the existing declaration's
   signature and docstring are byte for byte unchanged. No definition changes. Only the proof,
   private proof imports, and namespace/elaboration commands change, as declared in
   `coord/changes/ample-ideal-section-imports.md`. Verdict: pass.
2. Compiled both modules together in import order using `lcompile.py --all`: no errors or
   warnings. Inspected every proof and checked forbidden commands and holes: none. A scratch
   copy with `#print axioms` confirms the bridge uses only the three standard axioms; the item
   additionally uses `sorryAx` through existing open ample separatedness. There is no arbitrary
   data taken from an unproved existence theorem or hollow definition. Verdict: pass.
3. No statements are split off with holes. Read the new proved bridge and its private stalk
   helper: injectivity follows from shrinking a zero germ and the section basis, surjectivity
   from representing a germ and expanding in that basis. The maximal-ideal comparison is a
   genuine linear-map transport. Checked empty schemes, zero sections, trivial line bundles,
   zero/unit ideals, and denominator exponent zero. Repeated searches using different wording:
   LeanFinder “line bundle section residue fibre nonzero if and only if basis on neighborhood”
   returned structure-ring evaluation/basic-open lemmas, not a module bridge; Loogle
   `IsFreeGenerator` did not resolve that identifier; grep “stalk.*[Gg]enerator|[Gg]enerator.*stalk”
   returned no Mathlib match. Also searched both Lean roots for nonvanishing and generation
   APIs. No exact upstream or library replacement found. Verdict: pass.
4. Read the construction from the item downward: affine ideal/support facts, source denominator
   clearing, source free-generator and tensor-power identities give the claimed section.
   Quasi-coherence uses closed-immersion pushforward and kernel closure directly. The extra
   factor ensures positive degree even at exponent zero. Imports needed by signatures are
   public; added proof-only imports are plain imports. No shorter available route found.
   Every removed old proof dependency is listed under No longer needed; the tensor notion is
   correctly retained in the DAG despite removing its redundant module import. The unit's
   realized statement `thm-sc-proper-cohomology` and steps are unchanged. Verdict: pass.
5. Compared node records: the existing node changes only `proof`, `proof_deps`, `proof_origin`;
   each dependency corresponds to the written argument. The new bridge node has its source,
   word proof, searches, creation/blueprint/unit records, and verbatim Lean signature. The
   closed-immersion node records the pushforward declaration among its declarations, and the
   kernel node records the exact theorem used. Verdict: pass.

Second reading changed only this report: recorded the one closed original hole, zero added
holes, inherited ample-separatedness axiom dependency, independent searches, and these verdicts.
No Lean proof or node repair was needed.
