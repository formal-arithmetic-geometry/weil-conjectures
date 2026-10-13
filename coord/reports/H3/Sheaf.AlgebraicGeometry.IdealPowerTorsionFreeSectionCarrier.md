## What changed

Replaced the original hole by a complete combination of two genuine steps of
Stacks Tag 01YB: a coherent carrier of the given open section, followed by a
high ideal-power multiplication image of that coherent carrier. The target
signature and public imports are unchanged. Two proof-only imports provide the
steps. The final proof lifts the section through the bijective product inclusion,
composes two monomorphisms, and proves the required section equality.
The original node now records these two direct dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_idealPower_torsionFree_section_carrier`.
No sorry remains in the item's module. This is a decomposition, not a proof
without sorry dependencies: one upper hole closed, two strictly simpler holes added.

The added holes are:
- `AlgebraicGeometry.Scheme.Modules.exists_coherent_open_section_carrier`
  (node `lem-pc-coherent-open-section-carrier`), the finite-type extension step.
- `AlgebraicGeometry.Scheme.Modules.exists_coherent_idealPower_torsionFree_product`
  (node `lem-pc-coherent-ideal-power-torsion-free-product`), the annihilator
  stabilization and Artin-Rees step for a coherent input module.

The first step asserts coherence, unlike the rejected earlier carrier. The second
has no ambient E or prescribed section s and uses the actual multiplication image,
so neither statement repackages the original conclusion. Both have full proofs in
words from Tag 01YB. No definition or axiom was added.

## No longer needed

No original import removed and no module pruned. The target no longer directly
uses these six original proof_deps; they are retained in the helper nodes' plans:
- `lem-weil-pbc-module-finite-type-submodule-extension`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-weil-pbc-sections-annihilated-by-ideal`
- `lem-weil-pbc-noetherian-acc-quasi-coherent`
- `lem-weil-pbc-coherent-artin-rees`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`

The retained uses are finite-type submodule
extension and coherence for the carrier; annihilator quasi-coherence, ACC,
Artin-Rees, and ideal-product affine sections for the high-power product.
The product node also records finite-type ideal modules and the recursive-power
comparison as tools for forming the power annihilators.
The rejected earlier auxiliary module and its two nodes are absent.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt used a quasi-coherent carrier, which E itself supplies, and
then restated the entire torsion-free carrier theorem with redundant inputs.
This delivery instead requires a coherent carrier, and separately states a
uniform high-power product theorem for any coherent input. Coherence is essential
for ACC and Artin-Rees. The source was checked directly at Stacks Tag 01YB.
The unit's realized fields are empty; its route is unchanged.

Edge cases checked: n=0 means annihilation by the unit ideal; for unit I take k=0,
for zero I take a positive k and the zero multiplication image, for empty U the
section lifting is unique, and for H=0 every assertion is immediate. The carrier
step also covers empty U by the zero submodule. These checks show no nonzero
section on a closed complement is erroneously required to survive.

## New nodes

`lem-pc-coherent-open-section-carrier`, in
`Sheaf.AlgebraicGeometry.CoherentOpenSectionCarrier`, is the coherent carrier
step of Tag 01YB using finite-type extension 01PF and coherence 01XZ.

`lem-pc-coherent-ideal-power-torsion-free-product`, in
`Sheaf.AlgebraicGeometry.CoherentIdealPowerTorsionFreeProduct`, is the
stabilized-annihilator/Artin-Rees construction in the second paragraph of 01YB.
It states properties of the existing multiplication image and chooses no new data
inside a definition. Both nodes retain the original chapter and unit.

## Second reading by H3

1. Interface: compared every delivered module with the repository. The two helper
   modules are new. The existing target signature is byte-for-byte identical;
   its Lean changes are two plain proof imports, the proof body, and an ACC
   source-tag correction in the proof docstring. The
   existing node changes only proof, proof_deps, and proof_origin. No definition,
   hypothesis, conclusion, visibility, or target meaning changed. PASS.
2. Kernel check: all three modules compile locally through lcompile.py without
   errors or warnings. The only two sorries are the entire proofs of the public,
   documented helper theorems listed above. There are no data definitions or
   prohibited declarations in this delivery. Explicit #print axioms checks of all three declarations show only propext,
   Classical.choice, Quot.sound, and sorryAx from the two documented holes;
   the delivery tool additionally probes every added constant. PASS.
3. Split statements: independently read Tag 01YB and the finite-type extension
   and coherence dependencies. The coherent carrier is the finite-type image
   extension step; the product theorem concerns a fixed coherent module and its
   existing multiplication image, independently of any ambient E or chosen s.
   These are distinct, strictly simpler parts of the original argument.
   Checked empty opens, zero modules, unit and zero ideals, and exponent zero.
   For the zero ideal, a positive power gives the zero product and U is empty;
   for the unit ideal use k=0; exponent-zero annihilation forces zero directly.
   No arbitrary existence witness is used as data in a definition. Repeated
   searches with different terms using leanfinder, loogle, grep, and rg on both
   library roots found no duplicate theorem or immediate shorter closure. The
   searches include finite-type subsheaves containing prescribed sections and
   stabilized torsion, rather than the first worker's carrier terminology. PASS.
4. Route and imports: the target actually lifts through the product inclusion
   and composes two monomorphisms; it does not simply apply a renamed target.
   Both new proof imports are used. The helpers' public imports provide the
   notions in their signatures. No original module import is removed. The
   unit sk-thm-picard-coherence has empty realized statement/step lists, and this
   delivery preserves the original finite-type-carrier and Artin-Rees route.
   Neither remaining hole has a closure that takes only a few minutes from the
   currently available interfaces. This is a decomposition, with net -1 hole,
   rather than a proof free of sorry dependencies. PASS.
5. DAG agreement: checked all three nodes, the Lean signatures, source and
   docstring arguments, proof-step dependency unions, provenance, searches,
   blueprint ancestry, chapter/unit, created and lean records. The existing node
   records exactly the two helper applications; the new nodes retain the two
   parts of its old plan and the additional ideal-power comparison tools. PASS.

Changed during second reading: clarified the direct dependencies replaced by
this decomposition in "No longer needed" and recorded the independent checks.
Corrected the mistaken ACC citation 0CYW to 01Y8 in both proof docstrings
and the new product node source/provenance. No proof body, statement, or
definition needed repair. The independent source checks used
https://stacks.math.columbia.edu/tag/01YB, /tag/01PF, /tag/01XZ, and /tag/01Y8.
