## What changed

Replaced the original hole in `singletonTensorDegreeComparisonHom_bijective` by
an additive-group argument from two strict parts of the affine calculation:
`singletonTensorDegreeComparisonHom_kernel` and
`singletonTensorDegreeComparisonHom_surjective`. Added their two modules and
nodes, and updated the original node's proof, proof dependencies and proof origin.
The original declaration signature and public import are unchanged.

For two source elements with equal images, the combining proof rewrites the
image of their difference as zero, applies the zero-kernel statement, and uses
`sub_eq_zero` to obtain equality. It pairs this injectivity with the lifting
statement. The new statements respectively handle the kernel and the range;
neither states the original bijectivity conclusion. Their docstrings give the
affine tensor construction, its normalization on all generators, and the
separate injectivity or lifting argument. This delivery is a decomposition.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_bijective`
(node `new-etale-affine-singleton-tensor-degree-comparison-bijective`).
The item module has no sorry.

Added two named public theorem holes:

- `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_kernel`
  (node `new-etale-affine-singleton-tensor-degree-kernel`).
- `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_surjective`
  (node `new-etale-affine-singleton-tensor-degree-surjective`).

One original hole is closed and two lower holes are added: net minus one.
Both are strict parts of the affine calculation; the kernel statement does
not assert lifting, and the lifting statement does not assert injectivity.
No data is chosen in a definition from an unproved theorem.

## No longer needed

No original import or original geometric dependency is pruned. The affine
pullback-section theorem and binary affine fibre-product spectrum formula
remain proof dependencies of both new nodes. No existing library module is
claimed to leave the target closure.

The earlier sandbox attempt's `EtaleAffineIndexedTensorSections` and
`EtaleAffineTensorPullbackSections`, and the attempted
`EtaleAffineSingletonTensorDegreeEvaluationExt`, are not part of this
reduction or delivery. Their new nodes are not delivered. Their proof-imports
were removed. The combining proof also no longer needs the attempted private
`tensorPi_addHom_ext` helper. These are abandoned local additions, not pruning
of already landed modules.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt contained two geometric holes and a combining proof
that did not compile within the 60-second limit. The affine algebra and
coefficient equivalences could be composed in a checked partial proof, but
identifying their generator formula with the predicate's singleton projection
caused either a compiler timeout or an apparent identical-type mismatch.
The normalized projection carries implicit product and additive-group
structures; attempts to abstract that comparison across a new module also
hit the file limit. No tool, library definition or existing signature was
changed to bypass this.

The final decomposition leaves the two actual affine arguments as separate
kernel and range calculations, rather than claiming the inherited proof was
complete. The remaining proofs must construct the same affine tensor
comparison and check its normalization, as the docstrings and nodes explain.
The source for both parts is the original node's affine calculation in Stacks
Tag 03P2, expanded by its existing affine fibre-product and pullback-section
dependencies. Edge cases: n=0 has one factor; zero modules and empty affine
schemes are allowed. The unit's realized record has no nodes at this depth;
its route is unchanged.

## New nodes

`new-etale-affine-singleton-tensor-degree-kernel` states that a normalized
comparison has zero kernel. Its proof constructs the affine tensor equivalence,
uses tensor induction to identify evaluation with that equivalence, and then
uses its injectivity and injectivity of ULift.down.

`new-etale-affine-singleton-tensor-degree-surjective` states target-section
lifting. Its proof uses the same affine tensor equivalence to choose a preimage
of the evaluated section and uses injectivity of singleton evaluation to check
the lifted source element maps to the requested target element.

No change record or forced adaptation is needed.

## Second reading by G1

1. **Visible declarations unchanged: PASS.** Compared the item module with the
repository using `diff -u`. The existing declaration, its complete binder list,
conclusion, visibility, namespace and docstring are unchanged. Removed the
accidental doubled space before `:=` so even the signature text matches. The
only imports added to that module are the two plain proof imports. No definition,
existing public import or target statement changes; no change record is needed.
There are exactly three delivered Lean modules and three node records.

2. **Proof and axioms: PASS as a decomposition.** Compiled all three files in
import order through `lcompile.py`. Independently compiled scratch copies with
`#print axioms` for all three declarations. Each reports exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The combining theorem has no
local sorry; its `sorryAx` comes from the two declared lower holes. Read its
`map_sub`/`sub_eq_zero` argument: equal images give a difference in the kernel,
which is zero, and the second theorem supplies surjectivity. No axiom, unsafe,
opaque, implemented_by, extern or hollow definition is added.

3. **Split statements and sources: PASS, still open.** Read the pure-tensor
normalization predicate, the affine-section theorem
`Modules.exists_tensorPullback_affine_sections`, the fibre-product-spectrum
node and its Mathlib match `pullbackSpecIso`, and the definitions
`tensorSectionsComp`, `tensorSectionsUnit`, `etaleTensorSectionsRestriction`.
Checked the affine calculation in [Stacks 03P2](https://stacks.math.columbia.edu/tag/03P2),
proof's first affine-case paragraph, against
[01I4](https://stacks.math.columbia.edu/tag/01I4),
[01I9](https://stacks.math.columbia.edu/tag/01I9), and
[01IA](https://stacks.math.columbia.edu/tag/01IA). The kernel theorem keeps X, F,
quasi-coherence, affine etale U and W, the X-morphism g, n, f and normalization;
it asserts only zero-kernel detection. The second keeps those same hypotheses
and asserts only existence of preimages. Neither assumes g surjective or any
faithful-flatness property: neither is required for the degree identification.
For n=0 there is one W factor; for F=0 both groups are zero; empty W gives zero
sections and tensor power, since n+1 is positive. The statements include all
these cases. Each is a strict part of bijectivity, with a separate final
injectivity or lifting argument, rather than a renamed bijectivity assertion.
No new data is chosen from an unproved existence theorem.

Searched independently with msearch LeanFinder for injectivity of the tensor
comparison over affine schemes, Loogle for `AddMonoidHom.ker_eq_bot`, and grep
for singleton kernel/range and affine tensor comparisons; inspected the
upstream AlgebraicGeometry tree and the repository's Sheaf modules with rg.
The candidates give flat tensor-map injectivity, invertible-module cancellation
or a kernel theorem already assuming injectivity, not this normalized map.
The higher degree-isomorphism and inverse modules depend on this item and
cannot prove it without circularity. Neither remaining affine argument closes
by these candidates in a few minutes. The report therefore continues to count
one hole closed, two added, net minus one, as a decomposition only.

4. **Route and pruning: PASS.** The existing additive proof is already short;
Mathlib's `injective_iff_map_eq_zero` expresses its same zero-kernel reduction
but does not close either geometric hole. Kept the working proof. Every
import in the item is needed either by its public statement or by its proof;
the new modules each expose only the normalization import their signatures
need. Both old proof dependencies,
`lem-weil-pbc-module-pullback-affine-sections` and
`lem-weil-pbc-fibre-product-affine-spectra`, are replaced as direct dependencies
of the item by the two new nodes, and retained inside their proof plans. Thus
none is pruned from the proof route or target closure. The unit
`dag/units/sk-prop-h2.json` has `realized.statement=[]` and `realized.steps=[[]]`;
no realized unit step is bypassed. Traced the new nodes' blueprint provenance
to `lem-sc-etale-affine-qcoherent` through the existing Amitsur, degree comparison
and inverse nodes and corrected their `from` records accordingly.

5. **Node/Lean agreement: PASS after repairs.** The item's node now describes
exactly the two lower calculations followed by the additive difference proof;
its `proof_deps` and `proof_origin` agree with the Lean. Verified the new nodes'
verbatim `lean.statement`, module, file, declaration, chapter, unit, created
record, source, proof and recorded searches. Rewrote their informal statements
to introduce X, F, U, W, g, n and f explicitly. Split their single long proof
paragraph into four steps and cited the previously omitted quasi-coherent
pullback, tensor-pullback adjunction, normalized restriction and normalization
nodes. The cited affine-section statement supplies both bijectivity and the
pure-tensor formula, while the spectrum formula supplies its projection maps;
no step relies on hidden material from those nodes' proofs. `proof_deps` is
exactly the union of the step citations. Added the independent searches to
both new nodes, retaining the logged LeanSearch-unavailable result honestly.
Added source/blueprint module docstrings to both new files. No Lean proof was
rewritten and no additional hole was introduced during this reading.
