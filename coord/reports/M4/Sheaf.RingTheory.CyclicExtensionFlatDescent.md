## What changed

Replaced the sole hole in `LinearMap.exists_cyclic_extension_flat_descent` by a complete
Lean proof from `LinearMap.exists_ideal_power_hom_lift`. The existing theorem signature is unchanged. Second reading removed the unused public
short-complex import and recorded its downstream check below. Constructed the middle module as
`(N × R) / range (r ↦ (l(r), -r))`; proved injectivity, exactness, surjectivity,
both comparison squares, and bijectivity of the scalar-extended comparison map.
The construction uses no data chosen from a sorried existence theorem except the
local witnesses of the lifting lemma inside this theorem proof; it introduces no definition.
The inverse of `a` onto its range is determined uniquely by injectivity.

Added `Sheaf.RingTheory.IdealPowerHomLift`, one theorem isolating the ideal-Hom part of
05EG's two-right-arrows argument. Updated the parent DAG proof to the implemented route.
Both modules compile through `lcompile.py --all` without errors or warnings.

## Proved and sorry left

Closed: `LinearMap.exists_cyclic_extension_flat_descent`
(node `lem-weil-pbc-cyclic-extension-flat-descent`); no sorry remains in the item's module.

Added and left sorry: `LinearMap.exists_ideal_power_hom_lift`
(node `lem-weil-pbc-ideal-power-hom-lift`). Its whole proof is `by sorry`.
This is a decomposition, not a net hole reduction: one upper hole closed, one lower hole added.
The new theorem only lifts maps out of an ideal power modulo principal maps. It contains
no extension, no middle module, no short exact sequence, and no comparison equivalence;
the main module proves all those parts explicitly from it.

Edge cases checked mathematically: if `I = 0`, the source of the new map is zero and
its conclusion is vacuous. If `I = R`, every map is principal, so `l = 0` and
`m = -d(1)` suffice. For `S = R`, take `l = d`, `m = 0`. No assumption that
`N` is finitely generated, or that `S` is faithfully flat, has been introduced.

## No longer needed

Removed direct proof imports:
- `Sheaf.Paper.CyclicExtensionCocycle`;
- `Sheaf.Paper.TorsionModuleFlatBaseChangeIso`;
- `Sheaf.RingTheory.TorsionHomFlatComparison`.

The latter two are still needed in the new lifting lemma's proof plan and imported there;
this is relocation, not pruning of their work. Finite-product tensor comparison, free modules,
flat tensor exactness, tensor right exactness, and quotient modules likewise remain needed,
either directly in the main proof or in the lifting lemma's plan.

The route no longer needs `lem-weil-pbc-cyclic-extension-cocycle` or its module
`Sheaf.Paper.CyclicExtensionCocycle`: explicit graph relations replace its extension
construction, classification and boundary-change equivalences. The elementary naive-Koszul
kernel calculation and cycle homology calculation are written out in the new node;
they do not require the packaged extension theorem.

The route no longer needs `lem-weil-pbc-tensor-quotient-base-change`
(`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`): all quotient comparisons stay
in `S ⊗[R] (R ⧸ I^n)`, so no comparison with `S/(I^n S)` is constructed.
These nodes are removed from the parent's proof dependencies; no claim is made that
other targets or modules cannot still need them. Second reading also removed the unused public import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, and the redundant private imports
`Mathlib.LinearAlgebra.Quotient.Basic` and `Mathlib.LinearAlgebra.Prod`.


For completeness, the old parent `proof_deps` absent from the new parent are:
`def-weil-pbc-free-module`, `lem-weil-pbc-tensor-finite-product`,
`lem-weil-pbc-torsion-module-flat-base-change-iso`, and
`lem-weil-pbc-torsion-hom-flat-comparison` (all relocated to the lower lifting node),
plus `lem-weil-pbc-cyclic-extension-cocycle` and
`lem-weil-pbc-tensor-quotient-base-change` (unused by this route).
This reports removal from this proof route, not whole-library unreachability.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The nine-step plan is mathematically sound, but the complete
cocycle package and the quotient-ring tensor comparison are unnecessary for assembling
this particular extension. Using maps from the ideal power makes the constructive part
shorter and confines the remaining work to the Koszul/Hom comparison.

The local Stacks source path recorded by the DAG was absent on this machine. Read the
specified sources at https://stacks.math.columbia.edu/tag/05EG, /05EE and /05EF instead.
LeanSearch was attempted and returned an internal server error; the unavailable search
is recorded honestly, without a mathematical no-match verdict. LeanFinder, Loogle,
Mathlib grep, and library grep found no ready-made lifting/descent theorem.
The unit `sk-thm-p1` and its realized statements and steps are unchanged.

## New nodes

`lem-weil-pbc-ideal-power-hom-lift`, in `Sheaf.RingTheory.IdealPowerHomLift`:
05EG's Koszul one-cycle class lift followed by injectivity of the torsion Hom comparison,
formulated as lifting `I^n → S ⊗ N` modulo principal maps. The node and docstring spell
out generator choice, the kernel killed by `I^n`, homology killed by `I^n`, tensor
compatibility, class lifting, admissibility, and factorization through `I^n`.
Its dependencies are existing nodes. No forced adaptation is needed.
The import change record is `coord/changes/CyclicExtensionFlatDescentImports.md`.

## Second reading by M4

1. Compared the complete existing module with the repository using `diff` and
   separately compared the theorem signature byte for byte: identical. No existing
   declaration, hypothesis, conclusion, universe, visibility or definition changed.
   The only public-interface edit is the explicitly recorded removal of an unused
   public import. There are no adapted modules or target changes. PASS.
2. Read the graph quotient construction, inverse onto the range, exactness proofs,
   comparison squares and bijectivity argument. Both modules compile through
   `lcompile.py --all`, with no errors or warnings. Scratch copies with
   `#print axioms` for both declarations report only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The sole textual hole is the named public theorem
   `LinearMap.exists_ideal_power_hom_lift`; no forbidden declarations, hidden holes,
   hollow definitions or exposed arbitrary witness choices occur. The middle module
   is an explicit quotient inside a proposition proof; its use of lifting witnesses
   does not define an exported object from an unproved existence assertion. PASS.
3. Independently checked the lower theorem against Stacks Tags
   [05EG](https://stacks.math.columbia.edu/tag/05EG),
   [05EE](https://stacks.math.columbia.edu/tag/05EE), and
   [05EF](https://stacks.math.columbia.edu/tag/05EF): lift the cycle class, kill its
   restriction to the naive-Koszul kernel using torsion-Hom injectivity, then factor
   through the ideal. Finite generation of I gives finite generation of I^n; killing
   by I^n gives I-power torsion. The sign of the principal correction agrees with
   the relation `(l(r),-r)` and `tau + a(m)`. Checked I=0, I=R (including S=0),
   S=R, and n=1; no faithfulness or finite-presentation hypothesis is needed.
   The lemma isolates the ideal-Hom calculation and leaves extension construction
   and comparison to the main proof, so it is a genuine decomposition, not a renamed
   copy of the item. Its docstring and node supply the full natural-language proof.
   Repeated LeanFinder, Loogle and Mathlib grep searches with new wording; searched
   the local Sheaf and upstream sources for the tags and equivalent ideal-Hom claims.
   Factorization criteria need finite presentation/flat targets and do not supply
   this result for arbitrary N. No shorter ready-made theorem was found; closing
   the Koszul comparison is substantial further work, not a few-minute repair. PASS.
4. The main proof genuinely reduces the upper problem and constructs the extension
   explicitly. Removed the unused short-complex public import and two redundant
   private imports; compiled after removal. Kept the lower module's private imports
   for the remaining named theorem's stated proof plan. Every removed old parent
   dependency is listed above, distinguishing relocation from bypass. Read
   `dag/units/sk-thm-p1.json`: no statement or step realization is removed or replaced;
   the alteration is below those realizations in the cyclic descent tool. Compiled
   the original sole direct importer `Sheaf.RingTheory.TorsionExtensionFlatDescent`
   unchanged against the edited module; listed all 210 textual transitive users in
   the import change record. No forced adaptation is needed. PASS.
5. Checked both node statements against Lean, every step's `uses` against the union
   `proof_deps`, and the parent's implemented proof against `proof_origin`. The new
   node has a source, complete proof steps, searches, creation and blueprint provenance,
   matching chapter/unit and verbatim Lean signature. Added this reader's independent
   search records to the new node. Existing node changes are confined to the stage-3
   owned proof fields; no statement or unit record is changed. PASS.

Second reading changed: removed three unused/redundant imports, added
`coord/changes/CyclicExtensionFlatDescentImports.md` with the unchanged direct-importer
compile and downstream inventory, completed the removed-dependency report, and added
independent search evidence and this review. No mathematical proof repair was needed.
Holes closed: `LinearMap.exists_cyclic_extension_flat_descent` (1 of 1 original holes).
Holes added: `LinearMap.exists_ideal_power_hom_lift` (1). This is a decomposition with
net zero hole reduction; the original theorem still depends on the lower hole.
