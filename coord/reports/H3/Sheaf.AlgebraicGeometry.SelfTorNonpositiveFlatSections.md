## What changed

The existing signature of `AlgebraicGeometry.exists_selfTor_nonpositive_flat_sections`
is unchanged. Its proof now obtains normalized affine coordinates compatible with
one chosen augmented comparison, identifies a supplied quotient homomorphism with
the chosen one using quotient surjectivity, applies the already proved tensor-lift
homotopy theorem, and substitutes equality of homology maps into the chosen
restriction square. This is a real independence-of-lift argument, not the selection
of arbitrary coordinate equivalences.

Added `Sheaf.AlgebraicGeometry.SelfTorNonpositiveChosenComparisons`, stating the
strictly weaker geometric construction for one chosen comparison on each basic
inclusion. It deliberately does not assert compatibility with arbitrary lifts.
The remaining theorem is documented with the full affine tensor-zigzag argument,
its normalization, the chosen algebraic lift, and the restriction square.

Both modules compile individually through `lcompile.py` (about 5 and 13 seconds).
The target proof uses a declaration-scoped heartbeat setting for elaboration of
restricted tensor complexes; the 60-second file limit is unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_selfTor_nonpositive_flat_sections`
(node `new-n4-self-tor-nonpositive-flat-sections`).

Added one hole in
`AlgebraicGeometry.exists_selfTor_nonpositive_chosen_comparisons`
(node `new-h3-self-tor-nonpositive-chosen-comparisons`).
This is a decomposition: one original hole closed, one lower hole added, net zero.
The quotient-map equality and arbitrary-lift homology independence are fully proved.
No definitions or axioms were added. The two experimental coordinate/naturality
splits were withdrawn before delivery; neither appears in the delivered source.

## No longer needed

Removed from the target module's direct proof imports:

- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
  (`lem-sc-affine-quotient-resolution-sheafification`).
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
  (`lem-pc-bounded-above-flat-kflat`).
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`
  (`lem-pc-kflat-open-restriction`).
- `Sheaf.AlgebraicGeometry.AffineChartTotalTensor`
  (`lem-pc-affine-chart-total-tensor`).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
  (`lem-pc-sheaf-modules-tensor-closed`).
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
  (`lem-pc-tensor-mapping-cone-iso`).
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
  (`lem-pur-quasi-iso-cone-acyclic`).

These remain dependencies of the geometric intermediate theorem; none is globally
pruned. The following old proof dependencies also move below that intermediate theorem:

- `lem-weil-pbc-affine-tilde-gamma-adjunction`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`).
- `lem-weil-pbc-spec-module-tilde-sections`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`).

They are no longer direct proof dependencies of the item; the chosen comparison
still needs them. All nine old proof dependencies are thereby accounted for. The main proof imports the chosen comparison
and `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy` only.
No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG planned a geometric square for every supplied lift. That is
unnecessary: the existing proved quotient tensor lift homotopy theorem gives
independence algebraically, after the square is checked for one chosen lift.
Arbitrary pointwise coordinate equivalences cannot be substituted for normalized
coordinates, so the initial experimental naturality theorem was rejected and
removed rather than delivered. Zero quotients, empty affine charts, degree zero,
and identity basic inclusions are covered by the remaining construction and by
the existing homotopy theorem without additional hypotheses.

## New nodes

`new-h3-self-tor-nonpositive-chosen-comparisons` states the affine geometric
construction with compatibility for one chosen augmented lift per basic inclusion.
It keeps the original chart tensor calculation and restriction-square argument,
and adds the existing quotient resolution tensor comparison as the source of
these chosen lifts. It does not depend on the item being proved. No change record
is needed: no existing statement, definition, or public import was changed.


## Second reading by H3

1. **Unchanged interface: pass.** Read the complete diff against the repository.
   Independently compared the text from `theorem
   exists_selfTor_nonpositive_flat_sections` through its final conclusion: it is
   byte-for-byte identical before `:= by`. Its docstring, public imports and
   visibility also stay unchanged. The only additional declaration is the
   reported chosen-comparison theorem; there are no definition changes or forced
   adaptations and no change record is required.

2. **Kernel proof and remaining hole: pass as a decomposition.** Compiled both
   modules together through `lcompile.py --all`, without compiler errors or
   warnings (6.5 and 12.4 seconds). Independently compiled a scratch copy with
   `#print axioms` for both delivered theorems and the homotopy dependency.
   The delivered theorems use only `propext`, `Classical.choice`, `Quot.sound`
   and the reported `sorryAx`; the homotopy theorem uses only the first three.
   The only source hole is the named public chosen-comparison theorem, whose
   entire proof is `by sorry`. No axiom declaration, unsafe/opaque declaration,
   extern, implemented_by, definition, or arbitrary witness construction was
   introduced. Obtaining existential witnesses occurs inside a theorem proof,
   not in a data definition. One upper hole closes and one lower hole is added;
   the full geometric result is still open.

3. **Split truth and usefulness: pass.** Read the chosen-comparison signature,
   its entire docstring and node, the proved quotient-resolution tensor comparison,
   and the proved tensor-lift homotopy theorem. Checked Stacks Tags
   [08DX](https://stacks.math.columbia.edu/tag/08DX),
   [06YG](https://stacks.math.columbia.edu/tag/06YG),
   [06YB](https://stacks.math.columbia.edu/tag/06YB),
   [01I9](https://stacks.math.columbia.edu/tag/01I9), and
   [00LS](https://stacks.math.columbia.edu/tag/00LS).
   The first two zigzag legs use the K-flat *other tensor factor*, so they do
   not mistakenly assume that the quotient concentrated in degree zero is flat
   or K-flat. Restriction of scalars preserves exactness; it need not preserve
   projectivity. The source projectivity suffices for augmented lifts.
   For I = top or empty charts the quotient and homology vanish; for n = 0 the
   same augmented comparison gives the usual quotient product; identity basic
   inclusions use the identity comparison up to the proved homotopy. No
   noetherian, regular-sequence, finite-rank or extra flatness hypothesis is used.
   The new theorem retains the geometric calculation but asserts a restriction
   square for one lift; the item proves the additional arbitrary-lift assertion
   by quotient-map uniqueness and an actual tensor homotopy. It is not an
   application of a renamed theorem with the same quantified conclusion.
   Independent searches used leanfinder for natural affine sections of tensor
   homology, loogle for `HomologicalComplex.homologyMap`, and grep for
   `tilde.*homology|homology.*tilde`, as well as local `rg` with Tor/flat/homology
   and self-Tor names. Mathlib hits concern general homology maps, algebraic Tor,
   flat scheme maps and sheaf cohomology, not this geometric comparison.
   The existing self-Tor parent results depend on the item, so cannot replace it.
   Closing the geometric split is not a few-minute consequence of the available
   interfaces: constructing the normalized tensor zigzags and restriction square
   remains necessary.

4. **Route and pruning: pass.** The item opens its original hole, uses the chosen
   geometric square, and proves independence algebraically via the already
   proved `ModuleCat.quotient_tensor_resolution_lift_homotopy` and Mathlib's
   `Homotopy.homologyMap_eq`. Its two proof imports are used; all existing public
   imports stay unchanged. The split retains the geometric dependency imports
   as its proof plan. Compared the old and new `proof_deps`: all nine old nodes
   are listed above as moved below the split, not globally pruned. Read
   `dag/units/sk-thm-picard-duality.json`: its existing `realized` arrays are
   empty and are untouched. This below-unit reduction retains the affine
   self-Tor calculation and the ancestor chain; it bypasses no realized unit
   statement or step.

5. **Lean/DAG agreement: pass.** The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`: the steps are chosen coordinates,
   quotient-mk surjectivity, then tensor homotopy and homology equality, exactly
   as in Lean. Its dependencies are precisely the chosen-comparison and
   tensor-lift-homotopy nodes. The new node has source, full proof steps, their
   dependency union, recorded searches, status `split`, creation metadata,
   blueprint provenance, chapter/unit and the verbatim Lean declaration record.
   Its proof depends only on the original geometric ingredients and the existing
   algebraic lifting theorem, never on the item it helps prove.

Second reading changed only this report: added the independent review and made
its pruning inventory explicit for both affine tilde nodes. The Lean proofs and
node files required no repair. The scratch axiom-check copy was removed.
