## What changed

Closed the local proof hole in
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_isAffine` by applying the existing
upstream declaration `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`.
The latter's `HasTorsionCohomologicalDimensionLE` definition unfolds to the displayed field
hypothesis and `Sheaf.H` conclusion. All existing signatures and public imports are unchanged.
One private proof import replaces the unused private proof imports listed below.

The upstream declaration is still unproved. This delivery reuses an existing open affine bound;
it does not claim to prove Artin vanishing or its induction argument. The DAG retains
`thm-sc-affine-torsion-cd` as its mathematical proof dependency, and identifies the exact alternate
upstream declaration used, rather than claiming an elementary proof with no dependencies.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_isAffine`.
Holes added: none. No `sorry` remains in the delivered module; no theorem is split off.

The existing upstream theorem
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine` remains `sorry` in
`WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension`. Accordingly,
`#print axioms` for both declarations reports `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`. The local hole is closed conditional on this existing open dependency; this is not a
completed proof of the import closure. Closure progress and global pruning belong to the pinned
sorry ledger, not the count of local holes or removed imports.

## No longer needed

Removed unused private proof imports:

- `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`

Added private proof import:
`WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension`.

No old DAG proof dependency is removed: the sole old dependency `thm-sc-affine-torsion-cd`
is still needed, through its existing upstream affine-bound declaration. No DAG node or module
is claimed globally pruned. The removed imports need not leave the target closure if other modules
still import them.

## Where the brief, the DAG or earlier work was wrong

The original module's docstring said there was no Lean declaration of the affine theorem. There
is one in the upstream module, with the exact bound needed here, although its proof is `sorry`.
The first worker correctly found this shorter existing-library application, but described it
without disclosing its open proof and erased the mathematical dependency from the node. That
would hide the unresolved affine argument. The second reading restores the dependency and
corrects the progress and pruning claims. No statement or definition is changed.

## Second reading by F2

1. Compared the sole delivered Lean module with the shared repository using `diff`; checked the
   existing theorem signature byte for byte. Verdict: unchanged signature, visibility, public
   imports, hypotheses and conclusion; no definition or target change and no change record needed.
2. Compiled the module locally with `lcompile.py` without errors or warnings. Inspected the
   one-line proof and the upstream theorem and bound definition. A scratch copy with
   `#print axioms` confirms only the three allowed axioms and `sorryAx`, coming from the existing
   upstream affine theorem. No direct `sorry`, forbidden axiom, unsafe declaration or hollow
   definition is introduced. Verdict: valid application of an existing open dependency, not an
   axiom-complete proof.
3. No new statement or split-off hole exists, so new-node/source/search obligations are vacuous.
   Checked the upstream declaration and the local affine-bound declarations by name and by the
   `HasTorsionCohomologicalDimensionLE`/`Sheaf.H` definitions. The application works uniformly for
   dimension zero, empty X and arbitrary q satisfying hq: no nonemptiness or positive-dimension
   hypothesis is supplied. Verdict: no stronger hypothesis or weaker conclusion is smuggled in.
4. The proof already uses the exact existing upstream theorem, the shortest application found.
   Its single added import is private and necessary. Existing public statement imports stay
   unchanged. All 19 removed private imports are named above. The unit `sk-prop-sf-cbc` has empty
   `realized.statement` and `realized.steps`; this delivery changes neither the unit record nor
   its route and retains the affine-bound dependency. Verdict: no unit bypass or globally
   established pruning; only unused direct proof imports removed.
5. Compared the node and Lean proof. Restored `thm-sc-affine-torsion-cd` in both `proof_deps`
   and the proof step's `uses`, and named the precise existing upstream declaration and its
   unresolved proof. `proof_origin` points to that source module. The unchanged Lean statement
   record still matches the signature. Verdict: metadata now discloses the actual mathematical
   dependency and the remaining hole; no new nodes.

Second reading changed the node's proof/dependency account and this report. The compiling Lean
proof itself required no repair.
