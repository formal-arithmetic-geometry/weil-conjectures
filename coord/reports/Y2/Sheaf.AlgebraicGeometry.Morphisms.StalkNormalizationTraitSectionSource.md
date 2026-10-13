## What changed

Replaced the single sorry in
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource` with a complete
Lean assembly, preserving its public signature and its existing docstring. Added a fully
proved private helper `AlgebraicGeometry.Scheme.stalk_dvr`. It excludes a field stalk using
`Scheme.range_fromSpecStalk` and `fromSpecStalk_closedPoint`, converts the dimension bound
to `Ring.KrullDimLE 1`, constructs the Dedekind-domain instance from normality, and applies
`IsDiscreteValuationRing.TFAE`.

Added two separate statement modules, each with exactly one named public sorry:
`StalkNormalizationTraitFlat` states global flatness of the local tame normalization
without a section or a rational point; `StalkNormalizationTraitSectionUnramified` states
formal unramifiedness on a source open above the closed section. Both take a DVR stalk,
rather than asking their future prover to redo the dimension reduction. The original
proof supplies that DVR hypothesis using the proved helper.

The assembly restricts the global flatness to the source open supplied by the second
statement. Mathlib proves local finite presentation: the stalk is Noetherian, its
spectrum is locally Noetherian, the smooth pullback is locally Noetherian, and a finite
morphism into it is locally of finite type and hence locally of finite presentation.
Open inclusions preserve flatness and local finite presentation under composition.
`Etale.of_formallyUnramified_of_flat` then gives the exact original conclusion.

The two new statement modules and the item compile together without warnings through
lcompile.py. The remaining hard inputs are classical tame normalization and its
uniformizer test, read directly in Stacks Tags 0EYG, 0EYH, 0EYI(2), and 0EYJ. No target,
existing public signature, definition, or public import changed. No forced adaptations.

## Proved and sorry left

Hole closed:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_source`, node
`lem-sbc-stalk-normalization-trait-section-source`.

Holes added and still left:
- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_flat`, node
  `lem-sbc-stalk-normalization-trait-flat`.
- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_unramified`, node
  `lem-sbc-stalk-normalization-trait-section-unramified`.

This is a decomposition of one upper hole into two lower geometric statements, not an
axiom-free proof of the item. The raw change is one hole closed minus two added, hence
minus one; it is not claimed as a net reduction of the sorry count. The private
`AlgebraicGeometry.Scheme.stalk_dvr` proof and the final combination contain no sorry.
There are no other new declarations or holes, and no data is chosen from an unproved
existence theorem.

The lower statements isolate different mathematical obligations. Flatness asserts a
property on the entire normalization and does not assume a section or split fibre.
Formal unramifiedness asserts vanishing of relative differentials near the section and
does not assert flatness or etaleness. A standard tame algebra A[T]/(T^e-pi), with e > 1
invertible, is free of rank e over a DVR A but ramified at its closed point: this tests
why the flatness conclusion alone does not prove the item. Such a factor fails the
split generic section hypothesis, since a putative root would have valuation 1/e.
The e = 1 case passes both conclusions. Products handle disconnected covers, and an
empty section fibre gives a vacuous universal assertion. The field-stalk edge case is
excluded by the explicit Lean contradiction, without using hmin.

## No longer needed

Removed the item's proof imports:
- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`, node
  `lem-sbc-normal-integral-generic-hom-full`.
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`, node
  `lem-sbc-generic-fibre-action-extension`.

Neither new statement imports them either. After restriction to the DVR stalk the
punctured local base is its generic point, so the cartesian comparison identifies the
punctured cover directly with the corresponding base change of Z. Its G-action and
torsor identity are already supplied by Z; there is no need to extend an action over a
larger punctured open in this dimension. This removes these two dependency edges for
this item; it does not claim that other targets or sibling modules cease to need them.
No unit statement or unit step is bypassed, and no existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

The previous proposed core restated the original conclusion with an automatic
open-immersion conjunct. It has not been restored. Here the DVR reduction is actually
proved, and two strictly separate properties are combined by Mathlib's etale criterion.

The existing DAG proof was one paragraph with dependencies only for extending generic
morphisms and actions. Those declarations do not provide the tame flatness or
split-section differential calculation. The new nodes state precisely these missing
parts, with complete proofs in words and the sources of the corresponding steps.
The trait case also does not need the planned generic action extension once its
punctured base has been identified with the generic point. The updated item node
records the actual private DVR proof and flat/unramified assembly.

Searches were made in Mathlib, both source-library roots, and the whole DAG before
creating the nodes. LeanFinder returned normalization universal-property results for
flatness and unramified algebra/locus results for the section calculation, with no
matching scheme theorem. Direct Mathlib AlgebraicGeometry grep found no normalization
flatness or normalization unramifiedness theorem. Both requested LeanSearch queries
returned Internal Server Error; their unavailable results are recorded honestly.
Blueprint searches for tame normalization flatness and Tag 0EYI returned no nodes.
The existing `FiniteNormalTraitPurity` requires an etale open already meeting the
closed fibre, so it cannot supply this item's missing section neighbourhood.

## New nodes

`lem-sbc-stalk-normalization-trait-flat`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationTraitFlat.lean`.
The trait stalk is assumed to be a DVR, and no section or rational point is assumed.
Tame local normal forms from Tags 0EYG and 0EYH are finite free, which descends to
flatness of the concrete localized relative normalization.

`lem-sbc-stalk-normalization-trait-section-unramified`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationTraitSectionUnramified.lean`.
The split generic section fibre forces every exponent in a tame normal form above the
closed section point to be one, as in Tag 0EYI(2). Its differential module consequently
vanishes, and the unramified locus supplies the source opens. Flatness is left to the
other node and is not part of this conclusion.

Both nodes belong to `sec-smooth-base-change`, unit `sk-prop-input-spreading`, with the
same nearest blueprint ancestor as the item. No change record is required: existing
interfaces are preserved and the added public statements live in new modules.

## Second reading by Y2

1. Compared each delivered module with the repository. The target theorem signature, binder order,
visibility, definitions, and all existing declarations are unchanged byte for byte. The two additional
modules are new split-off statement modules. The changed item imports the two new modules and the DVR
characterization only for its proof; the removed generic-extension imports are no longer referenced.
Verdict: no accidental interface change.

2. Compiled all three modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all` and obtained
exit code 0 with no warnings. The only remaining `sorry`s are the two named lower theorems listed above;
there is no `sorry` in a definition, and no axiom, unsafe, opaque, extern, implemented_by, or
`debug.skipKernelTC`. The proved item depends on `sorryAx` only through those explicitly split statements;
the private `stalk_dvr` helper is proved. Verdict: compilation and axiom conditions pass subject to the
open lower nodes.

3. Read both new statements against their Lean signatures and checked edge cases in the docstrings.
The flatness statement omits section and rational-point hypotheses, while the unramifiedness statement
retains exactly the split-section data and concludes only formal unramifiedness. They are strictly
weaker obligations than the item and are not restatements of its conclusion. The item combines them
with the standard flat-plus-formally-unramified etale criterion. Verdict: both split statements are
true as stated and exactly the needed decomposition; their source and proof prose match the intended
trait argument.

4. Checked the updated item node, the two new node files, their Lean records, and the unit record.
The item proof steps use precisely the two split nodes; the old generic-action and generic-morphism
nodes are removed from `proof_deps` and are listed as pruned. The unit remains
`sk-prop-input-spreading`, and no unit statement or realized step is bypassed. Verdict: DAG route and
pruning agree with the Lean proof.

5. Searched the repository and Mathlib declarations for existing normalization-flatness or
normalization-unramifiedness results, and reviewed the listed LeanFinder/LeanSearch results. No existing
theorem supplies either split statement. The `stalk_dvr` construction uses the local-spectrum range
and the DVR TFAE directly, with no arbitrary witness. Verdict: no duplicate theorem or hollow data
construction found.

Changes made during this second reading: appended this review to the report and retained the delivered
proof and split nodes unchanged.
