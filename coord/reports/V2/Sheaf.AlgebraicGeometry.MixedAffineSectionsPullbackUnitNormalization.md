## What changed

The assigned module constructs the pullback complex model with the pinned counit,
proves the sections comparison on its termwise affine chart, and composes the resulting
isomorphism with the inverse sections comparison. Private proved helpers transport
invertibility of a left-derived counit and of a sections unit across isomorphisms,
and cancel an invertible morphism in the normalization equation.
The generic sections/counit/Leray factorization is isolated in the new module
Sheaf.AlgebraicGeometry.MixedPullbackSectionsCounitUnit. Existing signatures,
visibility, public imports and definitions are unchanged.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization
(lem-sc-mixed-affine-pullback-unit-normalization).
Added and left: AlgebraicGeometry.mixedPullback_sections_counit_unit
(lem-sc-mixed-pullback-sections-counit-unit).
This is a decomposition: one upper hole is replaced by one strictly algebraic
unit-factorization hole. The K-flat model, chart transport, construction of b and
inverse cancellation are proved here. No sorry remains inside the assigned proof.
No definition contains sorry. Existing dependency theorems retain their own holes.

## No longer needed

Removed import: Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison.
Its node lem-pc-affine-kflat-pullback-chart-comparison and theorem
AlgebraicGeometry.affine_kFlat_pullback_chart_comparison are no longer used by
this proof. The termwise square uses adjunction uniqueness, toSpecGamma naturality
and tensorPullback composition directly; the derived model uses the original
counit and uniqueness of left derived functors. All other original imports stay.
This prunes this dependency edge; other targets may still need that module.
The unit realization record has empty realized lists, so no required unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The chart comparison only asserts an unnormalized Nonempty isomorphism. It does not
supply the normalized counit needed for the pinned derived adjunction. Its geometric
components suffice, but the pinned counit is handled separately by uniqueness.
The initial cache lacked MixedAffineSectionsComplexUnit.olean; a later automatic
refresh supplied it. No dependency source was copied into the delivery to work around this.
The cited Stacks sources were checked at the online [Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0),
[Tag 08DW](https://stacks.math.columbia.edu/tag/08DW),
[Tag 079W](https://stacks.math.columbia.edu/tag/079W), and
[Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T).
Zero complexes and empty schemes are included; the new lemma assumes no affine,
K-flat, boundedness or invertibility condition, and w and wA remain independent.

## New nodes

lem-sc-mixed-pullback-sections-counit-unit records the generic sections/counit
factorization, in Sheaf.AlgebraicGeometry.MixedPullbackSectionsCounitUnit. It has
no existence conclusion, no affine model and no invertibility conclusion. Its
hypothesis is the underived Hom-equivalence factorization, supplied in the parent
by exists_schemeDerivedAdjunction at the identity. Its proof is the explicit
naturality and localization-factor calculation in the original node step 3.
LeanSearch was unavailable; LeanFinder, Loogle and source searches found the
component naturalities but no existing declaration of this composite identity.
No change record is needed because no existing interface is changed.

Change record: coord/changes/mixed-affine-normalization-proof-elaboration.md documents
proof-local elaboration commands conservatively classified by preflight as interface edits.

## Second reading by V2

1. Compared both delivered modules with the repository versions. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof bodies, proof-only imports, and the newly split theorem/module were added. Verdict: pass.

2. Compiled `MixedPullbackSectionsCounitUnit.lean` and `MixedAffineSectionsPullbackUnitNormalization.lean` with `lcompile.py`; no compiler errors or warnings were reported. The only remaining `sorry` is the named split theorem `AlgebraicGeometry.mixedPullback_sections_counit_unit`, and no definition contains `sorry`. Verdict: pass.

3. Checked the split statement against its Lean type and DAG node. It is a generic sections/counit naturality factorization, strictly weaker than the affine normalization target, with no affine, K-flat, or invertibility assumptions. Searches in the library and Mathlib found no duplicate declaration. Verdict: pass.

4. Checked the proof route from the target downward: K-flatness, derived counit uniqueness, affine chart sections isomorphism, and inverse cancellation are used as recorded. The removed `AffineKFlatPullbackChartComparison` import and dependency are genuinely unused. Verdict: pass.

5. Checked node metadata and the unit route. The target node proof/proof_deps match the declarations and imports, and the new node records its source, proof steps, Lean declaration, and split status. No unit step is bypassed. Verdict: pass.

Changed during second reading: no Lean statements or proofs; appended this review record only.
