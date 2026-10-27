## What changed

Retained the previous attempt's explicit three-cell associativity proof and joint naturality
argument, together with its proved square-support, system-support, and integral pullback
compositor calculations. Repaired the localization rewrite in
Sheaf.SixFunctors.IntegralSystemCompositorAssociativity. The factorization calculation now
uses a proved private generic lemma over abelian categories, avoiding repeated unfolding of
the concrete coefficient-system categories.

Moved the original component notation, including every original definition body, to
Sheaf.SixFunctors.CompositionProjectionData and publicly reexported it from the item. This lets
Sheaf.SixFunctors.TriangleProjectionCompositorContraction be a separate theorem module without
an import cycle. The item's existing public statement is unchanged.

The complete proof of compositionProjectionMate combines the contraction equation with
invertibility and naturality, and separately proves three-cell associativity by expanding the
prescribed compositors, vertical/horizontal pasting, naturality and endpoint transports.
System associativity is transferred from the section-normalized pullback compositors through
adjunction conjugation. The system invertibility proof detects isomorphisms by evaluations;
it never claims that evaluations are faithful on derived morphisms.

Change record: coord/changes/U7-composition-projection-data.md.

## Proved and sorry left

Original item: one hole, compositionProjectionMate. Its proof is now complete from the named
steps, so one of one original holes is closed by decomposition. Two holes are added, so this
packet does not claim a net reduction of the sorry ledger.

Remaining holes, each the whole proof of a public theorem in its own module:

- AlgebraicGeometry.ProEtale.ordinaryProperOpenMateIsIso in
  Sheaf.SixFunctors.OrdinaryProperOpenInvertibility
  (lem-sf-ordinary-proper-open-invertibility).
- AlgebraicGeometry.ProEtale.CompactCompositionProjection.triangleProjectionCompositorContraction
  in Sheaf.SixFunctors.TriangleProjectionCompositorContraction
  (lem-sf-triangle-projection-compositor-contraction).

Additional proved public declarations:

- AlgebraicGeometry.Scheme.ProperOpenSquareSupport.derived_support_square
  (lem-sf-proper-open-square-derived-support).
- WeilConjectures.IntegralSystemRealization.systemProperOpenSupportedCounit and
  WeilConjectures.IntegralSystemRealization.systemProperOpenGammaIsIso
  (lem-sf-system-proper-open-support).
- WeilConjectures.IntegralSystemRealization.integralSystemCompositorAssociativity
  (lem-sf-integral-system-compositor-associativity).

The new square-support, system-support, contraction statement and integral-compositor modules
have passed single-file compilation. The existing component definitions were checked byte for
byte after comment masking; their bodies are identical after relocation.

The lower holes separate the proper/open invertibility argument from the triangle tensor
contraction. They assert neither the original conjunction nor three-cell associativity.
The assembly and its naturality/associativity proofs are actual Lean calculations.

## No longer needed

Removed proof imports:

- WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian moves to the data module, where the
  existing spaceNoetherian proof still uses it.
- Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower,
  WeilConjectures.Compactification.CategoryBaseChange,
  Sheaf.Compactification.NagataSketchClosure: the statement fixes the triangle and three-cell
  grid, so its associativity equation follows directly from pasting; no new tower is chosen.
- Sheaf.SixFunctors.OpenTensorNormalization, Sheaf.SixFunctors.ProperOpenProjectionMate,
  Sheaf.Paper.SemilinearDerivedSections, Sheaf.Paper.RingedProjectionCanonicalNormalization,
  Sheaf.SixFunctors.TriangleProjectionNormalForm: no separate import needed by the final
  assembly; the contraction task retains the normal-form/open-normalization dependencies.

The revised item proof does not use lem-sf-cartesian-closure-refinement,
lem-cbc-compactifiable-compatible-tower, lem-cbc-compactifiable-cofiltered,
lem-sf-three-cell-compositor, or lem-sf-refinement-projection-counit.
The generic three-cell calculation replaces the three-cell node for this supplied grid.
Refinement and existence lemmas remain in the project for other consumers; no module is
withdrawn and no source-library declaration is removed. Existing public imports are preserved.
The ringed tensor-composition and open-normalization nodes remain dependencies of contraction;
Noetherianity remains in the unchanged component notation. None is claimed globally pruned.

Removed retained exploratory private lemmas ordinary_pi_comp, system_pi_comp,
ordinaryTensorPull, pi_comp_of_tensor, and left_tensor_projection_comp, which the actual assembly
never called. Their expected role is documented in the contraction task's natural-language proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left missing metadata and put the contraction hole in the item module;
this packet supplies the separate module, nodes and change record. Its previous disk-space
failure is no longer occurring: remote validation now reaches Lean diagnostics.

The item's original proof plan does not provide invertibility of the prescribed mate, even
though TriangleLaws requires it; reviewed_lean already flags this gap. Ordinary unbounded
invertibility is now a separate named theorem with the support/adjunct proof, while system
invertibility is proved from square support and the recorded open adjunct. The existing
ProperOpenDerivedSupport theorem has a common source for both opens; it cannot directly prove
the system square case, so the delivered square theorem generalizes that proof with both sources.

The supplied three-cell equation needs no choice of Cartesian refinements. Direct expansion
of the prescribed gamma and compositors suffices, with no change to the unit route or its
statement (the unit's realized statement/steps lists are empty). Empty source schemes and zero
inputs impose no additional nonemptiness hypothesis in any new statement. Identity arrows and
zero maps are included in every categorical calculation. The contraction has arbitrary inputs
and retains both successive pullbacks; the invertibility task has the exact finite-ring and
proper/quasi-compact-open hypotheses of its intended use.

Mathlib searches: retained LeanFinder and Loogle searches found generic counit/mate lemmas;
new LeanSearch found only ordinary scheme-module pushforward composition and geometric
properness results; grep found isIso_counit_app_of_iso. No matching project-level contraction
or arbitrary unbounded proper/open invertibility theorem was found. Existing system
invertibility statements were checked and require bounded constructible origins, so they do
not supply the ambient theorem used here.

## New nodes

- def-sf-composition-projection-data: unchanged existing component notation in an importable
  module, plus TriangleEquations.
- lem-sf-ordinary-proper-open-invertibility: invertibility of the ordinary canonical mate;
  one remaining hole with its support and adjunct proof.
- lem-sf-proper-open-square-derived-support: proved support assertion for distinct open sources.
- lem-sf-system-proper-open-support: proved supported counit and invertibility of the specified
  intrinsic system gamma.
- lem-sf-integral-system-compositor-associativity: proved coherence of the recorded pullback
  compositors using sections, adjunctions and localization.
- lem-sf-triangle-projection-compositor-contraction: the remaining tensor/counit contraction,
  separated from invertibility, naturality and three-cell associativity.

Change record: coord/changes/U7-composition-projection-data.md.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
