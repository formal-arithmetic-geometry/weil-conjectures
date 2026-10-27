## What changed

Proved `AlgebraicGeometry.Etale.ordinaryFiniteP1_kummer_maps` with its original
statement. The proof computes the actual Kummer class of O(1), treats arbitrary
finite coefficients by cyclic devissage, proves the map is an isomorphism on
algebraically closed fibres, and uses proper exchange and conservative geometric
pullbacks for the relative result. The infinity section splits the unit component;
scalar faithfulness of the Chern class handles the other homology degree.

For base change, the proof applies the existing declarations
`ordinaryFiniteP1_twisted_unit_baseChange` and
`ordinaryFiniteP1_chern_adjunct_baseChange`, then combines their equations by the
biproduct universal property. Their modules do not import this item. The supplied
Chern-family specification supplies exactly the two component specifications.
All added proof imports are private. Proved private lemmas keep generic functor
and Ext identities abstract and record the fibre and relative arguments. Derived
pullback linearity proves scalar naturality without unfolding its construction.
No existing public definition or statement is changed.
The proved scalar-class, adjunct, and Tate-coefficient APIs record the expensive
comparison arguments separately. Their concrete definitions stay unchanged;
generic identities and closed functor definitions avoid repeated elaboration of
derived localization data. The homology-monomorphism argument is generic over a
projective object and is specialized to the constant unit on a geometric point.

Added the proved theorem `projectiveLine_constant_coefficient_generator` in
`Sheaf.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator`. Its argument
is independent of the projective-line decomposition: reduction of cyclic
coefficients is surjective in degree two because degree three vanishes; finite
abelian devissage then extends the generator to all finite coefficients.
Updated the item's DAG proof and dependencies to this route.

Validation: `lcompile.py --all` accepted all eight files under the unchanged
60-second per-file gate. A source comparison checks that all eight original
public signatures are unchanged. Development profiler options were removed for
the delivery check. Every originally planned direct dependency removed from this
node is named below; no library module is withdrawn.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.ordinaryFiniteP1_kummer_maps`
(node `lem-asd-ordinary-finite-p1-kummer-maps`). No holes remain in the item.
Added zero holes: `projectiveLine_constant_coefficient_generator`,
`ordinaryFiniteClass_scalar_faithful`,
`ordinaryFiniteP1ChernPushforward_scalar_faithful`,
`ordinaryFiniteP1KummerClass_scalar_bijective_of_normalization`, and all their
helpers are proved. The new `ordinaryFiniteUnit_mono_homology_zero` is proved, and
`ordinaryFinitePushforward_single_shift_homology_iso` is an explicit composite of
the existing canonical comparison isomorphisms, with no holes.
The new `ordinaryFiniteP1_fibre_target_card` is also proved.
This is one of one
original holes closed, with
zero unproved statements split off. Existing imported statements are used as provided by the
library, including the two component base-change declarations and the geometric
cohomology inputs. This delivery does not claim their holes are closed.

## No longer needed

The original four private proof imports are retained. The new proof does not use
the following originally planned direct proof dependencies:

- `def-pc-divisor-line-bundle` and `lem-asd-ordinary-supported-kummer`: the degree
  trace and naturality of the actual Picard/Kummer class replace supported classes.
- `lem-amb-proper-coproducts-projection`,
  `lem-weil-pbc-ringed-exchange-tensor-coherence`, and
  `lem-asd-proper-finite-coefficient-extension`: cyclic devissage replaces derived
  scalar extension and the projection formula.
- `lem-amb-kummer-any-base`: Kummer-class pullback is encapsulated by the existing
  Chern-adjunct component equation.
- `lem-asd-ordinary-finite-class-comparison`: the existing Chern-adjunct base-change
  declaration supplies the required component equation directly.
- `lem-asd-finite-etale-twist-line`: the local-line API supplies the geometric
  trivialization. The line universal property from
  `lem-asd-etale-finite-twist-pullback` remains needed inside the proved
  Tate-coefficient helper, rather than as a direct dependency of the item.
- `lem-weil-pbc-closed-immersion-proper`,
  `lem-weil-pbc-fibre-product-affine-spectra`,
  `lem-weil-pbc-projective-space-standard-charts`,
  `lemma-nagata-projective-space-base-change-proper`, and `pqf-lem-locnoeth-lft`:
  the infinity-section and existing projective-line geometric APIs replace the
  proposed chart argument. Properness is supplied by existing instances.

The separate constant-transition coefficient comparison
`lem-weil-pbc-constant-module-transition-coefficients` and its private import are
also unnecessary: the adopted `exists_eq_smul_id_of_iso` gives the scalar
description of rank-one endomorphisms directly. The redundant direct import of
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` was removed.

The direct imports of `FiniteEtaleTateLocalLine`, the adopted derived
`AlgClosedField` module, `KunnethMap`, and `HomSingleProjective` are now supplied
through the proved comparison helpers where needed. In particular the point's
Tate trivialization reuses `kummer_line_as_constant` over the identity map rather
than repeating its primitive-root construction. The local-line dependency remains
inside the Tate-coefficient helper and is removed only from the item's direct plan.

These are removals from this node's direct proof plan. No module is withdrawn;
transitive imports and other consumers may still need these declarations.

## Where the brief, the DAG or earlier work was wrong

The proposed proper finite coefficient extension route would import a chain back
through the ordinary projective-line input itself. The direct finite-abelian
coefficient argument avoids that circular route and uses the adopted cyclic
cohomology APIs. The unit's realized route is preserved. No target statement,
Kummer normalization, or geometric hypothesis is changed.

## New nodes

`lem-sp-projective-line-constant-coefficient-generator` records the independently
proved finite-coefficient generator theorem, including its source, full argument,
Mathlib searches, and Lean attachment. It leaves no work to a later session.

`lem-sp-ordinary-finite-class-scalar-faithfulness` records the proved compatibility
of scalar precomposition with the ordinary cohomology class comparison, followed
by injectivity of the scalar orbit. It exposes a small proved API for the existing
class construction and leaves no hole. No change record is required because no
existing statement or definition changes.

`lem-sp-ordinary-finite-adjunct-scalar-faithfulness` records the proved adjunction
transposition of scalar faithfulness. Its public statement retains the specified Chern pushforward arrow, whose
canonical adjunction is unfolded only in this helper. This avoids repeating that
derived-localization conversion in the item.

`lem-sp-projective-line-tate-coefficient-generator` records the proved passage
from the normalized roots-of-unity class to the finite Tate-coefficient scalar
orbit. The existing normalization theorem remains in the item with its original
signature and supplies this helper's normalization hypothesis. Both new helpers
are proved and introduce no remaining obligations.

`lem-sp-ordinary-finite-geometric-point-homology` records the proved criterion
that scalar faithfulness of an arrow from the point's constant unit makes its H0
map monic. Its private helpers include the finite-cardinality criterion and the
constant-unit H0 sections comparison used in the item.

`def-sp-ordinary-finite-fibre-homology-comparison` records the actual composite
of shift, homology, exact point-sections, and derived direct-image/global-sections
comparison isomorphisms. The construction has no choice of an unproved witness.
These two modules isolate measured expensive derived-instance comparisons; they
leave no new obligations. Their added proof imports in the item are private.

`lem-sp-ordinary-finite-p1-fibre-homology-card` records the proved passage from
the scalar generator in H2 and the constant H0 calculation to the two fibre
homology cardinalities. Its generator hypothesis is supplied by the already
proved Tate-coefficient API and the unchanged normalization theorem in the item.
This is a proper part of the geometric-fibre argument, and leaves no hole.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
