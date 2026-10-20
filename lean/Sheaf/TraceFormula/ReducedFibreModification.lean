/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.Separable

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.TraceFormula.ValuationReducedFibreNormalization
import Sheaf.AlgebraicGeometry.QcqsSeparableRiemannZariskiRefinement
import Sheaf.TraceFormula.FiniteEtaFlatification
import Sheaf.TraceFormula.FiniteEtaModificationGluing
import Sheaf.TraceFormula.FiniteEtaModificationSpreading

/-!
# Reduced fibres after a separable alteration

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, pp. 21–24,
with the integral qcqs convention of §1.2 and the generic-isomorphism meaning in §3.5
(blueprint: lem-trf-reduced-fibre-modification).

For a nonflat input the finite map is required to be an isomorphism on the generic
fibre. An isomorphism over schematically dense opens of both total spaces would
incorrectly retain arbitrary vertical components of the input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A dominant finitely presented family with geometrically reduced generic fibre has a
finite generic-fibre isomorphism from a flat finitely presented family with reduced
geometric fibres, after a separable alteration of its integral qcqs base.

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, pp. 21–24;
§3.5, opening paragraph, specifies properness and generic invertibility, including
nonflat inputs (blueprint: lem-trf-reduced-fibre-modification).

Proof plan, following the nine DAG steps:

1. Use the finite generic-isomorphism flatification conclusion of
   `lem-trf-finite-eta-flatification` (Temkin, Step 0, Raynaud–Gruson flattening).
   Write its maps as `S₁ → S` and `Z → X ×[S] S₁`. The base remains integral qcqs by
   `lem-weil-pbc-qcqs-morphism-permanence`, and the generic fibre of `Z` is the original
   geometrically reduced generic fibre. The extra dense-open clause currently in that
   dependency is unnecessary and needs its own correction for nonflat inputs.
2. Choose finite affine covers of `S₁` and their inverse images in `Z`. The affine
   criterion `lem-weil-pbc-flat-morphism-affine-criterion` gives flat finitely presented
   chart algebras. Pull these to every centred valuation ring in a separable closure
   of the generic field. Use `lem-pc-relatively-flat-module-pullback`,
   `lem-weil-pbc-qcqs-morphism-permanence`, and
   `lem-trf-geometric-reduced-fibre-locus-base-change` to retain the hypotheses.
3. Apply `lem-trf-valuation-reduced-fibre-normalization` to each chart over each such
   valuation ring. Its relative integral closure is finite, flat and finitely presented,
   generically unchanged, and has reduced geometric fibres, including arbitrary height.
4. Spread this finite algebra and its properties by
   `lem-trf-finite-eta-modification-spreading` to an integral affine quasi-model. The
   affine flatness criterion `lem-weil-pbc-flat-ring-map-iff-flat-affine` converts the
   algebraic output to the asserted flat scheme morphism.
5. Apply `lem-trf-qcqs-separable-riemann-zariski-refinement`. Quasi-compactness selects
   finitely many quasi-models; a common model `T → S₁` refines them. Its generic field
   is finite separable over the original one, and the relative open-cover clause gives
   the required covering over each base chart.
6. Pull the local finite maps back to the covering opens in `T`. Finiteness survives
   by `lem-trf-finite-radicial-basechange`, flatness by
   `lem-pc-relatively-flat-module-pullback`, finite presentation by
   `lem-weil-pbc-qcqs-morphism-permanence`, and reduced geometric fibres by
   `lem-trf-geometric-reduced-fibre-locus-base-change`. Fibres outside these opens are
   empty and reduced. Generic identifications persist.
7. Use `lem-trf-finite-eta-modification-gluing` after an additional finite birational
   base modification `S' → T`. Unique overlap identifications satisfy the cocycle
   condition and glue the local finite maps to `Y' → Z ×[S₁] S'`, retaining flatness,
   finite presentation, reduced geometric fibres and generic invertibility. No
   normality of `T` or `S'` is used.
8. Compose the base maps using `lem-weil-pbc-proper-composition`. Their composite is
   proper surjective, and its generic fibre is the spectrum of the finite separable
   generic field of `T`. Compose the finite maps using
   `lem-trf-finite-radicial-basechange` and `lem-weil-pbc-finite-composition`. This gives
   the required finite map to `X ×[S] S'`. Its actual induced generic map is invertible
   since both factors are invertible there. The properties over `S'` come from step 7.
9. Flatness over the integral base implies schematic density of the generic fibre in
   the source: localize affine sections at the nonzero base elements and apply
   `lem-sc-flat-invertible-sections-torsion-free` with the structure sheaf to show that
   a section vanishing generically vanishes. This does not assert generic density in
   the original nonflat target.
-/
theorem exists_reduced_fibre_modification
    {S X : Scheme.{u}} [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (η : S) (hη : IsGenericPoint η Set.univ) (f : X ⟶ S)
    [IsDominant f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyReduced (f.fiberToSpecResidueField η)] :
    ∃ (S' : Scheme.{u}) (_ : IsIntegral S') (r : S' ⟶ S),
      IsProper r ∧ Surjective r ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra (S.residueField η) L),
        Module.Finite (S.residueField η) L ∧ Algebra.IsSeparable (S.residueField η) L ∧
        ∃ e : r.fiber η ≅ Spec (CommRingCat.of L),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)) =
            r.fiberToSpecResidueField η ∧
          ∃ (Y' : Scheme.{u}) (q : Y' ⟶ pullback f r),
            IsFinite q ∧
            IsIso (((Over.pullback (e.inv ≫ r.fiberι η)).map
              (Over.homMk q rfl :
                Over.mk (q ≫ pullback.snd f r) ⟶ Over.mk (pullback.snd f r))).left) ∧
            Flat (q ≫ pullback.snd f r) ∧
            LocallyOfFinitePresentation (q ≫ pullback.snd f r) ∧
            QuasiCompact (q ≫ pullback.snd f r) ∧
            QuasiSeparated (q ≫ pullback.snd f r) ∧
            GeometricallyReduced (q ≫ pullback.snd f r) := by
  sorry

end AlgebraicGeometry
