/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PerfectOpenSupportDetection
import WeilConjectures.AlgebraicGeometry.AdjointTensorAnnihilatorTransport
import Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.PseudoCoherentSupportAnnihilation
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization

/-!
# Support preservation by the right adjoint of proper flat direct image

Source: Stacks Project, duality.tex, Lemma 48.4.4, case (1), Tag 0E4G, using
perfect.tex, Tags 0A1H and 0A9C(i) for the unbounded strengthening in the node
(blueprint: lem-sc-proper-flat-right-adjoint-open-support).
-/

@[expose] public section

universe uT wXT wYT

open CategoryTheory

namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Comparing the two derived tensor models during annihilator elaboration is expensive.
/-- The right adjoint of proper, flat, finitely presented derived direct image preserves
support on the complement of a quasi-compact open. `F` is the restriction of `Rf_*` to
`D_QCoh`, identified with the recorded ambient direct image by the natural isomorphism
`hF`. Support means vanishing of every cohomology stalk on the open.
Source: Stacks Project, duality.tex, Tag 0E4G, Lemma 48.4.4, case (1); the unbounded
version uses perfect.tex, Tags 0A1H and 0A9C(i).
(blueprint: lem-sc-proper-flat-right-adjoint-open-support).

Proof:
1. Put T = Y minus V and U = f⁻¹(V). If a(Q)|U is nonzero, perfect generation
   (lem-pc-derived-qcoh-perfect-generation) detects it by a nonzero map P_U → a(Q)|U.
   The lifting lemma lem-sc-perfect-support-map-lift, with closed subset X, lifts it
   to β : P → a(Q), with P perfect and β|U nonzero, since P_U is a compatible summand.
2. The adjunction identifies β with a map Rf_*P → Q.
3. Properness, flatness and finite presentation, and
   lem-pc-proper-support-perfect-direct-image with G = O_X[0], make Rf_*P perfect.
   Case (i) of lem-sc-pseudo-coherent-support-annihilation supplies a perfect I and
   I → O_Y, an isomorphism over V, killing the composite I ⊗ᴸ Rf_*P → Rf_*P → Q.
4. The projection formula lem-pc-projection-formula identifies its source with
   Rf_*(Lf^*I ⊗ᴸ P). Adjunction makes Lf^*I ⊗ᴸ P → P → a(Q) zero.
5. Over U the map Lf^*I → O_X is invertible, contradicting β|U being nonzero.
   Thus every cohomology stalk of a(Q) vanishes on U. -/
theorem proper_flat_rightAdjoint_open_support
    {X Y : Scheme.{uT}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wXT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wYT} (SheafOfModules.{uT} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (Q : schemeDerivedQCohCategory Y)
    (hQ : ∀ (n : ℤ) (y : Y), y ∈ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uT} (moduleRings Y.toRingedSpace)) n).obj Q.obj).val.presheaf y))) :
    ∀ (n : ℤ) (x : X), x ∈ f ⁻¹ᵁ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uT} (moduleRings X.toRingedSpace)) n).obj
          (a.obj Q).obj).val.presheaf x)) := by
  classical
  let : ∀ W : X.Opens,
      HasDerivedCategory.{wXT} (SheafOfModules.{uT}
        ((moduleRings X.toRingedSpace).over W)) :=
    (nonempty_derivedOpenLocalization X).some
  let : ∀ W : Y.Opens,
      HasDerivedCategory.{wYT} (SheafOfModules.{uT}
        ((moduleRings Y.toRingedSpace).over W)) :=
    (nonempty_derivedOpenLocalization Y).some
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace (V : Set Y) := isCompact_iff_compactSpace.mp hV
  apply perfect_open_support_detection X (f ⁻¹ᵁ V) (f.isCompact_preimage hV) (a.obj Q)
  intro P hP β
  have hpush := properFlat_derivedDirectImage_perfect f P.obj hP
  have hFP : Scheme.IsPerfect Y (F.obj P).obj := by
    intro y
    obtain ⟨W, hy, K, hK, ⟨e⟩⟩ := hpush y
    exact ⟨W, hy, K, hK,
      ⟨(SheafOfModules.overFunctor (moduleRings Y.toRingedSpace)
        W).mapDerivedCategory.mapIso (hF.app P) ≪≫ e⟩⟩
  obtain ⟨I, i, hI, hi, hkill⟩ := exists_perfect_annihilator Y V
    (F.obj P) Q ((adj.homEquiv P Q).symm β) (Or.inl hFP) hQ
  obtain ⟨R, j, hj, hzero⟩ :=
    adjoint_tensor_annihilator_transport f F hF a adj V P Q β I hI i hi hkill
  let L := (SheafOfModules.overFunctor (moduleRings X.toRingedSpace)
    (f ⁻¹ᵁ V)).mapDerivedCategory
  have : IsIso (L.map j) := hj
  apply (cancel_epi (L.map j)).mp
  change L.map j ≫ L.map β.hom = L.map j ≫ 0
  rw [← L.map_comp, hzero, L.map_zero, CategoryTheory.Limits.comp_zero]

end AlgebraicGeometry
