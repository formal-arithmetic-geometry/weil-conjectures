/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel
import Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-! # Higher direct image stalks of an affine-line projection

Source: blueprint `thm-sc-affine-torsion-cd`, local calculation and compactification,
proof steps 4--10.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem isZero_pointPullback_of_algClosure_stalk
    {B : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ B)
    (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hz : IsZero ((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ s)).sheafFiber.obj
        F)) : IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj F) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  have : LocallySmall.{u + 1} (Spec (.of Ω)).Etale := locallySmall_max.{u + 1, u}
  have ht : ⋃ _ : PUnit.{u + 1}, Set.range t = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, default, Subsingleton.elim _ _⟩
  have hc := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of Ω)) (fun _ : PUnit.{u + 1} ↦ t) ht
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} s).obj F
  have hz' : IsZero ((pointSmallEtale t).sheafFiber.obj G) :=
    hz.of_iso ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} s t).app F)
  apply (IsZero.iff_id_eq_zero G).2
  apply (hc.jointlyFaithful AddCommGrpCat.{u + 1}).map_injective
  rintro ⟨_, ⟨i⟩⟩
  have hz'' : IsZero ((((pointSmallEtale t).ulift.{u + 1}).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G) :=
    hz'.of_iso (((pointSmallEtale t).uliftSheafFiberIso.{u + 1}
      AddCommGrpCat.{u + 1}).app G)
  let Φ := ((pointSmallEtale t).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1})
  calc
    Φ.map (𝟙 G) = 𝟙 (Φ.obj G) := Φ.map_id G
    _ = 0 := hz''.eq_of_src _ _
    _ = Φ.map 0 := (Φ.map_zero G G).symm

private theorem projectiveLine_infinity_isClosedImmersion (B : Scheme.{u}) :
    IsClosedImmersion (ProjectiveLine.infinity B) := by
  have : IsClosedImmersion
      (ProjectiveLine.infinity B ≫ AlgebraicGeometry.ProjectiveLine B ↘ B) := by
    rw [ProjectiveLine.infinity_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (AlgebraicGeometry.ProjectiveLine B ↘ B)

private theorem isZero_stalk_lowerStar_of_closedSection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (g : Y ⟶ Z) (hig : i ≫ g = 𝟙 Z)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : (Etale.lowerStar AddCommGrpCat.{u + 1} i).essImage A)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (hz : IsZero ((pointSmallEtale (s ≫ i)).sheafFiber.obj A)) :
    IsZero ((pointSmallEtale s).sheafFiber.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj A)) := by
  obtain ⟨N, ⟨e⟩⟩ := hA
  have eN := (asIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit.app
    N)).symm ≪≫ (Etale.upperStar AddCommGrpCat.{u + 1} i).mapIso e
  have eStalk := (pointSmallEtale s).sheafFiber.mapIso eN ≪≫
    (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} i s).app A
  have hzN := hz.of_iso eStalk
  have ePush := ((Etale.lowerStarComp AddCommGrpCat.{u + 1} i g (𝟙 Z) hig.symm) ≪≫
    Etale.lowerStarId AddCommGrpCat.{u + 1} Z).app N
  have eG := (Etale.lowerStar AddCommGrpCat.{u + 1} g).mapIso e
  exact hzN.of_iso ((pointSmallEtale s).sheafFiber.mapIso (eG.symm ≪≫ ePush))

private theorem torsionCd_affineLine (L : Type u) [Field L] [IsSepClosed L] :
    (AffineSpace PUnit.{u + 1} (Spec (.of L))).HasTorsionCohomologicalDimensionLE 1 := by
  let a : Spec (.of (MvPolynomial PUnit.{u + 1} L)) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L (MvPolynomial PUnit.{u + 1} L)))
  have : LocallyOfFiniteType a := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have : IsCurve a :=
    { krullDim_le_one := by
        change topologicalKrullDim (PrimeSpectrum (MvPolynomial PUnit.{u + 1} L)) ≤ 1
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp }
  have hb : HasTorsionCohomologicalDimensionLE
      (Spec (.of (MvPolynomial PUnit.{u + 1} L))) 1 :=
    (IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed a).2 inferInstance
  exact hb.of_isUniversalHomeomorphism (AffineSpace.SpecIso PUnit.{u + 1} (.of L)).inv

private theorem torsionCd_affineLine_pullback_of_field
    {X B R : Scheme.{u}} (e : X ≅ AffineSpace PUnit.{u + 1} B)
    (f : X ⟶ B) (he : e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f)
    (ρ : R ⟶ B) (L : Type u) [Field L] [IsSepClosed L] (eR : R ≅ Spec (.of L)) :
    (pullback f ρ).HasTorsionCohomologicalDimensionLE 1 := by
  have h := AffineSpace.isPullback_map (n := PUnit.{u + 1}) ρ
  have hp : IsPullback (AffineSpace.map PUnit.{u + 1} ρ ≫ e.inv)
      (AffineSpace PUnit.{u + 1} R ↘ R) f ρ := by
    apply h.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he, Iso.inv_hom_id_assoc]
    · simp
  let eA := (AffineSpace.functor.obj (Opposite.op PUnit.{u + 1})).mapIso eR
  exact (torsionCd_affineLine L).of_isUniversalHomeomorphism
    ((hp.isoPullback.symm ≪≫ eA).inv)

private theorem projectiveLine_polynomial_geometry
    (K : Type u) [Field K] (m : ℕ) :
    let B := Spec (.of (MvPolynomial (Fin m) K))
    let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))
    let Y := AlgebraicGeometry.ProjectiveLine B
    let g := Y ↘ B
    IsIntegral Y ∧ Smooth (g ≫ b) ∧ LocallyOfFiniteType (g ≫ b) ∧
      QuasiCompact (g ≫ b) ∧ topologicalKrullDim Y = ((m + 1 : ℕ) : WithBot ℕ∞) := by
  dsimp only
  let B := Spec (.of (MvPolynomial (Fin m) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))
  let Y := AlgebraicGeometry.ProjectiveLine B
  let g : Y ⟶ B := Y ↘ B
  have hb : Smooth b := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have hdB : topologicalKrullDim B = (m : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin m) K)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdb : SmoothOfRelativeDimension m b :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq b m).2 hdB
  have hdg : SmoothOfRelativeDimension 1 g := inferInstance
  have hg : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have hcomp : SmoothOfRelativeDimension (1 + m) (g ≫ b) := inferInstance
  have hsm : Smooth (g ≫ b) := SmoothOfRelativeDimension.smooth (1 + m) _
  have hlft : LocallyOfFiniteType (g ≫ b) := inferInstance
  have hqc : QuasiCompact (g ≫ b) := inferInstance
  have hgc : GeometricallyConnected g := MorphismProperty.of_isPullback
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) b) inferInstance
  have hconn : ConnectedSpace Y := GeometricallyConnected.connectedSpace g g.isOpenMap
  have hnoeth : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ b)
  have hreg : IsRegular Y := IsRegular.of_smooth (g ≫ b)
  have hint : IsIntegral Y := IsRegular.isIntegral Y
  refine ⟨hint, hsm, hlft, hqc, ?_⟩
  simpa only [Nat.add_comm 1 m] using
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (g ≫ b) (1 + m)

private theorem isTorsion_functor_obj
    {X Y : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [F.Additive]
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0) : (F.obj M).IsTorsion := by
  apply isTorsion_of_nsmul_id_eq_zero hN
  have hm := congrArg F.map hM
  rw [Functor.map_nsmul, Functor.map_zero] at hm
  rw [F.map_id] at hm
  exact hm

private theorem isZero_leray_of_row_column
    {X Y B T : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ B) (s : T ⟶ B)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (r : ℕ)
    (hLeray :
      (∀ p q : ℕ, p + q = r →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
            (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))) →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)))
    (hrow : IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived r).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} j).obj M)))
    (hmixed : ∀ p q : ℕ, 0 < p → 0 < q →
      IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))
    (hcolumn : IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived r).obj M)))) :
    IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)) := by
  apply hLeray
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = r := by omega
    subst q
    exact hcolumn.of_iso ((Etale.upperStar AddCommGrpCat.{u + 1} s).mapIso
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedZeroIsoSelf.app _))
  · by_cases hq : q = 0
    · subst q
      have hp' : p = r := by omega
      subst p
      exact ((Etale.upperStar AddCommGrpCat.{u + 1} s).map_isZero hrow).of_iso
        ((Etale.upperStar AddCommGrpCat.{u + 1} s).mapIso
          (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived r).mapIso
            ((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerivedZeroIsoSelf.app M)))
    · exact (Etale.upperStar AddCommGrpCat.{u + 1} s).map_isZero
        (hmixed p q (Nat.pos_of_ne_zero hp) (Nat.pos_of_ne_zero hq))

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The higher direct image of a bounded-torsion sheaf on affine space vanishes at
points whose residue transcendence degree plus the cohomological degree exceeds the
source dimension. The hypothesis `hCartier` is the bound on punctured smooth strict localizations;
the caller proves it using the coefficient-field model and dimension induction.
The hypotheses `hP1`, `hBoundary`, and `hStalk` supply, respectively, the projective-line
bound, mixed-degree boundary acyclicity, and the strict-local stalk comparison.
The hypothesis `hLeray` supplies diagonal vanishing after exact inverse image.
The hypothesis `hAffineLine` identifies the explicit polynomial projection with
the structural morphism of a relative affine line.
This statement concerns the projection and its stalks, rather than global cohomology.

Source: blueprint `thm-sc-affine-torsion-cd`, proof steps 4--10.
(blueprint: lem-sc-affine-line-projection-stalk-bound)

Proof: Put d = n + 2, B = A^(d-1)_K, Y = P^1_B, g : Y -> B, j : A^d_K -> Y,
and i : B -> Y the infinity section. The supplied `hAffineLine` identification
followed by the standard affine chart constructs j. The two polynomial charts
give dim Y = d and show Y is smooth and integral over K.
The Cartier boundary has equation h in the infinity chart. Its complement immersion
is quasi-compact (on the charts its inverse images are the whole chart and D(h))
and separated, so the strict-henselization stalk formula applies.

At a boundary point of residue transcendence degree a, use the punctured smooth
strict-local bound `hCartier`. The boundary equation h is nonzero in the strict-local
domain and belongs to its maximal ideal; also a < d. It gives cohomological dimension
at most d-a for Spec R[1/h]. The supplied stalk comparison `hStalk` therefore gives zero stalks
of R^q j_*M when q > d-a. Away from the boundary positive direct images of j vanish
because restricting the immersion gives the identity.

For q > 0, the caller uses the closed-support equivalence to write
R^q j_*M = i_*N_q. Closed-section acyclicity then gives R^p g_*R^q j_*M = 0
for p,q positive; this is the supplied `hBoundary` statement.
Additivity preserves the annihilator N
through all direct images and right derived functors. The supplied projective-line
bound `hP1`, applied to the torsion sheaf
j_*M,
gives R^p g_* j_*M = 0 for p > 2. The caller proves this hypothesis from the
projective-line geometric-stalk comparison and the curve bound, independently of the
affine cohomological dimension theorem.

For r>2, apply the supplied Leray diagonal-vanishing statement `hLeray` after
inverse image at the chosen point of B. A diagonal term with both coordinates
positive is zero by the boundary-section calculation. The term with q=0 is zero
by the projective-line bound because p=r>2. For p=0, q=r, closed support writes the higher
image as i_*N. The closed
immersion counit and the identity g i = id identify both its boundary stalk and the
base stalk of its direct image with the stalk of N. This proves the assertion for r>2,
including r>d, without needing to choose
an edge-map isomorphism.

For r=2 the inequality d < 2 + trdeg_K kappa(y) forces y to be the generic point of
the polynomial base B. Its strict localization is a separably closed field: its
regular local ring has dimension zero. The strict-henselization stalk formula for
the affine projection then identifies this stalk with H^2 of an affine line over
that separably closed field. The affine-curve bound makes this zero. This also handles
d=2. For a merely separably closed geometric field, test after extension to its
algebraic closure. This single geometric point covers the one-point base spectrum,
so its geometric fibre functor is conservative. The inverse-image/stalk comparison
therefore turns vanishing there into the stated zero inverse-image sheaf. Thus the assertion
holds for every geometric point specified here. - /
theorem affineLineProjection_stalk_bound
    (hP1 : ∀ (S : Scheme.{u})
      (F : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
        AddCommGrpCat.{u + 1}), F.IsTorsion → ∀ q : ℕ, 2 < q →
      IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1}
        (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj F))
    (hBoundary : ∀ {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
      (i : Z ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ Z),
      Set.range i.base = (Set.range j.base)ᶜ → i ≫ g = 𝟙 Z →
      ∀ (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (p q : ℕ),
      0 < p → 0 < q →
      IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))
    (hStalk : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion → ∀ q : ℕ,
      Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q) →
      IsZero ((pointSmallEtale s).sheafFiber.obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)))
    (hLeray : ∀ {X Y S T : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ S) (s : T ⟶ S)
      (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (r : ℕ),
      (∀ p q : ℕ, p + q = r →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
            (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))) →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)))
    (hAffineLine : ∀ (K : Type u) [CommRing K] (m : ℕ),
      let B := Spec (.of (MvPolynomial (Fin m) K))
      let f := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
        (Fin.castSucc : Fin m → Fin (m + 1))).toRingHom)
      ∃ e : Spec (.of (MvPolynomial (Fin (m + 1)) K)) ≅ AffineSpace PUnit.{u + 1} B,
        e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f)
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hCartier : ∀ (Y : Scheme.{u}) [IsIntegral Y]
        (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
        (a : ℕ), a < n + 2 → topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
          (y : Y), s (IsLocalRing.closedPoint Ω) = y →
        ∀ [Algebra K (Y.residueField y)],
          Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
            Y.fromSpecResidueField y ≫ f →
        ∀ [Algebra (Y.residueField y) Ω],
          Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
            Y.fromSpecResidueField y = s →
          Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u}) →
        ∀ [Algebra K (strictHenselizationRing s)],
          Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
            strictHenselizationStructuralMap s ≫ f →
        ∀ (h : strictHenselizationRing s), h ∈ IsLocalRing.maximalIdeal _ → h ≠ 0 →
          (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE (n + 2 - a))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (hq : 2 ≤ q) :
      let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
          Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
        Spec.map (CommRingCat.ofHom (MvPolynomial.rename
          (Fin.castSucc : Fin (n + 1) → Fin (n + 2))).toRingHom)
      let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))),
        ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) +
            residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
          IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
            (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)) := by
  classical
  dsimp only
  intro Ω _ _ s hs
  let X := Spec (.of (MvPolynomial (Fin (n + 2)) K))
  let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
  let f : X ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
    (Fin.castSucc : Fin (n + 1) → Fin (n + 2))).toRingHom)
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  let t : Spec (.of (AlgebraicClosure Ω)) ⟶ B :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ s
  have ht : t (IsLocalRing.closedPoint (AlgebraicClosure Ω)) =
      s (IsLocalRing.closedPoint Ω) := by
    change s ((Spec.map (CommRingCat.ofHom
      (algebraMap Ω (AlgebraicClosure Ω))))
      (IsLocalRing.closedPoint (AlgebraicClosure Ω))) = _
    congr 1
    exact Subsingleton.elim _ _
  have hMt : M.IsTorsion := isTorsion_of_nsmul_id_eq_zero hN hM
  apply isZero_pointPullback_of_algClosure_stalk s
  change IsZero ((pointSmallEtale t).sheafFiber.obj
    (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M))
  obtain ⟨e, he⟩ := hAffineLine K (n + 1)
  change e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f at he
  by_cases hq2 : q = 2
  · subst q
    have hs' : ((n + 1 : ℕ) : Cardinal.{u}) ≤ residueFieldTrdeg b
        (t (IsLocalRing.closedPoint (AlgebraicClosure Ω))) := by
      rw [ht]
      have hs'' : (2 : Cardinal.{u}) + (n : Cardinal.{u}) <
          (2 : Cardinal.{u}) + residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat, add_comm] using hs
      have hn := (Cardinal.add_lt_add_iff_of_left_lt_aleph0
        (Cardinal.natCast_lt_aleph0 (n := 2))).mp hs''
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Cardinal.natCast_add_one_le_iff).2 hn
    obtain ⟨L, hL, hLc, ⟨eR⟩⟩ := polynomial_generic_strictLocalization_field
      K (n + 1) t hs'
    let := hL
    let := hLc
    have hcd := torsionCd_affineLine_pullback_of_field e f he
      (strictHenselizationStructuralMap t) L eR
    apply hStalk f t M hMt 2
    exact hcd _ (Etale.isTorsion_upperStar _ hMt) 2 (by omega)
  · have hq3 : 2 < q := by omega
    let Y := AlgebraicGeometry.ProjectiveLine B
    let g : Y ⟶ B := Y ↘ B
    let j : X ⟶ Y := e.hom ≫ ProjectiveLine.affineChart B
    let i : B ⟶ Y := ProjectiveLine.infinity B
    have hi : IsClosedImmersion i := projectiveLine_infinity_isClosedImmersion B
    have hj : IsOpenImmersion j := inferInstance
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      have hr : j.opensRange = (ProjectiveLine.affineChart B).opensRange := by
        exact Hom.opensRange_comp_of_isIso _ _
      change Set.range i = (j.opensRange : Set Y)ᶜ
      rw [hr]
      exact ProjectiveLine.range_infinity B
    have hig : i ≫ g = 𝟙 B := ProjectiveLine.infinity_over
    have hfg : j ≫ g = f := by
      change (e.hom ≫ ProjectiveLine.affineChart B) ≫ g = f
      rw [Category.assoc, ProjectiveLine.affineChart_over]
      exact he
    obtain ⟨hint, hsm, hlft, hqc, hd⟩ := projectiveLine_polynomial_geometry K (n + 1)
    change IsIntegral Y at hint
    change Smooth (g ≫ b) at hsm
    change LocallyOfFiniteType (g ≫ b) at hlft
    change QuasiCompact (g ≫ b) at hqc
    change topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞) at hd
    let v := t ≫ i
    let y := v (IsLocalRing.closedPoint (AlgebraicClosure Ω))
    let : Algebra K (Y.residueField y) := ((g ≫ b).residueFieldAlgebraMap y).toAlgebra
    obtain ⟨a, ha, htr, htry, h, hhm, hh0, ⟨eh⟩⟩ :=
      affineLine_infinity_strictLocal_model K n e t
    have hqa : n + 2 - a < q := by
      have hnat : n + 2 < q + a := by
        have hs' : ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) + a := by
          rw [← htr, ht]
          exact hs
        exact_mod_cast hs'
      omega
    let χ := (SpecToEquivOfField (AlgebraicClosure Ω) Y v).2
    let : Algebra (Y.residueField y) (AlgebraicClosure Ω) := χ.hom.toAlgebra
    have hΩ : Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure Ω))) ≫
        Y.fromSpecResidueField y = v :=
      (SpecToEquivOfField (AlgebraicClosure Ω) Y).symm_apply_apply v
    let α := Spec.preimage (strictHenselizationStructuralMap v ≫ (g ≫ b))
    let : Algebra K (strictHenselizationRing v) := α.hom.toAlgebra
    have hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing v))) =
        strictHenselizationStructuralMap v ≫ (g ≫ b) := Spec.map_preimage _
    have hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
        Y.fromSpecResidueField y ≫ (g ≫ b) := by
      change Spec.map (CommRingCat.ofHom ((g ≫ b).residueFieldAlgebraMap y)) = _
      unfold Hom.residueFieldAlgebraMap
      rw [CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp, Category.assoc,
        Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
        Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    have hcd := hCartier Y (g ≫ b) a ha hd (AlgebraicClosure Ω) v y rfl
      hκ hΩ htry hK h hhm hh0
    have hcd' := hcd.of_isUniversalHomeomorphism eh.inv
    have hboundary := hStalk j v M hMt q
      (hcd' _ (Etale.isTorsion_upperStar _ hMt) q hqa)
    have hsupport : (Etale.lowerStar AddCommGrpCat.{u + 1} i).essImage
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M) := by
      apply Etale.mem_essImage_lowerStar_of_isZero_upperStar i hij
      have e₁ := Functor.rightDerivedCompObjIso
        (Etale.lowerStar AddCommGrpCat.{u + 1} j)
        (Etale.upperStar AddCommGrpCat.{u + 1} j) q M
      have e₂ := Functor.rightDerivedObjIsoOfIso
        (asIso (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit)
        q M
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show 0 < q by omega).ne'
      exact (Functor.isZero_rightDerived_obj_of_exact (𝟭 _) M r).of_iso
        (e₁.symm ≪≫ e₂)
    have hcolumnStalk := isZero_stalk_lowerStar_of_closedSection i g hig _ hsupport t
      hboundary
    have hcolumn := isZero_pointPullback_of_algClosure_stalk s _ hcolumnStalk
    have htotal := isZero_leray_of_row_column j g s M q (hLeray j g s M q)
      (hP1 B _ (isTorsion_functor_obj (Etale.lowerStar AddCommGrpCat.{u + 1} j)
        M N hN hM) q hq3)
      (fun p r hp hr ↦ hBoundary j i g hij hig M p r hp hr) hcolumn
    rw [hfg] at htotal
    let c := Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
    have : LocallySmall.{u + 1} (Spec (.of Ω)).Etale := locallySmall_max.{u + 1, u}
    have : ((pointSmallEtale c).sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
      (pointSmallEtale c).sheafFiber_additive
    have hz := ((pointSmallEtale c).sheafFiber
      (A := AddCommGrpCat.{u + 1})).map_isZero htotal
    exact hz.of_iso ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} s c).app
      (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)).symm
-/

end AlgebraicGeometry.Scheme
