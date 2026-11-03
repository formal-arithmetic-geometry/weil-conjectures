/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescentKummer
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

/-!
# Relative affine-line low-degree calculation

Source: Stacks Project, Etale Cohomology, Tags 0EYU, 03Q9 and 03PL; the
"Reduction to a geometric fibre" and "Degrees 0 and 1" paragraphs of the blueprint
proof `sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/det-prop-a1-kummer`
(blueprint: lem-pur-relative-line-low-degree-general).
-/


namespace AlgebraicGeometry.Etale

private theorem splitMono_unit_of_section
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsSplitMono ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M) := by
  let af := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let as := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s
  let e : upperStar (ModuleCat.{u + 1} Λ) f ⋙
      upperStar (ModuleCat.{u + 1} Λ) s ≅ 𝟭 _ :=
    (upperStarComp _ s f (𝟙 Y) hs.symm).symm ≪≫ upperStarId _ Y
  have : (upperStar (ModuleCat.{u + 1} Λ) f ⋙
      upperStar (ModuleCat.{u + 1} Λ) s).Full := Functor.Full.of_iso e.symm
  have : (upperStar (ModuleCat.{u + 1} Λ) f ⋙
      upperStar (ModuleCat.{u + 1} Λ) s).Faithful := Functor.Faithful.of_iso e.symm
  refine ⟨⟨(lowerStar (ModuleCat.{u + 1} Λ) f).map (as.unit.app _) ≫
    inv ((af.comp as).unit.app M), ?_⟩⟩
  exact (congrArg (fun z => z ≫ inv ((af.comp as).unit.app M))
    (Adjunction.comp_unit_app af as M).symm).trans (IsIso.hom_inv_id _)

private theorem isIso_unit_of_homology_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : ∀ x : Y, Finite ↑(((Y.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj M))
    (hu : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M) := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  let R := rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  let c := (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).app M
  let e := H.mapIso (R.mapIso c) ≪≫
    (Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
      (lowerStar (ModuleCat.{u + 1} Λ) f)).app
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj M)
  have := splitMono_unit_of_section Λ f s hs M
  exact isIso_of_isSplitMono_of_iso Λ _
    (e.symm ≪≫ (asIso (H.map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))).symm ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M) hM

/-- Relative affine-line and punctured-line low-degree calculation.

Source: Stacks Project, Etale Cohomology, Tags 0EYU, 03Q9 and 03PL; the
"Reduction to a geometric fibre" and "Degrees 0 and 1" paragraphs of the blueprint
proof `det-prop-a1-kummer` (blueprint: lem-pur-relative-line-low-degree-general).

The coefficient sheaf is the finite Tate line `μ_(ℓ^N) ⊗ Λ`, represented by
`finiteEtaleTateSheaf` in degree one.  The open immersion `j` is required to
have the complement of the zero section as its range, so it is the relative
multiplicative group.  The two displayed isomorphisms are the actual
adjunction units; the last equality says that restriction is the identity
when those units are used to identify both direct images with the base sheaf.

Proof:
1. Compare scalar extension of the roots-of-unity sections over `ZMod m` with scalar
   extension of their underlying abelian groups, using uniqueness of left adjoints.
   Kummer-level independence then identifies the finite line with `tateTwistSheaf`.
2. Transport the arbitrary-field affine-line derived unit isomorphism and the
   punctured-line degree-zero unit isomorphism to this concrete coefficient.
3. Each ordinary unit is a split monomorphism because its morphism has a section.
   Degree-zero homology of derived direct image identifies its target with its source.
   The stalks of the coefficient are finite, so a split monomorphism between these
   isomorphic sheaves is an isomorphism. This gives the actual specified units.
4. The pullback/single comparison and bounded-below/unbounded comparison transport
   the source library's positive-degree affine-line vanishing to the displayed H1p.
5. The upper-star/lower-star composition coherence identifies the composite of the
   first unit and restriction with the second unit. Cancel that isomorphism.
-/
theorem relativeLineLowDegreeGeneral
    (k : Type u) [Field k] (ell : ℕ) (hell : ell.Prime)
    (hellk : IsUnit (ell : k)) (N : ℕ) (hN : 1 ≤ N)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (G : Scheme.{u})
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y)
    [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    let m : ℕ := ell ^ N
    let p : AffineSpace (ULift.{u} (Fin 1)) Y ⟶ Y :=
      (AffineSpace.over (ULift.{u} (Fin 1)) Y).hom
    let π : G ⟶ Y := j ≫ p
    let LY : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      Scheme.finiteEtaleTateSheaf Λ m Y hΛ 1
    let LX : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
        (ModuleCat.{u + 1} Λ) :=
      (Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj LY
    let LU : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj LX
    let restriction :
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj LX ⟶
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj LU :=
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) j).unit.app LX) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) j p π
          (by rfl)).hom.app LU
    let H1p :=
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (1 : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj LX))
    ∃ e₀ : LY ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj LX,
      ∃ eπ : LY ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj LU,
        e₀.hom = (Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) p).unit.app LY ∧
        eπ.hom = (Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) p).unit.app LY ≫ restriction ∧
        IsZero H1p ∧
        e₀.hom ≫ restriction ≫ eπ.inv = 𝟙 LY := by
  have hmpos : 0 < ell ^ N := by
    have _ := hN
    exact pow_pos hell.pos _
  have hmfield : IsUnit ((ell ^ N : ℕ) : Γ(Spec (.of k), ⊤)) := by
    simpa only [Nat.cast_pow, map_pow, map_natCast] using
      (hellk.pow N).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have : NeZero (ringChar Λ) := ⟨CharP.ringChar_ne_zero_of_finite Λ⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := ⟨ell ^ N, hmpos, hΛ, hmfield⟩
  have : HasInvertibleExponent Λ Y := .of_hom aY
  let p := (AffineSpace.over (ULift.{u} (Fin 1)) Y).hom
  let π := j ≫ p
  let M := Scheme.finiteEtaleTateSheaf Λ (ell ^ N) Y hΛ 1
  have hmy : IsUnit ((ell ^ N : ℕ) : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hmfield.map aY.appTop.hom
  let eM : M ≅ tateTwistSheaf Λ Y 1 :=
    finiteEtaleLineAbIso Y (ell ^ N) Λ hΛ ≪≫
      extendScalarsRootsOfUnityIsoTateTwistSheaf Λ (ell ^ N) hΛ hmy
  let eT : tateObject Λ Y 1 ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M :=
    tateTwistObjectIsoSingleFunctor Λ Y 1 ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso eM.symm
  have hM : ∀ x : Y, Finite ↑(((Y.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj M) := by
    intro x
    exact Finite.of_equiv _
      (((Y.uliftPointSmallEtale x).sheafFiber.mapIso eM) ≪≫
        (GrothendieckTopology.Point.uliftSheafFiberIso _ _).app _ ≪≫
        sheafFiberTateTwistSheafIso Λ Y 1 (Y.algClosurePoint x)).toLinearEquiv.toEquiv.symm
  have hpderived : IsIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) p).unit.app (tateObject Λ Y 1)) :=
    isIso_unit_tateObject_affineLine_of_field Λ aY
  have hpzero : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit
        (_root_.DerivedCategory.homologyFunctor _ 0)) eT).1
      (show IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
          (tateObject Λ Y 1))) from inferInstance)
  have hp := isIso_unit_of_homology_zero Λ p (AffineSpace.zeroSection _ Y)
    (AffineSpace.zeroSection_comp_over _ Y) M hM hpzero
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : LocallyOfFiniteType p := inferInstanceAs
    (LocallyOfFiniteType (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) Y) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact j := by infer_instance
  have : HasInvertibleExponent Λ G := .of_hom π
  have hπderived := isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_field Λ aY j hj
  have hπzero : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit
        (_root_.DerivedCategory.homologyFunctor _ 0)) eT).1 hπderived
  have hπ := isIso_unit_of_homology_zero Λ π (complementOneSection j hj)
    (by
      change complementOneSection j hj ≫ (j ≫ p) = 𝟙 Y
      rw [← Category.assoc, complementOneSection_comp]
      exact AffineSpace.oneSection_comp_over _ Y) M hM hπzero
  let e₀ := asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M)
  let eπ := asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app M) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) π).mapIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) j p).app M)
  have heπ : eπ.hom =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) p).obj M)) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) j p).hom.app _) := by
    exact upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) j p M
  dsimp only
  refine ⟨e₀, eπ, rfl, heπ, ?_, ?_⟩
  · have : HasInvertibleExponent Λ (AffineSpace (ULift.{u} (Fin 1)) Y) := .of_hom p
    let LX := (upperStar (ModuleCat.{u + 1} Λ) p).obj M
    let eX : (_root_.DerivedCategory.singleFunctor _ 0).obj LX ≅
        tateObject Λ (AffineSpace (ULift.{u} (Fin 1)) Y) 1 :=
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) p).app M).symm ≪≫
        (L((p)^*[ModuleCat.{u + 1} Λ])).mapIso eT.symm ≪≫
          leftDerivedUpperStarTateObjectIso p 1
    let H := _root_.DerivedCategory.homologyFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 1
    exact (isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_field
      Λ Y aY 1 (by norm_num)).of_iso
        (H.mapIso ((Functor.rightDerivedFunctorPlusCompatibility
          (lowerStar (ModuleCat.{u + 1} Λ) p)).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj LX)) ≪≫
          H.mapIso ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).mapIso eX))
  · exact (congrArg (fun z => z ≫ eπ.inv) heπ.symm).trans eπ.hom_inv_id

end AlgebraicGeometry.Etale
