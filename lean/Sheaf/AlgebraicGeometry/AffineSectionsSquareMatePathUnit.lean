/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

/-! # Unit formula for the affine sections mate path

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-sections-square-mate-path-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The path through the square mate and the comparisons r,d, evaluated on the
unit for p_* followed by affine sections. This formula does not involve the derived
comparison c on the other path.
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T; perfect.tex, Tag 0AA7.
(blueprint: lem-pc-affine-sections-square-mate-path-unit).
Proof: transpose the fixed pullback composition comparisons under the pinned
composite adjunctions. Their left-derived factorization and the normalized
Hom-equivalence equations identify the resulting mate with the direct-image
composition comparison, compatibly with the pasted right-derived units.
Whisker this unit equation by affine sections. Substitute hb, hr and hd, and
move the direct-image and sections units past the underived comparisons by
naturality. Exact scalar restriction identifies its derived composite unit
with the levelwise restriction comparison. The resulting underived path has
components t^{-1}, the pushforward square comparison, v and z. Each acts as the
identity on sections by ht, hv and hz; their scalar actions agree by the
fibre-product condition. It therefore equals s, by hs and extensionality of
module maps. Deriving this equality gives the displayed localization of s
followed by the sections unit and the exact-restriction comparison. All of
these factorization equations hold on arbitrary homotopy-category objects;
no cancellation of a unit, and no K-injectivity assumption, is used here.
For zero complexes both sides vanish; identity squares reduce to unit coherence. -/
theorem affineSections_square_mate_path_unit
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let P₀ := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let Q₀ := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let P := schemeDerivedDirectImage (pullback.fst f g)
    let Q := schemeDerivedDirectImage (pullback.snd f g)
    let RF := schemeDerivedDirectImage f
    let RG := schemeDerivedDirectImage g
    let A₀ := affineGlobalSections (𝟙 (Spec R))
    let B₀ := affineGlobalSections (𝟙 (Spec B))
    let S₀ := affineGlobalSections f
    let T₀ := affineGlobalSections (pullback.snd f g)
    let A := affineDerivedGlobalSections (𝟙 (Spec R))
    let D := affineDerivedGlobalSections (𝟙 (Spec B))
    let S := affineDerivedGlobalSections f
    let T := affineDerivedGlobalSections (pullback.snd f g)
    let aA := affineGlobalSectionsDerivedIso (𝟙 (Spec R))
    let aB := affineGlobalSectionsDerivedIso (𝟙 (Spec B))
    let aS := affineGlobalSectionsDerivedIso f
    let aT := affineGlobalSectionsDerivedIso (pullback.snd f g)
    let ρ₀ := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    let aρ := affineBaseChangedSectionsDerivedIso f g
    ∀ (t : F₀ ⋙
        A₀ ≅ S₀)
    (b : RF ⋙
        A ≅ S)
    (ht : ∀ (M : SheafOfModules.{u} (moduleRings (X).toRingedSpace))
        (x : (S₀).obj M), (t.hom.app M) x = x)
    (hb : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (X).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (F₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((RF).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (S₀).rightDerivedFunctorUnit.app J ≫
        (aS).hom.app (DerivedCategory.Qh.obj J))
    (z : Q₀ ⋙
        B₀ ≅ T₀)
    (d : Q ⋙
        D ≅ T)
    (hz : ∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (T₀).obj M), (z.hom.app M) x = x)
    (hd : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (Q₀)
        (B₀)).app J ≫
        (aB).hom.app
          ((Q).obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
        ((z.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (T₀).rightDerivedFunctorUnit.app J ≫
        (aT).hom.app (DerivedCategory.Qh.obj J))
    (v : G₀ ⋙
        A₀ ≅
      B₀ ⋙
        ρ₀)
    (r : RG ⋙ A ≅
      D ⋙
        (ρ₀).mapDerivedCategory)
    (hv : ∀ (M : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (x : (B₀).obj M), (v.hom.app M) x = x)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (G₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((RG).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (B₀ ⋙
          ρ₀).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (B₀)
            (ρ₀) ≪≫
          Functor.isoWhiskerRight (aB)
            (ρ₀).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (s : P₀ ⋙
        S₀ ≅
      T₀ ⋙
        ρ₀)
    (hs : ∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (T₀).obj F),
      (s.hom.app F) x = x)
    (J : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (.up ℤ)),
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p : ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (i : Y ⟶ Z),
        derivedPullback i ⋙ derivedPullback h ≅ derivedPullback (h ≫ i) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h) (pullback.condition (f := f) (g := g)).symm) ≪≫
        (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    let F := DerivedCategory.Qh.obj J
    (Functor.rightDerivedFunctorCompUnit
        (P₀)
        (S₀)).app J ≫
      (aS).hom.app
        ((P).obj F) ≫
      b.inv.app ((P).obj F) ≫
      (A).map (δ.app F) ≫
      r.hom.app ((Q).obj F) ≫
      (ρ₀).mapDerivedCategory.map
        (d.hom.app F) =
    DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
      (T₀ ⋙
        ρ₀).rightDerivedFunctorUnit.app J ≫
      (aρ).hom.app F := by sorry

end AlgebraicGeometry
