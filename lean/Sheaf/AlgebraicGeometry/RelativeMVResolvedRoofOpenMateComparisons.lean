/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import Sheaf.AlgebraicGeometry.RelativeMVResolvedOpenRoofComparison
import Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison

/-! # Mate comparisons for the concrete resolved row roof -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.defeqAttrib.useBackward true

private theorem component_roof_transport
    {C : Type*} [Category C] {X Y Z T : C}
    {p : X ⟶ Z} {q : Y ⟶ Z} [IsIso q] {η : Y ⟶ T} {a : X ⟶ T}
    (p' : X ⟶ Z) (q' : Y ⟶ Z) [IsIso q']
    (hp : p = p') (hq : q = q')
    (h : p' ≫ inv q' ≫ η = a) : p ≫ inv q ≫ η = a := by
  cases hp
  cases hq
  exact h

set_option maxHeartbeats 1000000 in
-- The two open-vertex types contain fixed complex and derived functor comparisons.
/-- The open and diagonal components of a normalized resolved row roof are the
specified local base-change mates. Source: Stacks Project, Tags 08FE, 08HY,
08HZ and 0D5T.
(blueprint: lem-pc-relative-mv-resolved-roof-open-mate-comparisons).
Proof: The middle-only mate comparison provides the two middle-vertex
isomorphisms and their equation. Apply the proved one-open roof comparison to
W=U intersect V. Its denominator is the third vertex of the fixed row denominator:
the image chain map has schemeMVImageComponent as its third component, and
inverse image preserves the intersection. Its numerator is the third vertex of
the numerator row map by the prescribed third-component equation for u0.
Rewrite these two component identities, including under the invertible denominator,
and combine the two one-open isomorphisms and equation with the middle data.
No exactness, cover, global comparison or row construction occurs. Empty,
repeated and full opens and zero phi follow the same component identities. -/
theorem relativeMV_resolved_roof_open_mate_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (u₀ : schemeMayerVietorisComplex X U V (schemeMVResolution X K) ⟶
      schemeMayerVietorisComplex X U V
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hu₂ : u₀.τ₂ = biprod.map
      (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
      (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r))
    (hu₃ : u₀.τ₃ =
      ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) :
    let I := schemeMVResolution X K
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let A := (schemeMayerVietorisComplex X U V I).map Ff
    let R := (schemeMayerVietorisComplex X U V L).map Ff
    let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
    let u : A ⟶ R := Ff.mapShortComplex.map u₀
    let v : B.map F ⟶ R := (D.mapNatIso c).hom ≫
      Ff.mapShortComplex.map (schemeMVImageChainMap g' U V J L s)
    ∀ (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₂
      letI := hv₃
    ∃ (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right),
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  (
    classical
    extract_lets (descend := false) I J L Ff Ff' A R B G F η adj b c D u v
    intro hv₂ hv₃
    haveI := hv₂
    haveI := hv₃
    obtain ⟨e₂, e₂', h₂⟩ := relativeMV_resolved_roof_middle_mate_comparison
      f f' g g' hpull K K' φ U V r s u₀ hr hs hu₂ hv₂
    have hvW : IsIso (DerivedCategory.Q.map
        (c.hom.app (schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ (U ⊓ V)) J) ≫
          Ff.map (schemeMVImageComponent g' (U ⊓ V) J L s))) := hv₃
    have hvW' := hvW
    dsimp only [c, I, J, L, Ff] at hvW'
    obtain ⟨e₃, e₃', h₃⟩ := relativeMV_resolved_open_roof_comparison
      f f' g g' hpull K K' φ (U ⊓ V) r s hr hs hvW'
    refine ⟨e₂, e₃, e₂', e₃', h₂, ?_⟩
    have hu : u.τ₃ = Ff.map
        (((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) := by
      change Ff.map u₀.τ₃ = _
      exact congrArg Ff.map hu₃
    have hv : v.τ₃ =
        c.hom.app (schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ (U ⊓ V)) J) ≫
          Ff.map (schemeMVImageComponent g' (U ⊓ V) J L s) := rfl
    let IW := schemeOpenModuleImageComplex X (U ⊓ V) I
    let JW := schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ (U ⊓ V)) J
    let LW := schemeOpenModuleImageComplex X (U ⊓ V) L
    let p : DerivedCategory.Q.obj (Ff.obj IW) ⟶ DerivedCategory.Q.obj (Ff.obj LW) :=
      DerivedCategory.Q.map u.τ₃
    let q : DerivedCategory.Q.obj (F.obj (Ff'.obj JW)) ⟶
        DerivedCategory.Q.obj (Ff.obj LW) := DerivedCategory.Q.map v.τ₃
    haveI : IsIso q := hv₃
    let pW : DerivedCategory.Q.obj (Ff.obj IW) ⟶ DerivedCategory.Q.obj (Ff.obj LW) :=
      DerivedCategory.Q.map (Ff.map
        (((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r))
    let qW : DerivedCategory.Q.obj (F.obj (Ff'.obj JW)) ⟶
        DerivedCategory.Q.obj (Ff.obj LW) := DerivedCategory.Q.map
      (c.hom.app JW ≫ Ff.map (schemeMVImageComponent g' (U ⊓ V) J L s))
    haveI : IsIso qW := hvW
    have hp : p = pW := congrArg DerivedCategory.Q.map hu
    have hq : q = qW := congrArg DerivedCategory.Q.map hv
    change p ≫ inv q ≫ η.app (Ff'.obj JW) =
      adj.homEquiv _ _ (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)
    apply component_roof_transport pW qW hp hq
    exact h₃
  )

end AlgebraicGeometry
