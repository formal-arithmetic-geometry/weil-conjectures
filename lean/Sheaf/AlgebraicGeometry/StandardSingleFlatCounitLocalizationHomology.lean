module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk
import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPair
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow
import all Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem flat_restrict_iso {R T : CommRingCat.{u}} (e : R ≅ T)
    (N : ModuleCat.{u} R) (hN : Module.Flat R N) :
    Module.Flat T ((ModuleCat.restrictScalars e.inv.hom).obj N) := by
  let : Algebra T R := e.inv.hom.toAlgebra
  let : Module.Flat T R := RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso e.inv)
  let : Module.Flat R N := hN
  let N' := (ModuleCat.restrictScalars e.inv.hom).obj N
  let : Module R N' := inferInstanceAs (Module R N)
  let : Module.Flat R N' := hN
  change Module.Flat T N'
  let : IsScalarTower T R ((ModuleCat.restrictScalars e.inv.hom).obj N) :=
    ⟨fun r s m ↦ by change (e.inv.hom r * s) • m = _; simp [mul_smul]⟩
  exact Module.Flat.trans T R _

set_option maxHeartbeats 800000 in
-- The ring and derived-category transports require additional elaboration heartbeats.
set_option linter.unusedVariables false in
/-- Homology identifications and counit compatibility for fixed stalk data.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
Proof: unpack Classical.choose_spec hpres into the upper bound, termwise flatness,
identifications e and t, and presentation equation for K. Take its termwise stalk at xS
and restrict scalars along the inverse open-stalk ring isomorphism. Exact additive stalks
preserve zero terms and the bound; flat stalks and transport along the ring isomorphism
give termwise flatness. Set P′ equal to this constructed P, with equality rfl. Choose a
universal left-derived extension-of-scalars pair for g.stalkMap a. On K-flat resolutions,
the ordinary tensor-pullback stalk isomorphism identifies scalar extension with the stalk
of pullback. Naturality and the pure-tensor formula identify the scalar-extension counit
with the stalk of the sheaf counit; localization descends this identity. Transport e and
t through these comparisons. Derived direct image commutes with restriction to full
inverse-image opens, and derived pullback commutes with open restriction. Their
unit-and-counit mate identities identify the restricted base-change map with the original
map. Transport the stalks from S and V to B and A along the open-stalk isomorphisms.
Exact stalks commute with homology, so applying degree-n homology to the transported
presentation equation supplies eL, eR and the displayed equality for every integer n,
using the same P and derived pair.
(blueprint: lem-pc-standard-single-flat-counit-localization-homology). -/
theorem standardSingleFlatCounit_localization_homology
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hSaff : IsAffine S.toScheme) (hVaff : IsAffine V.toScheme)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (hpres : StandardSingleFlatCounitPresentation (p ∣_ S)
      (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    let K := Classical.choose hpres
    let xS : S.toScheme := ⟨g a, hS⟩
    let P :=
      ((ModuleCat.restrictScalars (S.stalkIso xS).inv.hom).mapHomologicalComplex
        (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).mapHomologicalComplex
          (.up ℤ)).obj K)
    ∃ (P' : CochainComplex (ModuleCat.{u} R) ℤ), P' = P ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P'.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P'.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))),
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P'))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P'))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P')) ≫ eR.hom  := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let R := B.presheaf.stalk (g a)
  let T := A.presheaf.stalk a
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} T)
  let K := Classical.choose hpres
  let xS : S.toScheme := ⟨g a, hS⟩
  let xV : V.toScheme := ⟨a, hV⟩
  let P := ((ModuleCat.restrictScalars (S.stalkIso xS).inv.hom).mapHomologicalComplex
    (.up ℤ)).obj
    (((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).mapHomologicalComplex
      (.up ℤ)).obj K)
  obtain ⟨hbound, hflat, e, t, heq⟩ := Classical.choose_spec hpres
  have hPbound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) := by
    obtain ⟨b, hb⟩ := hbound
    refine ⟨b, fun i hi ↦ ?_⟩
    exact (ModuleCat.restrictScalars (S.stalkIso xS).inv.hom).map_isZero
      ((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).map_isZero (hb i hi))
  have hPflat : ∀ i : ℤ, Module.Flat R (P.X i) := by
    intro i
    exact flat_restrict_iso (S.stalkIso xS)
      ((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).obj (K.X i))
      (RingedSpace.flat_stalk_of_isFlat _ _ (hflat i) xS)
  obtain ⟨LF, ε, hLF⟩ :=
    standardSingleFlatCounit_localization_pair h_affine p M hM g a P hPbound hPflat
  refine ⟨P, rfl, hPbound, hPflat, LF, ε, hLF, ?_⟩
  intro n
  let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
    ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) n
  let j := g.resLE S V hVS
  obtain ⟨s, v, hv⟩ := standardSingle_open_stalk_arrow p M g a S V hV hVS n
  obtain ⟨l, r, hc⟩ := openFlatComplex_stalk_counit g a S V hS hV hVS K
    hbound hflat LF ε hLF n
  let e' := F.mapIso (H.mapIso ((derivedPullback j).mapIso e))
  let t' := F.mapIso (H.mapIso t)
  refine ⟨s ≪≫ e' ≪≫ l, r ≪≫ t' ≪≫ v, ?_⟩
  have heq' := congrArg (fun f ↦ F.map (H.map f)) heq
  have hc' : F.map (H.map ((SingleComplexBaseChange.counit j).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) =
      l.hom ≫ (DerivedCategory.homologyFunctor _ n).map
        (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ r.hom := hc
  calc
    _ = s.hom ≫ F.map (H.map
          (standardSingleBaseChangeMap (p ∣_ S) (M.restrict (p ⁻¹ᵁ S).ι) j)) ≫
        v.hom := hv
    _ = _ := by
      rw [heq']
      simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc, e', t']
      rw [hc']
      simp only [Category.assoc]
      rfl
end AlgebraicGeometry
