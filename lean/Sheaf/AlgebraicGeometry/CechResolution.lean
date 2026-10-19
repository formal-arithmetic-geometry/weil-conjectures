module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.CechSheafResolution
import Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic

/-!
# Čech resolution and derived direct image

Source: Weil conjectures blueprint, `lem-pc-cech-resolution`, node order 670
(blueprint: lem-pc-cech-resolution).

The Čech complex of sheaves `D` with `D^p = ∏_{y : Fin (p+1) → ι} j_{U_y,*}(F|_{U_y})` is
tied to Mathlib's `cechComplexFunctor`: its presheaf of sections `V ↦ D^p(V)` is the Čech
complex of the cover `U` with coefficients in the presheaf `W ↦ (V ↦ F(W ⨯ V))`, that is
`V ↦ Č(U ∩ V, F)`; the augmentation `F → D^0` is the restriction `F(V) → F(U_i ⨯ V)`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem derived_iso_of_acyclic_resolution
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (D : CochainComplex X.Modules ℕ)
    (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D) [QuasiIso ε]
    (hD : ∀ p, (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic (D.X p)) :
    Nonempty ((schemeDerivedDirectImage f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≅
      DerivedCategory.Q.obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (D.extend ComplexShape.embeddingUpNat))) := by
  let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    infer_instance
  let K := D.extend ComplexShape.embeddingUpNat
  let L : CochainComplex.Plus (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    ⟨K, 0, inferInstance⟩
  have hL : ∀ n, G.rightAcyclic (L.obj.X n) :=
    HomologicalComplex.prop_extend_X _ ComplexShape.embeddingUpNat hD
  have hunit := G.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hL
  let H := (HomotopyCategory.Plus.quotient (SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj L
  let eu : (DerivedCategory.Plus.ι (C := SheafOfModules.{u}
        (moduleRings S.toRingedSpace))).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj H)) ≅
      DerivedCategory.Qh.obj ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj K)) :=
    (DerivedCategory.Plus.ι (C := SheafOfModules.{u}
      (moduleRings S.toRingedSpace))).mapIso
        (asIso (G.rightDerivedFunctorPlusUnit.app H)).symm
  let e : G.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    G.rightDerivedFunctor.mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))).symm.app K) ≪≫
      (G.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Qh.obj H)).symm ≪≫
      eu ≪≫ (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings S.toRingedSpace))).app _
  have hε : QuasiIso (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff ε ComplexShape.embeddingUpNat).2 inferInstance
  let eF : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
        DerivedCategory.Q.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app F ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).symm ≪≫
      asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap ε
        ComplexShape.embeddingUpNat))
  exact ⟨G.rightDerivedFunctor.mapIso eF ≪≫ e⟩

/-- The finite affine Čech resolution is exact and computes the derived direct image.
Let `S = Spec A`, `f : X ⟶ S` separated and quasi-compact, `U` a finite affine open cover of
`X` and `F` a quasi-coherent `𝒪_X`-module. Then the Čech complex of sheaves `D` (terms
`∏_J j_{J,*}(F|_{U_J})`, sections over `V` the Čech complex of `U ∩ V` with coefficients in
`F`, augmented by the restrictions `ε : F → D^0`) is a resolution of `F` (`ε` is a
quasi-isomorphism, i.e. the augmented complex is exact), its terms are `f_*`-acyclic, and
`Rf_* F ≅ f_* D` in `D(𝒪_S)`.
Source: the blueprint node `lem-pc-cech-resolution`, proof paragraphs 1--4
(blueprint: lem-pc-cech-resolution).

Proof: exactness is local; on a cover member `U_i` the index `i` gives a contracting
homotopy of the augmented complex. The intersections `U_J` are affine (`S` affine, `f`
separated), so `j_J` and `f ∘ j_J` are affine morphisms and their higher direct images of
the quasi-coherent `F|_{U_J}` vanish; the Grothendieck spectral sequence for
`(j_{J,*}, f_*)` gives `R^q f_*(j_{J,*} F|_{U_J}) = 0` for `q > 0`, hence each finite product
term is `f_*`-acyclic. The finite acyclic-resolution criterion
(`lem-pc-derived-acyclic-resolution`) then identifies `Rf_* F` with `f_* D`. -/
theorem cech_resolution_derived_direct_image
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] [QuasiCompact f]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i : ι, IsAffineOpen (U i))
    (F : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))] :
    ∃ (D : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
      (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p),
      (∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1)) ∧
      (∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) ∧
      (∀ p : ℕ, Nonempty (D.X p ≅ ∏ᶜ fun y : Fin (p + 1) → ι =>
        (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj (F.restrict (⨅ l, U (y l)).ι))) ∧
      QuasiIso ε ∧
      (∀ p q : ℕ, 0 < q →
        IsZero ((schemeModuleHigherDirectImage f (q : ℤ)).obj (D.X p))) ∧
      Nonempty ((schemeDerivedDirectImage f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≅
        DerivedCategory.Q.obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (D.extend ComplexShape.embeddingUpNat))) := by
  obtain ⟨D, ε, e, hd, hε, hterms, hqi⟩ := exists_cech_sheaf_resolution U hU F
  have : QuasiIso ε := hqi
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : G.rightAcyclic.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  have hD : ∀ p, G.rightAcyclic (D.X p) := by
    intro p
    obtain ⟨ep⟩ := hterms p
    apply G.rightAcyclic.prop_of_iso ep.symm
    apply G.rightAcyclic.prop_product
    intro y
    exact affine_open_pushforward_rightAcyclic f (⨅ l, U (y l))
      (IsAffineOpen.iInf (fun l ↦ haffine (y l))) F
  refine ⟨D, ε, e, hd, hε, hterms, hqi, ?_, ?_⟩
  · intro p q hq
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    exact (hD p n).of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso G (D.X p) (n + 1))
  · exact derived_iso_of_acyclic_resolution f F D ε hD

end AlgebraicGeometry
