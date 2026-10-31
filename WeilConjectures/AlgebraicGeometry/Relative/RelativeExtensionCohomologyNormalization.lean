/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Relative torsor extensions and normalized supported cohomology

Source: Stacks Project, Tags 03AJ, 06XR, 06XV and 0A45, relative refinement;
blueprint lem-pur-divisor-class, first sentence and forget-support paragraph
(blueprint: lem-pur-relative-extension-cohomology-normalization).

The comparison is uniquely specified on every resolution cocycle by evaluation at one
and the inclusion into the signed cone with zero open coordinate. The relative torsor
class is the negative of the existing raw lifting-cocycle equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

private local instance (priority := 3000) additiveSelfForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := ⟨𝟭 _, rfl⟩

private theorem additiveSelfForget_additive :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).Additive

attribute [local instance] additiveSelfForget_additive

private theorem additiveSelfForget_homology :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).PreservesHomology

attribute [local instance] additiveSelfForget_additive additiveSelfForget_homology


private local instance (priority := 3000) integralWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

private local instance (priority := 3000) integralLocallyBijective (T : Scheme.{u}) :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

private theorem framedQuotient_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (e : S.X₃ ≅ T.X₂) (h : T.X₁ ⟶ S.X₂) (hh : h ≫ S.g ≫ e.hom = T.f) :
    let a := S.f ≫ cokernel.π h
    let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g)
      (by calc
        h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
          simp only [Category.assoc]
        _ = 0 := by rw [hh, T.zero])
    ∃ hz : a ≫ b = 0, (ShortComplex.mk a b hz).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have hzcomp : h ≫ (S.g ≫ e.hom ≫ T.g) = 0 := by
    calc
      h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
        simp only [Category.assoc]
      _ = 0 := by rw [hh, T.zero]
  let a := S.f ≫ cokernel.π h
  let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g) hzcomp
  have hb : cokernel.π h ≫ b = S.g ≫ e.hom ≫ T.g := cokernel.π_desc _ _ _
  have hab : a ≫ b = 0 := by
    dsimp only [a]
    rw [Category.assoc, hb, ← Category.assoc, S.zero, zero_comp]
  have : Mono h := mono_of_mono_fac hh
  have hhc : (ShortComplex.mk h (cokernel.π h) (cokernel.condition h)).ShortExact :=
    { exact := ShortComplex.exact_cokernel h }
  have ha : Mono a := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    let k := kernel.ι a
    have hk : (k ≫ S.f) ≫ cokernel.π h = 0 := by
      rw [Category.assoc]
      exact kernel.condition a
    let r := hhc.fIsKernel.lift (KernelFork.ofι (k ≫ S.f) hk)
    have hr : r ≫ h = k ≫ S.f := hhc.fIsKernel.fac _ WalkingParallelPair.zero
    have hrt : r ≫ T.f = 0 := by
      calc
        r ≫ T.f = (r ≫ h) ≫ S.g ≫ e.hom := by rw [← hh]; simp only [Category.assoc]
        _ = 0 := by rw [hr, Category.assoc, reassoc_of% S.zero, zero_comp, comp_zero]
    have hrzero : r = 0 := (cancel_mono T.f).1 (by simpa using hrt)
    have hka : k ≫ S.f = 0 := by rw [← hr, hrzero, zero_comp]
    exact (cancel_mono S.f).1 (by simpa using hka)
  have hbepi : Epi b := epi_of_epi_fac hb
  have hbCoker : IsColimit (CokernelCofork.ofπ b hab) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro M f hf
    have hSf : S.f ≫ (cokernel.π h ≫ f) = 0 := by
      rw [← Category.assoc]
      exact hf
    let q := hS.gIsCokernel.desc (CokernelCofork.ofπ (cokernel.π h ≫ f) hSf)
    have hq : S.g ≫ q = cokernel.π h ≫ f := hS.gIsCokernel.fac _ WalkingParallelPair.one
    have htq : T.f ≫ (e.inv ≫ q) = 0 := by
      calc
        T.f ≫ (e.inv ≫ q) = h ≫ (S.g ≫ q) := by
          rw [← hh]
          simp only [Category.assoc, e.hom_inv_id_assoc]
        _ = 0 := by rw [hq, ← Category.assoc, cokernel.condition, zero_comp]
    let r := hT.gIsCokernel.desc (CokernelCofork.ofπ (e.inv ≫ q) htq)
    have hr : T.g ≫ r = e.inv ≫ q := hT.gIsCokernel.fac _ WalkingParallelPair.one
    refine ⟨r, ?_⟩
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, hb, Category.assoc, Category.assoc, hr,
      ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp, hq]
  exact ⟨hab, { exact := ShortComplex.exact_of_g_is_cokernel _ hbCoker }⟩


attribute [local irreducible] relativeFiberMap relativeTorsorEquiv

/-- The relative extension characterization, including its equivariant framed lift.
Source: Stacks Tag 03AJ, relative refinement using Tag 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def RelativeExtensionRepresents {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) : Prop :=
  ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      @id (E.obj.obj V) (f.app V (P.1.vadd V g t)) =
        @id (E.obj.obj V) (f.app V t) + a.hom.app V g) ∧
    (∀ (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V),
      b.hom.app V (f.app V t) = (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0 ∧ β = hE.extClass

/-- Existence and uniqueness of the framed supported extension class.
Source: Stacks Tags 03AJ and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: the integral open-closed sequence and its sections adjunction meet the
hypotheses of relative_extension_existsUnique. Apply that theorem to P and its
specified section. The quotient construction kills that section, and uniqueness
of the extension class gives exactly the displayed characterization. -/
theorem relativeExtension_existsUnique {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    ∃! β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1, RelativeExtensionRepresents i P β := by
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  exact Sheaf.Torsor.relative_extension_existsUnique T P.1
    (Scheme.Etale.mk i.openComplement.ι) P.2 t (supportedIntegralUnit i)
    ht hT η hη hηt

/-- The class determined uniquely by the relative extension characterization.
Source: Stacks Tags 03AJ and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtension {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G 1 :=
  Classical.choose (relativeExtension_existsUnique i P)

/-- Cocycle normalization of the integral supported-Hom comparison in every degree.
The first equation evaluates precomposition with p at one; the second says that the
open cone coordinate is zero. Thus these equations specify the kernel inclusion,
not an arbitrary isomorphism. The shift coordinate is valid also in degree zero.
Source: Stacks Tags 06XR and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
structure RelativeExtensionComparisonNormalization {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q) : Prop where
  onCocycle : ∀ (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶
      I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
      I.cocomplex).cycles (q : ℤ)),
    (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex).f q
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) =
      (HomologicalComplex.extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex) ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv
          (k.hom.app (op (Scheme.Etale.mk (𝟙 T)))
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) →
    (((CochainComplex.mappingCone (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.sndX
        (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)
        ((q : ℤ) + -1))
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) = 0 →
    e q (I.extMk k (q + 1) rfl hk) =
      (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).homologyπ q z



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem relativeExtension_morphism {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' Q' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (φ : G ⟶ G') (E' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a' : G' ⟶ E') (b' : E' ⟶ Q') (hab' : a' ≫ b' = 0)
    (r : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶ Q')
    (f' : P.1.sheaf.obj ⟶ E'.obj ⋙ forget AddCommGrpCat.{u + 1})
    (hf'a : ∀ V g t, f'.app V (P.1.vadd V g t) =
      (show E'.obj.obj V from f'.app V t) + (φ ≫ a').hom.app V g)
    (hf'b : ∀ V t, b'.hom.app V (f'.app V t) =
      (supportedIntegralUnit i ≫ r).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
    (hf'τ : (show E'.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)) from
      f'.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0) :
    ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact),
      relativeExtension i P = hE.extClass ∧
        ∃ α : E ⟶ E', a ≫ α = φ ≫ a' ∧ α ≫ b' = b ≫ r := by
  classical
  let U := Scheme.Etale.mk i.openComplement.ι
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  obtain ⟨E⟩ : Nonempty (Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1) :=
    Sheaf.Torsor.nonempty_extensionPresentation T P.1
  let S := ShortComplex.mk E.inclusion E.projection E.inclusion_projection
  have hS : S.ShortExact := Sheaf.Torsor.extension_presentation_shortExact T E
  let h := (η E.middle).symm (E.generator (op U) P.2)
  have hp : h ≫ E.projection = t := by
    apply (η (supportedIntegralConstant T)).injective
    rw [hη, AddEquiv.apply_symm_apply, hηt]
    exact E.projection_generator _ _
  obtain ⟨hab, hE⟩ := framedQuotient_shortExact S
    (ShortComplex.mk t (supportedIntegralUnit i) ht) hS hT
    (by exact CategoryTheory.Iso.refl (supportedIntegralConstant T)) h (by
      change h ≫ E.projection ≫ 𝟙 _ = t
      simpa using hp)
  let a := E.inclusion ≫ cokernel.π h
  let b := cokernel.desc h (E.projection ≫ supportedIntegralUnit i)
    (by rw [← Category.assoc, hp]; exact ht)
  change (ShortComplex.mk a b hab).ShortExact at hE
  let f : P.1.sheaf.obj ⟶ (cokernel h).obj ⋙ forget AddCommGrpCat.{u + 1} :=
    { app V := TypeCat.ofHom fun z ↦ (cokernel.π h).hom.app V (E.generator V z)
      naturality V V' k := by
        ext z
        change (cokernel.π h).hom.app V' (E.generator V' (P.1.sheaf.obj.map k z)) =
          (cokernel h).obj.map k ((cokernel.π h).hom.app V (E.generator V z))
        rw [← E.generator_natural]
        exact ConcreteCategory.congr_hom ((cokernel.π h).hom.naturality k) _ }
  have hfa V g z : f.app V (P.1.vadd V g z) =
      (show (cokernel h).obj.obj V from f.app V z) + a.hom.app V g := by
    change (cokernel.π h).hom.app V (E.generator V (P.1.vadd V g z)) = _
    rw [E.generator_vadd, map_add]
    rfl
  have hfb V z : b.hom.app V (f.app V z) = (supportedIntegralUnit i).hom.app V
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩) := by
    change ((cokernel.π h ≫ b).hom.app V) (E.generator V z) = _
    rw [cokernel.π_desc]
    change (supportedIntegralUnit i).hom.app V
      (E.projection.hom.app V (E.generator V z)) = _
    rw [E.projection_generator]
  have hfτ : (show (cokernel h).obj.obj (op U) from f.app (op U) P.2) = 0 := by
    change (cokernel.π h).hom.app (op U) (E.generator (op U) P.2) = 0
    have hh := hη (cokernel.π h) h
    have he : (η E.middle) h = E.generator (op U) P.2 := AddEquiv.apply_symm_apply _ _
    rw [cokernel.condition, map_zero, he] at hh
    exact hh.symm
  have hβ : relativeExtension i P = hE.extClass := by
    exact ((Classical.choose_spec (relativeExtension_existsUnique i P)).2 _
      ⟨_, a, b, hab, hE, f, hfa, hfb, hfτ, rfl⟩).symm
  obtain ⟨α, ⟨hαa, hαf⟩, _⟩ := E.universal E' (φ ≫ a')
    (fun V z ↦ f'.app V z)
    (fun V V' k z ↦ (ConcreteCategory.congr_hom (f'.naturality k) z).symm) hf'a
  have hαb : α ≫ b' = E.projection ≫ supportedIntegralUnit i ≫ r := by
    obtain ⟨l, hl, huniq⟩ := E.universal Q' 0
      (fun V _ ↦ (supportedIntegralUnit i ≫ r).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
      (by
        intro V V' k z
        rw [← ConcreteCategory.comp_apply, ← (supportedIntegralUnit i ≫ r).hom.naturality,
          ConcreteCategory.comp_apply]
        congr 1
        exact (ConcreteCategory.congr_hom
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality k)
          ⟨1⟩).symm)
      (by intro V g z; change _ = _ + 0; exact (add_zero _).symm)
    apply (huniq _ ⟨by rw [← Category.assoc, hαa, Category.assoc, hab', comp_zero], ?_⟩).trans
      (huniq _ ⟨by rw [← Category.assoc, E.inclusion_projection, zero_comp], ?_⟩).symm
    · intro V z
      change b'.hom.app V (α.hom.app V (E.generator V z)) = _
      rw [hαf, hf'b]
    · intro V z
      change (supportedIntegralUnit i ≫ r).hom.app V
        (E.projection.hom.app V (E.generator V z)) = _
      rw [E.projection_generator]
  have hhα : h ≫ α = 0 := by
    apply (η E').injective
    rw [hη, map_zero]
    change α.hom.app (op U) ((η E.middle) ((η E.middle).symm _)) = 0
    rw [AddEquiv.apply_symm_apply, hαf]
    exact hf'τ
  let α' := cokernel.desc h α hhα
  have hα'a : a ≫ α' = φ ≫ a' := by
    rw [Category.assoc, cokernel.π_desc]
    exact hαa
  have hα'b : α' ≫ b' = b ≫ r := by
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, cokernel.π_desc, ← Category.assoc, cokernel.π_desc]
    exact hαb
  exact ⟨_, a, b, hab, hE, hβ, α', hα'a, hα'b⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem relativeExtension_map {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' Q' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (φ : G ⟶ G') (E' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a' : G' ⟶ E') (b' : E' ⟶ Q') (hab' : a' ≫ b' = 0)
    (hE' : (ShortComplex.mk a' b' hab').ShortExact)
    (r : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶ Q')
    (f' : P.1.sheaf.obj ⟶ E'.obj ⋙ forget AddCommGrpCat.{u + 1})
    (hf'a : ∀ V g t, f'.app V (P.1.vadd V g t) =
      (show E'.obj.obj V from f'.app V t) + (φ ≫ a').hom.app V g)
    (hf'b : ∀ V t, b'.hom.app V (f'.app V t) =
      (supportedIntegralUnit i ≫ r).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
    (hf'τ : (show E'.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)) from
      f'.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0) :
    (relativeExtension i P).comp (Ext.mk₀ φ) (add_zero 1) =
      (Ext.mk₀ r).comp hE'.extClass (zero_add 1) := by
  obtain ⟨E, a, b, hab, hE, hβ, α, hαa, hαb⟩ :=
    relativeExtension_morphism i P φ E' a' b' hab' r f' hf'a hf'b hf'τ
  have hn := hE.extClass_naturality hE'
    (ShortComplex.homMk φ α r hαa.symm hαb)
  change hE.extClass.comp (Ext.mk₀ φ) (add_zero 1) =
    (Ext.mk₀ r).comp hE'.extClass (zero_add 1) at hn
  rw [← hβ] at hn
  exact hn

set_option backward.isDefEq.respectTransparency false in
private def integerSectionEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (supportedIntegralConstant T ⟶ F) ≃+
      F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

set_option backward.isDefEq.respectTransparency false in
private lemma integerSectionEquiv_eval (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : supportedIntegralConstant T ⟶ F) :
    integerSectionEquiv T F a =
      a.hom.app (op (Scheme.Etale.mk (𝟙 T))) (supportedIntegralOne T) := by
  change ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homEquiv _ F a) ⟨1⟩ = _
  rw [Adjunction.homEquiv_unit]
  rfl

private lemma integerSectionEquiv_restrict (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : supportedIntegralConstant T ⟶ F) (U : T.Etaleᵒᵖ) :
    a.hom.app U ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) =
    F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
      (integerSectionEquiv T F a) := by
  rw [integerSectionEquiv_eval]
  have h := ConcreteCategory.congr_hom (a.hom.naturality
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op)
      (supportedIntegralOne T)
  simp only [ConcreteCategory.comp_apply] at h
  have hn := ConcreteCategory.congr_hom ((toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op) ⟨1⟩
  have hn' : (supportedIntegralConstant T).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
        (supportedIntegralOne T) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩ :=
    hn.symm
  rw [hn'] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralSupportedHomIso {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] :
    let j := (MorphismProperty.Over.mkIdTerminal @Etale T).from
      (Scheme.Etale.mk i.openComplement.ι)
    ∃ e : preadditiveCoyoneda.obj (op ((lowerStar AddCommGrpCat.{u + 1} i).obj
        (supportedIntegralConstant Z))) ≅
          Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} j,
      ∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
        (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶ F),
        kernel.ι (F.obj.map j.op) (e.hom.app F k) =
          integerSectionEquiv T F (supportedIntegralUnit i ≫ k) := by
  intro j
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  have hp : Epi (supportedIntegralUnit i) := hT.epi_g
  have hzero (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : supportedIntegralConstant T ⟶ F) :
      F.obj.map j.op (integerSectionEquiv T F a) = η F (t ≫ a) := by
    rw [hη, hηt]
    exact (integerSectionEquiv_restrict T F a _).symm
  let α : preadditiveCoyoneda.obj (op ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z))) ⟶ etaleSectionFunctor (Scheme.Etale.mk (𝟙 T)) :=
    { app F := AddCommGrpCat.ofHom
        { toFun k := integerSectionEquiv T F (supportedIntegralUnit i ≫ k)
          map_zero' := by simp
          map_add' k l := by
            change integerSectionEquiv T F (supportedIntegralUnit i ≫ (k + l)) = _
            rw [Preadditive.comp_add, map_add] }
      naturality F F' f := by
        ext k
        simp only [integerSectionEquiv_eval]
        rfl }
  have hα (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      α.app F ≫ F.obj.map j.op = 0 := by
    ext k
    change F.obj.map j.op (integerSectionEquiv T F (supportedIntegralUnit i ≫ k)) = 0
    rw [hzero, ← Category.assoc]
    change t ≫ supportedIntegralUnit i = 0 at ht
    rw [ht, zero_comp]
    exact (η F).map_zero
  let β : preadditiveCoyoneda.obj (op ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z))) ⟶
        Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} j :=
    { app F := kernel.lift _ (α.app F) (hα F)
      naturality F F' f := by
        apply (cancel_mono (kernel.ι (F'.obj.map j.op))).1
        simp only [Sheaf.supportedSectionsFunctor, Category.assoc, kernel.lift_ι,
          kernel.lift_ι_assoc]
        exact α.naturality f }
  have hβ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective (β.app F) := by
    have hi : Function.Injective (kernel.ι (F.obj.map j.op)) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    have he (k) : kernel.ι (F.obj.map j.op) (β.app F k) =
        integerSectionEquiv T F (supportedIntegralUnit i ≫ k) :=
      ConcreteCategory.congr_hom (kernel.lift_ι _ _ _) k
    constructor
    · intro k l hkl
      apply (cancel_epi (supportedIntegralUnit i)).1
      apply (integerSectionEquiv T F).injective
      rw [← he, ← he, hkl]
    · intro x
      let a := (integerSectionEquiv T F).symm (kernel.ι (F.obj.map j.op) x)
      have ha : t ≫ a = 0 := by
        apply (η F).injective
        rw [← hzero, AddEquiv.apply_symm_apply, map_zero]
        exact ConcreteCategory.congr_hom (kernel.condition (F.obj.map j.op)) x
      let k := hT.gIsCokernel.desc (CokernelCofork.ofπ a ha)
      have hk : supportedIntegralUnit i ≫ k = a :=
        hT.gIsCokernel.fac _ WalkingParallelPair.one
      exact ⟨k, hi ((he k).trans
        ((congrArg (integerSectionEquiv T F) hk).trans
          ((integerSectionEquiv T F).apply_symm_apply _)))⟩
  have : IsIso β := by
    have : ∀ F, IsIso (β.app F) := fun F ↦
      (ConcreteCategory.isIso_iff_bijective _).mpr (hβ F)
    exact NatIso.isIso_of_isIso_app β
  refine Exists.intro (asIso β) ?_
  intro F k
  change kernel.ι (F.obj.map j.op) (β.app F k) = _
  exact ConcreteCategory.congr_hom (kernel.lift_ι (F.obj.map j.op) (α.app F) (hα F)) k


set_option backward.isDefEq.respectTransparency false in
private lemma cone_projection_f {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (p : ℤ) :
    (RelativeCone.projection r).f p =
      ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) := by
  simp [RelativeCone.projection, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.shiftFunctorAdd_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.mappingCone.fst,
    CochainComplex.HomComplex.Cochain.rightShift_v]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cone_element_ext {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (p : ℤ) (x y : ((CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧).X p)
    (h₁ : (RelativeCone.projection r).f p x = (RelativeCone.projection r).f p y)
    (h₂ : (((CochainComplex.mappingCone r).shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom ≫ homotopyCofiber.sndX r (p - 1)) x =
      (((CochainComplex.mappingCone r).shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom ≫ homotopyCofiber.sndX r (p - 1)) y) : x = y := by
  let a := (CochainComplex.mappingCone r).shiftFunctorObjXIso
    (-1) p (p - 1) (by omega)
  let b := homotopyCofiber.XIsoBiprod r (p - 1) p
    (by change p - 1 + 1 = p; omega)
  let e := a ≪≫ b ≪≫ AddCommGrpCat.biprodIsoProd (A.X p) (B.X (p - 1))
  apply e.addCommGroupIsoToAddEquiv.injective
  apply Prod.ext
  · change (e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x =
      (e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) y
    dsimp only [e, Iso.trans_hom]
    rw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [cone_projection_f] at h₁
    exact h₁
  · have hb : b.hom ≫ biprod.snd = homotopyCofiber.sndX r (p - 1) := by
      apply homotopyCofiber.ext_from_X r p (p - 1) (by change p - 1 + 1 = p; omega)
        <;> simp [b]
    change (e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x =
      (e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) y
    dsimp only [e, Iso.trans_hom]
    rw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hb]
    exact h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized comparison exists and is unique, in all nonnegative degrees.
Source: Stacks Tags 06XR and 0A45, integral supported-Hom comparison
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: Hom from i_*Z_Z into each injective term identifies by precomposition with
p and evaluation at one with the kernel of restriction to the complementary open.
Its inclusion into the shifted cone is a quasi-isomorphism, as in the supported
relative-cone theorem. Compute Ext by I and take homology of that inclusion to
obtain the additive equivalences. The cocycle roof identifies I.extMk with this
resolution computation, so the displayed normalization holds. Every Ext class
has such a cocycle representative and its kernel inclusion is a cycle in the
cone. Consequently the normalization determines the equivalences uniquely. -/
theorem relativeExtensionComparison_existsUnique {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) :
    ∃! e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q,
      RelativeExtensionComparisonNormalization i G I e := by
  classical
  let U := Scheme.Etale.mk i.openComplement.ι
  let j := (MorphismProperty.Over.mkIdTerminal @Etale T).from U
  let H := Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} j
  obtain ⟨η, hη⟩ := integralSupportedHomIso i
  obtain ⟨x, hx⟩ := exists_ext_rightDerived_cocycle_comparison _ H η
  obtain ⟨E, _, _, _⟩ := relativeConeSupportComparison T i G I
  obtain ⟨R⟩ : Nonempty (RelativeCone.Realization T.smallEtaleTopology j I) :=
    ⟨E.realization j (by change IsOpenImmersion i.openComplement.ι; infer_instance) I⟩
  let K := (H.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := K.extend ComplexShape.embeddingUpNat
  let F := relativeSectionComplex T U I.cocomplex
  let A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  obtain ⟨m, hm, hmq⟩ : ∃ m : L ⟶ F,
      m = R.kernelIso.hom ≫ R.κ ∧ QuasiIso m := by
    have : QuasiIso R.κ := R.κ_quasiIso
    exact ⟨R.kernelIso.hom ≫ R.κ, rfl, inferInstance⟩
  have : QuasiIso m := hmq
  obtain ⟨e, he⟩ : ∃ e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T U I q,
      ∀ q : ℕ, e q =
        (((x q).symm.app G ≪≫ RelativeCone.computation T.smallEtaleTopology H I q) ≪≫
          asIso (homologyMap m (q : ℤ))).addCommGroupIsoToAddEquiv :=
    ⟨fun q ↦
      (((x q).symm.app G ≪≫ RelativeCone.computation T.smallEtaleTopology H I q) ≪≫
        asIso (homologyMap m (q : ℤ))).addCommGroupIsoToAddEquiv, fun _ ↦ rfl⟩
  let fst (q : ℕ) := (relativeForgetComplex T U I.cocomplex).f (q : ℤ)
  let snd (q : ℕ) :=
    ((CochainComplex.mappingCone (relativeSectionRestriction T U I.cocomplex)).shiftFunctorObjXIso
      (-1) (q : ℤ) ((q : ℤ) - 1) (by omega)).hom ≫
        homotopyCofiber.sndX (relativeSectionRestriction T U I.cocomplex) ((q : ℤ) - 1)
  have hm₁ (q : ℕ) : m.f q ≫ fst q =
      (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        kernel.ι ((I.cocomplex.X q).obj.map j.op) ≫
          (A.extendXIso ComplexShape.embeddingUpNat rfl).inv := by
    rw [hm]
    have hh := congrArg (fun t ↦ R.kernelIso.hom.f (q : ℤ) ≫ t) (R.κ_components q).2
    have hh' : (R.kernelIso.hom ≫ R.κ).f q ≫ fst q =
        R.kernelIso.hom.f q ≫ (kernel.ι
          (RelativeCone.restrictionComplex T.smallEtaleTopology j I.cocomplex)).f q := by
      change R.kernelIso.hom.f q ≫ R.κ.f q ≫ (RelativeCone.projection _).f q = _
      rw [cone_projection_f]
      simpa only [Category.assoc] using hh
    exact hh'.trans (R.kernel_components q)
  have hm₂ (q : ℕ) : m.f q ≫ snd q = 0 := by
    rw [hm]
    have hh := congrArg (fun t ↦ R.kernelIso.hom.f (q : ℤ) ≫ t) (R.κ_components q).1
    change R.kernelIso.hom.f q ≫ R.κ.f q ≫
      (((CochainComplex.mappingCone
        (RelativeCone.restrictionComplex T.smallEtaleTopology j I.cocomplex)).shiftFunctorObjXIso
          (-1) (q : ℤ) ((q : ℤ) - 1) (by omega)).hom ≫
        homotopyCofiber.sndX
          (RelativeCone.restrictionComplex T.smallEtaleTopology j I.cocomplex) ((q : ℤ) - 1)) = 0
    exact hh.trans (comp_zero)
  have hrep (q : ℕ)
      (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶
        I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0) :
      ∃ z : F.cycles (q : ℤ),
        fst q (F.iCycles q z) =
          (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
            (k.hom.app (op (Scheme.Etale.mk (𝟙 T)))
              ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
                (supportedIntegralOne T))) ∧
        snd q (F.iCycles q z) = 0 ∧
        e q (I.extMk k (q + 1) rfl hk) = F.homologyπ q z := by
    have hz : K.d q (q + 1) (η.hom.app (I.cocomplex.X q) k) = 0 := by
      have hn := ConcreteCategory.congr_hom (η.hom.naturality (I.cocomplex.d q (q + 1))) k
      change η.hom.app _ (k ≫ I.cocomplex.d q (q + 1)) = _ at hn
      simp only [ConcreteCategory.comp_apply] at hn
      rw [hk, map_zero] at hn
      exact hn.symm
    let c : K.cycles q := K.cyclesMk (η.hom.app (I.cocomplex.X q) k) (q + 1) (by simp) hz
    have hc : K.iCycles q c = η.hom.app (I.cocomplex.X q) k := K.i_cyclesMk _ _ _ _
    let w : L.cycles (q : ℤ) := (K.extendCyclesIso ComplexShape.embeddingUpNat rfl).inv c
    have hw : L.iCycles q w = (K.extendXIso ComplexShape.embeddingUpNat rfl).inv
        (η.hom.app (I.cocomplex.X q) k) := by
      have h := ConcreteCategory.congr_hom
        (K.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat (j := q) rfl) c
      simp only [ConcreteCategory.comp_apply, hc] at h
      exact h
    obtain ⟨z, hzi⟩ : ∃ z : F.cycles (q : ℤ),
        F.iCycles q z = m.f q (L.iCycles q w) :=
      ⟨cyclesMap m (q : ℤ) w, ConcreteCategory.congr_hom (cyclesMap_i m (q : ℤ)) w⟩
    refine Exists.intro z (And.intro ?_ (And.intro ?_ ?_))
    · rw [hzi, ← ConcreteCategory.comp_apply, hm₁]
      change (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
        (kernel.ι ((I.cocomplex.X q).obj.map j.op)
          ((K.extendXIso ComplexShape.embeddingUpNat rfl).hom (L.iCycles q w))) = _
      rw [hw, Iso.inv_hom_id_apply, hη, integerSectionEquiv_eval]
      rfl
    · rw [hzi]
      exact ConcreteCategory.congr_hom (hm₂ q) (L.iCycles q w)
    · rw [he q]
      change homologyMap m (q : ℤ)
        ((K.extendHomologyIso ComplexShape.embeddingUpNat rfl).inv
          ((I.isoRightDerivedObj H q).hom
            ((x q).inv.app G (I.extMk k (q + 1) rfl hk)))) = _
      rw [hx G I q k hk c hc]
      have hp := ConcreteCategory.congr_hom
        (K.homologyπ_extendHomologyIso_inv ComplexShape.embeddingUpNat (j := q) rfl) c
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hp
      rw [hp]
      have hn := ConcreteCategory.congr_hom (homologyπ_naturality m (q : ℤ)) w
      simp only [ConcreteCategory.comp_apply] at hn
      have hzmap : cyclesMap m (q : ℤ) w = z := by
        apply (AddCommGrpCat.mono_iff_injective (F.iCycles (q : ℤ))).mp inferInstance
        exact (ConcreteCategory.congr_hom (cyclesMap_i m (q : ℤ)) w).trans hzi.symm
      exact hn.trans (congrArg (F.homologyπ q) hzmap)
  refine ExistsUnique.intro e ?_ ?_
  · constructor
    intro q k hk z h₁ h₂
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := hrep q k hk
    have he : z = w := by
      apply (AddCommGrpCat.mono_iff_injective (F.iCycles (q : ℤ))).mp inferInstance
      apply cone_element_ext (relativeSectionRestriction T U I.cocomplex) (q : ℤ)
      · exact h₁.trans hw₁.symm
      · exact h₂.trans hw₂.symm
    exact hw₃.trans (congrArg (F.homologyπ q) he.symm)
  · intro e' he'
    funext q
    apply AddEquiv.ext
    intro α
    obtain ⟨k, hk, rfl⟩ := I.extMk_surjective α (q + 1) rfl
    obtain ⟨z, hz₁, hz₂, hz₃⟩ := hrep q k hk
    exact (he'.onCocycle q k hk z hz₁ hz₂).trans hz₃.symm


/-- The supported-Hom comparison determined by the kernel inclusion and evaluation at one.
Source: Stacks Tags 06XR and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionComparison {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (q : ℕ) : Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q :=
  Classical.choose (relativeExtensionComparison_existsUnique i G I) q

set_option backward.isDefEq.respectTransparency false in
private lemma coneSecondCoordinate (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (n : ℕ) :
    relativeSnd T U I n =
      homotopyCofiber.sndX (relativeSectionRestriction T U I) ((n : ℤ) + 1 + -1) ≫
      (HomologicalComplex.extendXIso _ _ (by simp :
        ComplexShape.embeddingUpNat.f n = (n : ℤ) + 1 + -1)).hom := by
  unfold relativeSnd relativeDegreeIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_snd]
  rw [← Category.assoc]
  congr 1
  have hs : ∀ (i j : ℤ) (h : i + 1 = j),
      (homotopyCofiber.XIsoBiprod (relativeSectionRestriction T U I) i j h).hom ≫
        biprod.snd = homotopyCofiber.sndX (relativeSectionRestriction T U I) i := by
    intro i j h
    subst j
    apply homotopyCofiber.ext_from_X _ (i + 1) i rfl <;> simp
  exact hs _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/- The first resolution row computes extMk of a lifted cocycle as minus the extension class. -/
private theorem extMk_of_extension_lift
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {G E Q : C} (I : InjectiveResolution G) (a : G ⟶ E) (b : E ⟶ Q)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (wI : I.ι.f 0 ≫ I.cocomplex.toCycles 0 1 = 0)
    (hI : (ShortComplex.mk (I.ι.f 0) (I.cocomplex.toCycles 0 1) wI).ShortExact)
    (h : E ⟶ I.cocomplex.X 0) (k : Q ⟶ I.cocomplex.X 1)
    (ha : a ≫ h = I.ι.f 0) (hb : b ≫ k = h ≫ I.cocomplex.d 0 1)
    (hk : k ≫ I.cocomplex.d 1 2 = 0) :
    I.extMk k 2 rfl hk = -hE.extClass := by
  have : Epi b := hE.epi_g
  obtain ⟨k', hki⟩ : ∃ k' : Q ⟶ I.cocomplex.cycles 1,
      k' ≫ I.cocomplex.iCycles 1 = k :=
    ⟨I.cocomplex.liftCycles k 2 (by simp) hk, I.cocomplex.liftCycles_i _ _ _ _⟩
  have hb' : b ≫ k' = h ≫ I.cocomplex.toCycles 0 1 := by
    apply (cancel_mono (I.cocomplex.iCycles 1)).mp
    rw [Category.assoc, hki, Category.assoc, I.cocomplex.toCycles_i, hb]
  have hn := hE.extClass_naturality hI
    (ShortComplex.homMk (𝟙 G) h k'
      (by change (𝟙 G) ≫ I.ι.f 0 = a ≫ h; exact (Category.id_comp _).trans ha.symm)
      (by change h ≫ I.cocomplex.toCycles 0 1 = b ≫ k'; exact hb'.symm))
  change hE.extClass.comp (Ext.mk₀ (𝟙 G)) (add_zero 1) =
    (Ext.mk₀ k').comp hI.extClass (zero_add 1) at hn
  rw [Ext.comp_mk₀_id] at hn
  have he := InjectiveResolution.mk₀_comp_extMk I
    (I.cocomplex.iCycles 1) 2 rfl (by simp) k'
  have hfirst : I.extMk (I.cocomplex.iCycles 1) 2 rfl (by simp) = -hI.extClass :=
    InjectiveResolution.extMk_firstCycles I wI hI
  have he' := congrArg (fun β ↦ (Ext.mk₀ k').comp β (zero_add 1)) hfirst
  have hh : (Ext.mk₀ k').comp (I.extMk (I.cocomplex.iCycles 1) 2 rfl (by simp))
      (zero_add 1) = -hE.extClass :=
    he'.trans ((Ext.comp_neg _ _ (zero_add 1)).trans (congrArg Neg.neg hn.symm))
  have heq : (Ext.mk₀ k').comp
      (I.extMk (I.cocomplex.iCycles 1) 2 rfl (by simp)) (zero_add 1) =
      I.extMk k 2 rfl hk := by
    simpa only [hki] using he
  exact heq.symm.trans hh

/-- The relative extension realizes the Ext-normalized relative torsor class.
Source: Stacks Tags 03AJ, 06XR, 06XV and 0A45, relative refinement
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: represent beta by 0 -> G -> E -> i_*Z_Z -> 0 and its equivariant torsor
map killing the frame. Extend the resolution augmentation across G -> E to h.
Factor dh through the quotient to a closed cocycle k. The first resolution row
and naturality of extension classes give I.extMk(k) = -beta: the cycles inclusion
is the negative of the first-row extension class. Under the comparison k maps
to the signed pair (a,0), where a = (kp)(1). The map h composed with the framed
lift is an equivariant map from P to the lifting torsor of a, killing the frame,
so the raw relative class of P is the frame cycle with coordinates (a,0). The
normalization of the comparison sends I.extMk(k) to that class. Hence the
comparison of beta is minus the raw class, the Ext-normalized relative class. -/
theorem relative_extension_cohomology_normalization {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    relativeExtensionComparison i G I 1 (relativeExtension i P) =
      -relativeTorsorEquiv T (Scheme.Etale.mk i.openComplement.ι) I (Quotient.mk _ P) := by
  classical
  let U := Scheme.Etale.mk i.openComplement.ι
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  obtain ⟨E, a, b, hab, hE, f, hfa, hfb, hfτ, hβ⟩ :=
    (Classical.choose_spec (relativeExtension_existsUnique i P)).1
  change relativeExtension i P = hE.extClass at hβ
  let : Mono a := hE.mono_f
  let : Epi b := hE.epi_g
  let : Injective (I.cocomplex.X 0) := I.injective 0
  obtain ⟨h, ha⟩ : ∃ h : E ⟶ I.cocomplex.X 0, a ≫ h = I.ι.f 0 :=
    ⟨Injective.factorThru (I.ι.f 0) a, Injective.comp_factorThru _ _⟩
  have hhd : a ≫ (h ≫ I.cocomplex.d 0 1) = 0 := by
    rw [← Category.assoc, ha]
    exact I.ι_f_zero_comp_complex_d
  obtain ⟨k, hb⟩ : ∃ k : (lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z) ⟶ I.cocomplex.X 1,
      b ≫ k = h ≫ I.cocomplex.d 0 1 :=
    ⟨hE.gIsCokernel.desc (CokernelCofork.ofπ (h ≫ I.cocomplex.d 0 1) hhd),
      hE.gIsCokernel.fac _ WalkingParallelPair.one⟩
  have hk : k ≫ I.cocomplex.d 1 2 = 0 := by
    apply (cancel_epi b).mp
    rw [← Category.assoc, hb, Category.assoc, I.cocomplex.d_comp_d, comp_zero, comp_zero]
  have hk' : ∃ k' : (lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z) ⟶ I.cocomplex.cycles 1,
      k' ≫ I.cocomplex.iCycles 1 = k :=
    ⟨I.cocomplex.liftCycles k 2 (by simp) hk, I.cocomplex.liftCycles_i _ _ _ _⟩
  obtain ⟨k', hki⟩ := hk'
  have hb' : b ≫ k' = h ≫ I.cocomplex.toCycles 0 1 := by
    apply (cancel_mono (I.cocomplex.iCycles 1)).mp
    rw [Category.assoc, hki, Category.assoc, I.cocomplex.toCycles_i, hb]
  have hsign : I.extMk k 2 rfl hk = -relativeExtension i P :=
    (extMk_of_extension_lift I a b hab hE _
      (resolutionLiftSequence_shortExact T I) h k ha hb hk).trans
        (congrArg Neg.neg hβ.symm)
  let s := k'.hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T))) (supportedIntegralOne T))
  let Q := Sheaf.Torsor.lifts (G := G) hT (resolutionLiftSequence_shortExact T I) s
  have hs (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V) :
      (I.cocomplex.toCycles 0 1).hom.app V (h.hom.app V (f.app V t)) =
        (I.cocomplex.cycles 1).obj.map (hT.from V.unop).op s := by
    have hn := ConcreteCategory.congr_hom (k'.hom.naturality (hT.from V.unop).op)
      ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (supportedIntegralOne T))
    have hp := integerSectionEquiv_restrict T (I.cocomplex.cycles 1)
      (supportedIntegralUnit i ≫ k') V
    rw [integerSectionEquiv_eval] at hp
    have he := congrArg (fun l ↦ l.hom.app V (f.app V t)) hb'
    change k'.hom.app V (b.hom.app V (f.app V t)) = _ at he
    rw [hfb] at he
    exact he.symm.trans hp
  let μ : P.1.sheaf ⟶ Q.sheaf := ⟨{
    app V := TypeCat.ofHom fun t ↦ ⟨h.hom.app V (f.app V t), hs V t⟩
    naturality V W l := by
      ext t
      apply Subtype.ext
      have hh := ConcreteCategory.congr_hom (h.hom.naturality l) (f.app V t)
      simp only [ConcreteCategory.comp_apply] at hh
      change h.hom.app W (f.app W (P.1.sheaf.obj.map l t)) =
        (I.cocomplex.X 0).obj.map l (h.hom.app V (f.app V t))
      exact (congrArg (h.hom.app W)
        (ConcreteCategory.congr_hom (f.naturality l) t)).trans hh }⟩
  let ε : P.1.Iso Q := Sheaf.Torsor.Iso.ofHom μ (fun V g t ↦ by
    apply Subtype.ext
    change h.hom.app V (f.app V (P.1.vadd V g t)) =
      h.hom.app V (f.app V t) + (I.ι.f 0).hom.app V g
    exact (congrArg (h.hom.app V) (hfa V g t)).trans
      ((map_add (h.hom.app V).hom _ _).trans
        (congrArg (h.hom.app V (f.app V t) + ·)
          (congrArg (fun l ↦ l.hom.app V g) ha))))
  have hz' : ∃ z : ResolutionFramedLift T U I,
      relativeTorsorEquiv T U I (Quotient.mk _ P) = relativeFrameClass T U I z ∧
        z.1 = s ∧ (show (I.cocomplex.X 0).obj.obj (op U) from z.2.1) = 0 := by
    refine ⟨⟨s, ε.iso.hom.hom.app (op U) P.2⟩,
      relativeTorsorEquiv_presentation T U I P s ε, rfl, ?_⟩
    change h.hom.app (op U) (f.app (op U) P.2) = 0
    exact (congrArg (h.hom.app (op U)) hfτ).trans (map_zero _)
  obtain ⟨z, hPz, hzs, hz⟩ := hz'
  have hzi : (relativeSectionComplex T U I.cocomplex).iCycles 1
      (relativeFrameCycle T U I z) = relativeFrameElement T U I z := by
    unfold relativeFrameCycle
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
    exact ShortComplex.abCyclesIso_inv_apply_iCycles _ _
  have hn := (Classical.choose_spec (relativeExtensionComparison_existsUnique i G I)).1.onCocycle
    1 k hk (relativeFrameCycle T U I z)
  have hfst : (relativeForgetComplex T U I.cocomplex).f 1
      ((relativeSectionComplex T U I.cocomplex).iCycles 1 (relativeFrameCycle T U I z)) =
      (HomologicalComplex.extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex) ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).inv
        (k.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
            (supportedIntegralOne T))) := by
    apply (HomologicalComplex.extendXIso
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex) ComplexShape.embeddingUpNat
        (rfl : (1 : ℤ) = 1)).addCommGroupIsoToAddEquiv.injective
    let e := HomologicalComplex.extendXIso
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex) ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)
    change e.hom ((relativeForgetComplex T U I.cocomplex).f 1
      ((relativeSectionComplex T U I.cocomplex).iCycles 1
        (relativeFrameCycle T U I z))) = e.hom (e.inv _)
    rw [Iso.inv_hom_id_apply]
    change ((relativeForgetComplex T U I.cocomplex).f 1 ≫ e.hom)
      ((relativeSectionComplex T U I.cocomplex).iCycles 1 (relativeFrameCycle T U I z)) = _
    erw [relativeForget_fst]
    rw [hzi]
    have he := CategoryTheory.Iso.inv_hom_id_apply
      (relativeDegreeIso T U I.cocomplex 0)
      ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1,
        -(show (I.cocomplex.X 0).obj.obj (op U) from z.2.1))
    change (Prod.fst ((relativeDegreeIso T U I.cocomplex 0).hom
      ((relativeDegreeIso T U I.cocomplex 0).inv _))) = _
    rw [he]
    change (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1 = _
    exact (congrArg ((I.cocomplex.iCycles 1).hom.app
      (op (Scheme.Etale.mk (𝟙 T)))) hzs).trans
      (congrArg (fun l ↦ l.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (supportedIntegralOne T))) hki)
  have hsnd : (((CochainComplex.mappingCone
      (relativeSectionRestriction T U I.cocomplex)).shiftFunctorObjXIso
      (-1) (1 : ℤ) (1 + -1) rfl).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T U I.cocomplex) (1 + -1))
      ((relativeSectionComplex T U I.cocomplex).iCycles 1 (relativeFrameCycle T U I z)) = 0 := by
    rw [hzi]
    dsimp only [relativeFrameElement]
    change (homotopyCofiber.sndX (relativeSectionRestriction T U I.cocomplex) 0)
      ((relativeDegreeIso T U I.cocomplex 0).inv
        (_, -(show (I.cocomplex.X 0).obj.obj (op U) from z.2.1))) = 0
    rw [hz, neg_zero]
    let C := ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    let a := (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1
    have hs : relativeSnd T U I.cocomplex 0
        ((relativeDegreeIso T U I.cocomplex 0).inv (a, 0)) = 0 := by
      change Prod.snd ((relativeDegreeIso T U I.cocomplex 0).hom
        ((relativeDegreeIso T U I.cocomplex 0).inv (a, 0))) = 0
      exact congrArg Prod.snd
        (Iso.inv_hom_id_apply (relativeDegreeIso T U I.cocomplex 0) (a, 0))
    have he := congrArg (fun f ↦ f ((relativeDegreeIso T U I.cocomplex 0).inv (a, 0)))
      (coneSecondCoordinate T U I.cocomplex 0)
    apply (C.extendXIso ComplexShape.embeddingUpNat
      (rfl : (0 : ℤ) = 0)).addCommGroupIsoToAddEquiv.injective
    exact (he.symm.trans hs).trans (map_zero _).symm
  have hn' := hn hfst hsnd
  change relativeExtensionComparison i G I 1 (I.extMk k 2 rfl hk) = _ at hn'
  rw [hsign, map_neg] at hn'
  change -relativeExtensionComparison i G I 1 (relativeExtension i P) =
    relativeFrameClass T U I z at hn'
  rw [hPz]
  exact neg_eq_iff_eq_neg.mp hn'




attribute [local irreducible] relativeExtensionComparison

/-- Coefficient and framed-torsor morphisms preserve the two normalized classes.
Source: Stacks Tags 03AJ and 0A45, pushout and relative naturality
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: push the extension out along f. The contracted-product torsor maps to the
pushout by (t,g') |-> image(t)+g'. This is equivariant and kills the induced frame.
An equivariant map to Q identifies that contracted product with Q, so uniqueness
of the framed extension gives the Ext equality. The cone comparison is natural
in coefficients; apply its homology map and the normalization theorem. -/
theorem relative_extension_coefficient {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ G') (I : InjectiveResolution G) (J : InjectiveResolution G') (a : I.Hom J f)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G') (σ : P.1.sheaf.obj ⟶ Q.sheaf.obj)
    (hσ : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      σ.app V (P.1.vadd V g t) = Q.vadd V (f.hom.app V g) (σ.app V t)) :
    (relativeExtension i P).comp (Ext.mk₀ f) (add_zero 1) =
      relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩ ∧
    homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) a.hom) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i G' J 1
        (relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩) := by
  obtain ⟨E, a', b, hab, hE, f', hfa, hfb, hfτ, hβ⟩ :=
    (Classical.choose_spec (relativeExtension_existsUnique i
      ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩)).1
  change relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩ =
    hE.extClass at hβ
  constructor
  · have hn := relativeExtension_map i P f E a' b hab hE (𝟙 _) (σ ≫ f')
      (fun V g t ↦ by
        change f'.app V (σ.app V (P.1.vadd V g t)) = _
        exact (congrArg (f'.app V) (hσ V g t)).trans
          (hfa V (f.hom.app V g) (σ.app V t)))
      (fun V t ↦ by
        change b.hom.app V (f'.app V (σ.app V t)) = _
        exact hfb V (σ.app V t))
      hfτ
    rw [Ext.mk₀_id_comp] at hn
    exact hn.trans hβ.symm
  · rw [relative_extension_cohomology_normalization,
      relative_extension_cohomology_normalization, map_neg]
    exact congrArg Neg.neg
      (relativeTorsorEquiv_coefficient T (Scheme.Etale.mk i.openComplement.ι)
        f I J a P Q σ hσ (relativeSectionMap_square T
          (Scheme.Etale.mk i.openComplement.ι) a.hom))

/-- Canonical closed exchange on integral coefficients, with the constant comparison.
Source: Stacks Tag 0A45, closed base change
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionExchange {T Z T' Z' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T')
    (h : T' ⟶ T) (w : Z' ⟶ Z) (sq : CommSq w i' i h) :
    (upperStar AddCommGrpCat.{u + 1} h).obj
        ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) ⟶
      (lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z') :=
  (baseChangeMap AddCommGrpCat.{u + 1} sq).app (supportedIntegralConstant Z) ≫
    (lowerStar AddCommGrpCat.{u + 1} i').map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} w).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom

/-- The closed exchange used for etale pullback is invertible.
Source: Stacks Tag 0A45, closed exchange
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: etale base change identifies the sections of the two direct images on
the pulled-back site. The constant-sheaf comparison is invertible. Their composite
is the displayed exchange, so it too is invertible. -/
theorem relativeExtensionExchange_isIso {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h) :
    IsIso (relativeExtensionExchange i i' h w sq.toCommSq) := by
  have : IsIso (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq) :=
    isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
  dsimp only [relativeExtensionExchange]
  infer_instance

/-- The actual Ext pullback, transported by the canonical closed exchange.
Source: Stacks Tag 0A45, relative base change
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionPullback {T Z T' Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z')) G' 1 :=
  letI := relativeExtensionExchange_isIso i i' h w sq
  ((Ext.mk₀ (inv (relativeExtensionExchange i i' h w sq.toCommSq))).comp
    (β.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} h)) (zero_add 1)).comp
      (Ext.mk₀ (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _).symm f))
      (add_zero 1)

/-- The pulled frame, including the identification of the two complementary opens.
Source: Stacks Tag 03AJ, pullback of framed torsors
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionPulledFrame {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj) :
    Sheaf.Torsor.WithSection G' (Scheme.Etale.mk i'.openComplement.ι) :=
  ⟨Q, Q.sheaf.obj.map ((eqToHom (congrArg (fun W : T'.Opens ↦ Scheme.Etale.mk W.ι) hW)) ≫
      openSectionPullback h i.openComplement).op
        (b.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2)⟩

private theorem integralConstantComposition {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (k : X ⟶ Z) (hk : k = g ≫ f) :
    (upperStarComp AddCommGrpCat.{u + 1} g f k hk).hom.app (supportedIntegralConstant Z) ≫
      (upperStar AddCommGrpCat.{u + 1} g).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  subst k
  exact Scheme.upperStarConstantSheafIso_comp AddCommGrpCat.{u + 1} g f
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralBaseChangeUnit {T' T D' D : Scheme.{u}}
    (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (hD : D' ⟶ D) (sq : CommSq hD i' i h) :
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
      (upperStar AddCommGrpCat.{u + 1} h).map (supportedIntegralUnit i) ≫
        relativeExtensionExchange i i' h hD sq = supportedIntegralUnit i' := by
  let P := supportedIntegralConstant T
  let H := upperStar AddCommGrpCat.{u + 1} h
  let HD := upperStar AddCommGrpCat.{u + 1} hD
  let L := lowerStar AddCommGrpCat.{u + 1} i'
  let c {X Y : Scheme.{u}} (f : X ⟶ Y) := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    f).hom.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hc : (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app P ≫
      HD.map (c i) ≫ c hD = (upperStar AddCommGrpCat.{u + 1} i').map (c h) ≫ c i' := by
    dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [Scheme.upperStarConstantSheafIso_comp]
    apply (cancel_epi ((upperStarComp AddCommGrpCat.{u + 1} i' h (hD ≫ i) sq.w).hom.app P)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (integralConstantComposition i' h (hD ≫ i) sq.w).symm
  simp only [supportedIntegralUnit, relativeExtensionExchange, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  change (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ H.map ((upperStarLowerStarAdjunction
        AddCommGrpCat.{u + 1} i).unit.app P) ≫ H.map ((lowerStar
          AddCommGrpCat.{u + 1} i).map (c i)) ≫
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app (supportedIntegralConstant D) ≫
        L.map (c hD) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i').unit.app
      (supportedIntegralConstant T') ≫ L.map (c i')
  rw [reassoc_of% (baseChangeMap_naturality AddCommGrpCat.{u + 1} sq (c i)),
    reassoc_of% (map_unit_baseChangeMap_app AddCommGrpCat.{u + 1} sq P)]
  rw [← L.map_comp, ← L.map_comp, hc]
  simp only [L.map_comp]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i').unit.naturality
    (c h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp [c]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralUnit_section {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (V : Y.Etale) (m : ULift.{u + 1} ℤ) :
    (supportedIntegralUnit g).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      ((sheafSections Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
      e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      adjZ.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      f.op)).hom m)).symm
  let θ := supportedIntegralUnit g
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openSectionPullback_isIso {T T' : Scheme.{u}}
    (h : T' ⟶ T)
    (W : T.Opens) : IsIso (openSectionPullback h W) := by
  let e : Scheme.Etale.mk (h ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk W.ι) :=
    MorphismProperty.Over.isoMk (isPullback_morphismRestrict h W).isoPullback
      (isPullback_morphismRestrict h W).isoPullback_hom_snd
  have he : e.hom = openSectionPullback h W := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (isPullback_morphismRestrict h W).isoPullback.hom ≫ pullback.fst W.ι h =
        pullback.lift (morphismRestrict h W) (h ⁻¹ᵁ W).ι (morphismRestrict_ι h W) ≫
          pullback.fst W.ι h
      rw [pullback.lift_fst]
      exact (isPullback_morphismRestrict h W).isoPullback_hom_fst
    · change (isPullback_morphismRestrict h W).isoPullback.hom ≫ pullback.snd W.ι h =
        pullback.lift (morphismRestrict h W) (h ⁻¹ᵁ W).ι (morphismRestrict_ι h W) ≫
          pullback.snd W.ι h
      rw [pullback.lift_snd]
      exact (isPullback_morphismRestrict h W).isoPullback_hom_snd
  rw [← he]
  infer_instance

/-- Etale pullback preserves the extension class and its relative realization.
The resolution lift and torsor map are arbitrary representatives of the given pullback.
Source: Stacks Tags 03AJ and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: exact inverse image preserves the extension. Closed exchange carries its
quotient to the new supported integers and is compatible with the unit p. Its
torsor map remains equivariant and kills the pulled frame. Uniqueness therefore
gives the Ext equality. Supported-Hom naturality identifies the resolution
transfer with this Ext pullback; normalization gives the second equality. -/
theorem relative_extension_pullback {T Z T' Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (a : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
    (hb : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      b.app V (P.1.vadd V g t) =
        Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V.unop))
          (f.hom.app V g) (b.app V t)) :
    relativeExtensionPullback i i' h w sq f (relativeExtension i P) =
      relativeExtension i' (relativeExtensionPulledFrame i i' h hW P Q b) ∧
    homologyMap (relativeTransfer h i.openComplement I.cocomplex J.cocomplex a) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      -relativeTorsorEquiv T' (Scheme.Etale.mk (h ⁻¹ᵁ i.openComplement).ι) J
        (Quotient.mk _ ⟨Q, Q.sheaf.obj.map (openSectionPullback h i.openComplement).op
          (b.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2)⟩) := by
  let F := lowerStar AddCommGrpCat.{u + 1} h
  let L := upperStar AddCommGrpCat.{u + 1} h
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h
  let B := MorphismProperty.Over.pullback @Etale ⊤ h
  let c := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let e := relativeExtensionExchange i i' h w sq.toCommSq
  have : IsIso e := relativeExtensionExchange_isIso i i' h w sq
  let R := relativeExtensionPulledFrame i i' h hW P Q b
  constructor
  · obtain ⟨E', a', b', hab', hE', f', hfa', hfb', hfτ', hβ'⟩ :=
      (Classical.choose_spec (relativeExtension_existsUnique i' R)).1
    change relativeExtension i' R = hE'.extClass at hβ'
    let r := (adj.homEquiv _ _).toFun e
    have hp : supportedIntegralUnit i ≫ r =
        supportedIntegralUnit h ≫ F.map (supportedIntegralUnit i') := by
      change supportedIntegralUnit i ≫ adj.homEquiv _ _ e =
        adj.homEquiv _ _ c.hom ≫ F.map (supportedIntegralUnit i')
      rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
      apply congrArg (adj.homEquiv _ _)
      have hu := integralBaseChangeUnit h i i' w sq.toCommSq
      change c.inv ≫ L.map (supportedIntegralUnit i) ≫ e = _ at hu
      have hh := congrArg (fun t ↦ c.hom ≫ t) hu
      simpa only [← Category.assoc, c.hom_inv_id, Category.id_comp] using hh
    let φ := b ≫ Functor.whiskerLeft B.op f'
    have hφa (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V) :
        φ.app V (P.1.vadd V g t) =
          (show (F.obj E').obj.obj V from φ.app V t) + (f ≫ F.map a').hom.app V g := by
      change f'.app (op (B.obj V.unop)) (b.app V (P.1.vadd V g t)) = _
      exact (congrArg (f'.app (op (B.obj V.unop))) (hb V g t)).trans
        (hfa' (op (B.obj V.unop)) (f.hom.app V g) (b.app V t))
    have hφb (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V) :
        (F.map b').hom.app V (φ.app V t) =
          (supportedIntegralUnit i ≫ r).hom.app V
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                V ⟨1⟩) := by
      rw [hp]
      exact (hfb' (op (B.obj V.unop)) (b.app V t)).trans
        (congrArg ((supportedIntegralUnit i').hom.app (op (B.obj V.unop)))
          (integralUnit_section h V.unop ⟨1⟩).symm)
    let U := Scheme.Etale.mk i.openComplement.ι
    let U' := Scheme.Etale.mk i'.openComplement.ι
    let k : U' ⟶ B.obj U :=
      eqToHom (congrArg (fun W : T'.Opens ↦ Scheme.Etale.mk W.ι) hW) ≫
        openSectionPullback h i.openComplement
    have hk : IsIso k := by
      have : IsIso (openSectionPullback h i.openComplement) :=
        openSectionPullback_isIso h i.openComplement
      dsimp only [k]
      infer_instance
    have hφτ : (show (F.obj E').obj.obj (op U) from φ.app (op U) P.2) = 0 := by
      apply (asIso (E'.obj.map k.op)).addCommGroupIsoToAddEquiv.injective
      rw [map_zero]
      have hn := ConcreteCategory.congr_hom (f'.naturality k.op) (b.app (op U) P.2)
      change _ = E'.obj.map k.op (φ.app (op U) P.2) at hn
      change E'.obj.map k.op (φ.app (op U) P.2) = 0
      exact hn.symm.trans hfτ'
    obtain ⟨E, a₀, b₀, hab₀, hE, hβ, α, hαa, hαb⟩ :=
      relativeExtension_morphism i P f (F.obj E') (F.map a') (F.map b')
        (by rw [← F.map_comp, hab', F.map_zero]) r φ hφa hφb hφτ
    let α' := (adj.homEquiv _ _).symm α
    let f₀ := (adj.homEquiv _ _).symm f
    have hα'a : L.map a₀ ≫ α' = f₀ ≫ a' := by
      exact (adj.homEquiv_naturality_left_symm a₀ α).symm.trans
        ((congrArg (adj.homEquiv _ _).symm hαa).trans
          (adj.homEquiv_naturality_right_symm f a'))
    have hα'b : α' ≫ b' = L.map b₀ ≫ e := by
      exact (adj.homEquiv_naturality_right_symm α b').symm.trans
        ((congrArg (adj.homEquiv _ _).symm hαb).trans
          ((adj.homEquiv_naturality_left_symm b₀ r).trans
            (congrArg (L.map b₀ ≫ ·) ((adj.homEquiv _ _).symm_apply_apply e))))
    have hn := (hE.map_of_exact L).extClass_naturality hE'
      (ShortComplex.homMk f₀ α' e hα'a.symm hα'b)
    change (hE.map_of_exact L).extClass.comp (Ext.mk₀ f₀) (add_zero 1) =
      (Ext.mk₀ e).comp hE'.extClass (zero_add 1) at hn
    rw [← Ext.mapExactFunctor_extClass L hE] at hn
    rw [← hβ, ← hβ'] at hn
    change ((Ext.mk₀ (inv e)).comp
      ((relativeExtension i P).mapExactFunctor L) (zero_add 1)).comp
        (Ext.mk₀ f₀) (add_zero 1) = _
    rw [Ext.comp_assoc, hn, ← Ext.comp_assoc, Ext.mk₀_comp_mk₀,
      IsIso.inv_hom_id, Ext.mk₀_id_comp]
    all_goals omega
  · rw [relative_extension_cohomology_normalization, map_neg]
    apply congrArg Neg.neg
    exact relativeTorsorEquiv_transfer h i.openComplement f I J a ha P Q b hb
      (relativeTransfer_square h i.openComplement I.cocomplex J.cocomplex a)

/-- Restriction of supported integers is determined by its composite with p'.
This formulation needs only inclusion of complementary opens, not a factorization
between the closed scheme structures.
Source: Stacks Tag 0A45, enlargement of support
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: the kernel of p' is the extension by zero from W'. Its composite with p
is zero because W' is contained in W. The cokernel property of p' gives a unique
factorization through its quotient. Epimorphy of p' proves uniqueness. -/
theorem relativeExtensionSupportMap_existsUnique {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement) :
    ∃! q : (lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z') ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z),
      supportedIntegralUnit i' ≫ q = supportedIntegralUnit i := by
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  obtain ⟨L', t', ht', hT', η', hη', hηt'⟩ :=
    exists_integral_openClosed_sections i' i'.openComplement rfl
  let r : Scheme.Etale.mk i'.openComplement.ι ⟶
      Scheme.Etale.mk i.openComplement.ι :=
    MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)
  let l : L' ⟶ L := (η' L).symm (L.obj.map r.op (η L (𝟙 L)))
  have hlt : l ≫ t = t' := by
    apply (η' _).injective
    rw [hη', hηt']
    change t.hom.app _ ((η' L) ((η' L).symm _)) = _
    rw [AddEquiv.apply_symm_apply]
    rw [← ConcreteCategory.comp_apply, t.hom.naturality, ConcreteCategory.comp_apply]
    have he : t.hom.app _ (η L (𝟙 L)) = η _ t := by
      simpa only [Category.id_comp] using (hη t (𝟙 L)).symm
    rw [he, hηt]
    exact (ConcreteCategory.congr_hom
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
          r.op) ⟨1⟩).symm
  have hk : t' ≫ supportedIntegralUnit i = 0 := by
    rw [← hlt, Category.assoc]
    change t ≫ supportedIntegralUnit i = 0 at ht
    rw [ht, comp_zero]
  let q := hT'.gIsCokernel.desc (CokernelCofork.ofπ (supportedIntegralUnit i) hk)
  have hq : supportedIntegralUnit i' ≫ q = supportedIntegralUnit i :=
    hT'.gIsCokernel.fac _ WalkingParallelPair.one
  have : Epi (supportedIntegralUnit i') := hT'.epi_g
  exact ⟨q, hq, fun q' hq' ↦ (cancel_epi (supportedIntegralUnit i')).1 (hq'.trans hq.symm)⟩

/-- The canonical restriction of the supported integer quotient.
Source: Stacks Tag 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionSupportMap {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement) :
    (lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z') ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) :=
  Classical.choose (relativeExtensionSupportMap_existsUnique i i' hW)

/-- Restrict the specified frame to a smaller complementary open.
Source: Stacks Tag 03AJ, framed relative refinement
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionRestrictedFrame {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    Sheaf.Torsor.WithSection G (Scheme.Etale.mk i'.openComplement.ι) :=
  ⟨P.1, P.1.sheaf.obj.map
    (MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)).op P.2⟩

/-- The restriction square for two complementary opens commutes.
Source: Stacks Tag 0A45, enlargement of support
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: restriction along W' -> W followed by W -> T is restriction along W' -> T.
Evaluate the presheaf composition law in every resolution degree and extend by zero. -/
theorem relativeExtensionEnlarge_square {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I)) ≫
        relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I =
      relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I ≫
        HomologicalComplex.extendMap
          (etaleSectionMap
            (show Scheme.Etale.mk i'.openComplement.ι ⟶ Scheme.Etale.mk i.openComplement.ι from
              MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
          ComplexShape.embeddingUpNat := by
  rw [Category.id_comp]
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  ext n : 1
  change (I.X n).obj.map _ = (I.X n).obj.map _ ≫ (I.X n).obj.map _
  rw [← Functor.map_comp]
  congr 1
  exact congrArg Quiver.Hom.op ((MorphismProperty.Over.mkIdTerminal @Etale T).hom_ext _ _)

/-- The actual cone map for enlargement of support, with identity on global sections.
Source: Stacks Tag 0A45, restriction of the open term
(blueprint: lem-pur-relative-extension-cohomology-normalization). -/
def relativeExtensionEnlargeComplex {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) I ⟶
      relativeSectionComplex T (Scheme.Etale.mk i'.openComplement.ι) I :=
  relativeFiberMap (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I)
    (relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I) (𝟙 _)
    (HomologicalComplex.extendMap
      (etaleSectionMap
        (show Scheme.Etale.mk i'.openComplement.ι ⟶ Scheme.Etale.mk i.openComplement.ι from
          MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
      ComplexShape.embeddingUpNat) (relativeExtensionEnlarge_square i i' hW I)

attribute [local irreducible] relativeExtensionEnlargeComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Enlarging support precomposes beta with quotient restriction and restricts its frame.
Source: Stacks Tags 03AJ and 0A45
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: pull the extension back along the canonical quotient restriction. The map
t |-> (f(t),p'(1)) is equivariant and vanishes on the restricted frame. Uniqueness
identifies its class with the new framed extension, proving the first equation.
The normalized kernel inclusions commute with restriction of open sections.
Taking homology gives the second equation. -/
theorem relative_extension_enlarge {T Z Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    (Ext.mk₀ (relativeExtensionSupportMap i i' hW)).comp
        (relativeExtension i P) (zero_add 1) =
      relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P) ∧
    (homologyMap (relativeExtensionEnlargeComplex i i' hW I.cocomplex) 1).hom
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i' G I 1
        (relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P)) := by
  let U := Scheme.Etale.mk i.openComplement.ι
  let U' := Scheme.Etale.mk i'.openComplement.ι
  let r : U' ⟶ U := MorphismProperty.Over.homMk (T.homOfLE hW) (by dsimp only [U, U']; simp)
  obtain ⟨E, a, b, hab, hE, f, hfa, hfb, hfτ, hβ⟩ :=
    (Classical.choose_spec (relativeExtension_existsUnique i P)).1
  change relativeExtension i P = hE.extClass at hβ
  have hp : supportedIntegralUnit i' ≫ relativeExtensionSupportMap i i' hW =
      supportedIntegralUnit i :=
    (Classical.choose_spec (relativeExtensionSupportMap_existsUnique i i' hW)).1
  constructor
  · have hn := relativeExtension_map i'
      (relativeExtensionRestrictedFrame i i' hW P) (𝟙 G) E a b hab hE
      (relativeExtensionSupportMap i i' hW) f
      (by
        intro V g t
        change f.app V (P.1.vadd V g t) = f.app V t + a.hom.app V g
        exact hfa V g t)
      (by intro V t; rw [hp]; exact hfb V t)
      (by
        have hn := ConcreteCategory.congr_hom (f.naturality r.op) P.2
        change f.app (op U') (P.1.sheaf.obj.map r.op P.2) =
          E.obj.map r.op (f.app (op U) P.2) at hn
        change f.app (op U') (P.1.sheaf.obj.map r.op P.2) = 0
        exact hn.trans ((congrArg (E.obj.map r.op) hfτ).trans (map_zero _)))
    rw [Ext.comp_mk₀_id, ← hβ] at hn
    exact hn.symm
  · rw [relative_extension_cohomology_normalization,
      relative_extension_cohomology_normalization, map_neg]
    apply congrArg Neg.neg
    let hT := MorphismProperty.Over.mkIdTerminal @Etale T
    let : Injective (I.cocomplex.X 0) := I.injective 0
    obtain ⟨s, ⟨ε⟩⟩ := Sheaf.Torsor.exists_equiv_lifts (G := G)
      (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1) hT
      (resolutionLiftSequence_shortExact T I) P.1
    rw [relativeTorsorEquiv_presentation T U I P s ε,
      relativeTorsorEquiv_presentation T U' I
        (relativeExtensionRestrictedFrame i i' hW P) s ε]
    have he := relativeFrameClass_map_eq T U I U' I (𝟙 _) (etaleSectionMap r I.cocomplex)
      (by
        rw [extendMap_id]
        change (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I.cocomplex)) ≫
          relativeSectionRestriction T U' I.cocomplex = _
        exact relativeExtensionEnlarge_square i i' hW I.cocomplex)
      ⟨s, ε.iso.hom.hom.app (op U) P.2⟩
      ⟨s, ε.iso.hom.hom.app (op U') (P.1.sheaf.obj.map r.op P.2)⟩ 0
      (by simp)
      (by
        simp only [map_zero]
        apply (sub_eq_zero.mpr ?_).symm
        exact congrArg Subtype.val
          (ConcreteCategory.congr_hom (ε.iso.hom.hom.naturality r.op) P.2))
    simpa only [extendMap_id, relativeExtensionEnlargeComplex,
      relativeExtensionRestrictedFrame, r, U, U', relativeSections, relativeSectionComplex] using he

/-- The given equivariant extension map identifies P with the fibre over p(1).
Together with its equivariance equation this retains the specified G-action. This
is also the fibre over one of the extension pulled back along p.
Source: Stacks Tag 03AJ, free torsor extension, relative refinement
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: work locally with a section t0 of P. Every torsor section is uniquely g+t0,
and equivariance identifies its image with f(t0)+a(g). Short exactness identifies
all points of the fibre with exactly these elements. Thus the map is locally
bijective. The map is natural and both objects are sheaves, so local inverses
glue to an inverse on every object. The displayed action is the original one. -/
theorem relative_extension_fibre {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (hfa : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      @id (E.obj.obj V) (f.app V (P.1.vadd V g t)) =
        @id (E.obj.obj V) (f.app V t) + a.hom.app V g)
    (hfb : ∀ (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V),
      b.hom.app V (f.app V t) = (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) :
    ∀ V : T.Etaleᵒᵖ, Function.Bijective (fun t : P.1.sheaf.obj.obj V ↦
      (⟨f.app V t, hfb V t⟩ : {e : E.obj.obj V // b.hom.app V e =
        (supportedIntegralUnit i).hom.app V
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)})) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let s := (supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    (supportedIntegralOne T)
  let Q : Sheaf.Torsor G := Sheaf.Torsor.lifts hT hE s
  have hone (V : T.Etaleᵒᵖ) :
      (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩) =
        ((lowerStar AddCommGrpCat.{u + 1} i).obj
          (supportedIntegralConstant Z)).obj.map (hT.from V.unop).op s := by
    dsimp only [s]
    rw [← ConcreteCategory.comp_apply, ← (supportedIntegralUnit i).hom.naturality,
      ConcreteCategory.comp_apply]
    congr 1
    exact (ConcreteCategory.congr_hom
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
          (hT.from V.unop).op) ⟨1⟩)
  have hpoint (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V) := (hfb V t).trans (hone V)
  let g : P.1.sheaf ⟶ Q.sheaf :=
    ⟨{ app V := TypeCat.ofHom (fun t ↦ ⟨f.app V t, hpoint V t⟩)
       naturality V V' k := by
         ext t
         apply Subtype.ext
         exact ConcreteCategory.congr_hom (f.naturality k) t }⟩
  let e : P.1.Iso Q := Sheaf.Torsor.Iso.ofHom g (fun V a t ↦ Subtype.ext (hfa V a t))
  intro V
  let eV : P.1.sheaf.obj.obj V ≅ Q.sheaf.obj.obj V :=
    ((sheafToPresheaf _ _).mapIso e.iso).app V
  have he : Function.Bijective (g.hom.app V) := eV.toEquiv.bijective
  refine ⟨fun x y h ↦ he.1 (Subtype.ext (congrArg (fun z ↦ z.1) h)), ?_⟩
  intro y
  obtain ⟨t, ht⟩ := he.2 ⟨y.1, y.2.trans (hone V)⟩
  exact ⟨t, Subtype.ext (congrArg (fun z ↦ z.1) ht)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Forgetting support gives the ordinary free torsor extension with the original action,
and hence the positive ordinary H1 class. The morphism of extensions identifies its
pullback fibre over one with P, retaining the action rather than just its H1 image.
Source: Stacks Tag 03AJ, free torsor extension and fibre over one
(blueprint: lem-pur-relative-extension-cohomology-normalization).
Proof: pull a representing relative extension back by p. Its fibre over one is
P through t |-> (f(t),1); in any local trivialization this is g |-> f(t0)+a(g),
so it respects the original G-action and is bijective. The universal quotient
presentation of the ordinary free extension maps to this pullback, sending the
generator t to (f(t),1) and g to (a(g),0). The same local coordinates give an
isomorphism of extensions. Naturality of extension classes gives the displayed
Ext equality. The projection from the signed cone forgets the frame, and the
Ext-normalized classification gives the positive ordinary torsor H1 class. -/
theorem relative_extension_forget {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (c : ResolutionSectionCanonicalComparison G I)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (hE : (ShortComplex.mk E.inclusion E.projection E.inclusion_projection).ShortExact) :
    (Ext.mk₀ (supportedIntegralUnit i)).comp (relativeExtension i P) (zero_add 1) =
      hE.extClass ∧
    relativeForgetH1 T i.openComplement G I c
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
        (Quotient.mk _ P.1) := by
  obtain ⟨E', a, b, hab, hE', f, hfa, hfb, hfτ, hβ⟩ :=
    (Classical.choose_spec (relativeExtension_existsUnique i P)).1
  obtain ⟨α, ⟨hαa, hαf⟩, _⟩ := E.universal E' a
    (fun V t ↦ f.app V t)
    (fun V V' k t ↦ (ConcreteCategory.congr_hom (f.naturality k) t).symm) hfa
  have hαb : α ≫ b = E.projection ≫ supportedIntegralUnit i := by
    obtain ⟨l, hl, huniq⟩ := E.universal _ 0
      (fun V _ ↦ (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
      (by
        intro V V' k t
        rw [← ConcreteCategory.comp_apply, ← (supportedIntegralUnit i).hom.naturality,
          ConcreteCategory.comp_apply]
        congr 1
        exact (ConcreteCategory.congr_hom
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality k)
          ⟨1⟩).symm)
      (by intro V g t; change _ = _ + 0; exact (add_zero _).symm)
    apply (huniq _ ⟨by rw [← Category.assoc, hαa, hab], ?_⟩).trans
      (huniq _ ⟨by rw [← Category.assoc, E.inclusion_projection, zero_comp], ?_⟩).symm
    · intro V t
      change b.hom.app V (α.hom.app V (E.generator V t)) = _
      rw [hαf, hfb]
    · intro V t
      change (supportedIntegralUnit i).hom.app V
        (E.projection.hom.app V (E.generator V t)) = _
      rw [E.projection_generator]
  change relativeExtension i P = hE'.extClass at hβ
  constructor
  · have h := hE.extClass_naturality hE'
      (ShortComplex.homMk (𝟙 _) α (supportedIntegralUnit i)
        (by simpa using hαa.symm) hαb)
    change hE.extClass.comp (Ext.mk₀ (𝟙 G)) (add_zero 1) =
      (Ext.mk₀ (supportedIntegralUnit i)).comp hE'.extClass (zero_add 1) at h
    rw [Ext.comp_mk₀_id, ← hβ] at h
    exact h.symm
  · rw [relative_extension_cohomology_normalization]
    change c.globalEquiv 1
      (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat
          (rfl : (1 : ℤ) = 1)).hom
        (HomologicalComplex.homologyMap
          (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex) 1
          (-relativeTorsorEquiv T (Scheme.Etale.mk i.openComplement.ι) I
            (Quotient.mk _ P)))) = _
    rw [map_neg, map_neg, map_neg]
    let hT := MorphismProperty.Over.mkIdTerminal @Etale T
    let : Injective (I.cocomplex.X 0) := I.injective 0
    obtain ⟨s, ⟨ε⟩⟩ := Sheaf.Torsor.exists_equiv_lifts (G := G)
      (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1) hT
      (resolutionLiftSequence_shortExact T I) P.1
    rw [relativeTorsorEquiv_presentation T (Scheme.Etale.mk i.openComplement.ι) I P s ε,
      relativeFrameClass_forget, neg_neg]
    have hp : (Quotient.mk _ P.1 : _root_.Quotient (Sheaf.Torsor.setoid (G := G))) =
        Quotient.mk _ (Sheaf.Torsor.lifts (G := G) hT (resolutionLiftSequence_shortExact T I) s) :=
      Quotient.sound ⟨ε⟩
    rw [hp, Sheaf.Torsor.classH1_lifts (G := G)
      (ι := I.ι.f 0) (d := I.cocomplex.toCycles 0 1)]
    rfl

end AlgebraicGeometry.Etale
