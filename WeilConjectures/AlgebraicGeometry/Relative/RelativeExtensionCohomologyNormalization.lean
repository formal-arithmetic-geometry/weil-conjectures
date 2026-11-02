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
public import WeilConjectures.AlgebraicGeometry.Curve.ExtensionPresentationShortExact
public import WeilConjectures.AlgebraicGeometry.Curve.RelativeTorsorExtension
public import WeilConjectures.SmoothPurity.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.SmoothPurity.OpenClosedIntegralSections

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

attribute [local instance] additiveSelfForget_additive

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
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
    simpa only [hki] using he
  exact heq.symm.trans hh

attribute [local irreducible] relativeExtensionComparison

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

attribute [local irreducible] relativeExtensionEnlargeComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Etale
