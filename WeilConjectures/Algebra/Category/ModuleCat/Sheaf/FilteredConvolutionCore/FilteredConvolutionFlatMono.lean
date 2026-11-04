/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # Monomorphisms after tensoring with complexes of flat module sheaves

Coproducts of module sheaves are exact, and tensoring with a complex whose terms are flat
preserves monomorphisms of complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- Coproducts indexed by a small type are exact in module sheaves (AB4). -/
private theorem hasExactColimitsOfShape_discrete (R : Sheaf J CommRingCat.{w}) (ι : Type) :
    HasExactColimitsOfShape (Discrete ι) (Modules R) := by
  have := isGrothendieckAbelian_coefficientUniverse.{u, v, w} (J := J)
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have : HasExactColimitsOfShape (Discrete (ULift.{w} ι)) (Modules R) := inferInstance
  exact HasExactColimitsOfShape.of_domain_equivalence (C := Modules R)
    (Discrete.equivalence Equiv.ulift)

/-- Monomorphisms of module sheaves are stable under coproducts indexed by a small type. -/
private theorem monomorphisms_isStableUnderColimitsOfShape_discrete
    (R : Sheaf J CommRingCat.{w}) (ι : Type) :
    (MorphismProperty.monomorphisms (Modules R)).IsStableUnderColimitsOfShape (Discrete ι) := by
  have := hasExactColimitsOfShape_discrete R ι
  infer_instance

/-- The morphism `X.mapObj p j ⟶ Y.mapObj p j` induced by a family of monomorphisms is a
monomorphism, provided monomorphisms are stable under coproducts indexed by the fibre. -/
private theorem mono_gradedObject_mapMap {I K : Type} {D : Type*} [Category* D]
    {X Y : GradedObject I D} (φ : X ⟶ Y) (p : I → K) [X.HasMap p] [Y.HasMap p] (j : K)
    [(MorphismProperty.monomorphisms D).IsStableUnderColimitsOfShape (Discrete (p ⁻¹' {j}))]
    (hφ : ∀ i, Mono (φ i)) : Mono (GradedObject.mapMap φ p j) :=
  MorphismProperty.IsStableUnderColimitsOfShape.condition
    (Discrete.functor (X.mapObjFun p j)) (Discrete.functor (Y.mapObjFun p j)) _ _
    (colimit.isColimit _) (colimit.isColimit _)
    (Discrete.natTrans fun i ↦ φ i.as.1) (fun i ↦ hφ i.as.1) (GradedObject.mapMap φ p j)
    (fun i ↦ GradedObject.ι_mapMap φ p i.as.1 j i.as.2)

/-- Coproducts of monomorphisms of module sheaves are monomorphisms (AB4). -/
theorem mono_sigmaMap {ι : Type} {X Y : ι → Modules R} (f : ∀ i, X i ⟶ Y i)
    [∀ i, Mono (f i)] : Mono (Limits.Sigma.map f) := by
  have := hasExactColimitsOfShape_discrete R ι
  infer_instance

/-- Coproducts of monomorphisms of complexes of module sheaves are monomorphisms. -/
theorem mono_sigmaMap_complex {ι : Type} {X Y : ι → Complex R} (f : ∀ i, X i ⟶ Y i)
    [∀ i, Mono (f i)] : Mono (Limits.Sigma.map f) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  have := monomorphisms_isStableUnderColimitsOfShape_discrete R ι
  refine MorphismProperty.IsStableUnderColimitsOfShape.condition
    (Discrete.functor X ⋙ HomologicalComplex.eval _ _ n)
    (Discrete.functor Y ⋙ HomologicalComplex.eval _ _ n)
    ((HomologicalComplex.eval _ _ n).mapCocone (colimit.cocone (Discrete.functor X)))
    ((HomologicalComplex.eval _ _ n).mapCocone (colimit.cocone (Discrete.functor Y)))
    (isColimitOfPreserves _ (colimit.isColimit _)) (isColimitOfPreserves _ (colimit.isColimit _))
    (Functor.whiskerRight (Discrete.natTrans fun i ↦ f i.as) _) (fun i ↦ ?_) _ fun i ↦ ?_
  · exact (inferInstance : Mono ((f i.as).f n))
  · exact congr_arg (fun g ↦ HomologicalComplex.Hom.f g n) (Sigma.ι_map f i.as)

/-- Tensoring on the left with a complex whose terms are flat preserves monomorphisms. -/
theorem mono_whiskerLeft_of_isFlatOnSite (X : Complex R)
    (hX : ∀ i, IsFlatOnSite (R := R) (X.X i)) {A B : Complex R} (f : A ⟶ B) [Mono f] :
    Mono (X ◁ f) := by
  have hf (p q : ℤ) : Mono (X.X q ◁ f.f p) := by
    obtain ⟨h₁, -⟩ := hX q
    have := @Limits.preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (siteSheafTensorRightIso R (X.X q)) h₁
    have : Mono (f.f p ▷ X.X q) := (tensorRight (X.X q)).map_mono (f.f p)
    rw [← Category.comp_id (X.X q ◁ f.f p), ← Iso.hom_inv_id (β_ (X.X q) (B.X p)),
      ← Category.assoc,
      BraidedCategory.braiding_naturality_right]
    infer_instance
  have : HasColimitsOfSize.{0, 0} (Modules R) := hasColimitsOfSizeShrink.{0, 0, w, w} _
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  have := monomorphisms_isStableUnderColimitsOfShape_discrete R
  refine mono_gradedObject_mapMap _ _ n fun ⟨q, p⟩ ↦ ?_
  simpa using hf p q

end SheafOfModules.FilteredConvolutionCore
