/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpoints
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Composition of normalized ordinary coefficient endpoints

Source: Stacks 0D6D; exact-single coherence and adjunction composition
(blueprint: lem-sp-p1-kummer-scalar-endpoint-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] cachedModSheafify

private theorem lineMap_ext
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u})
    (f g : Scheme.finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB))
    (h : ∀ (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W),
      f.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
        g.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z)) : f = g := by
  apply (Scheme.lineHomEquiv T N A hA _).injective
  ext W z
  simpa only [Scheme.lineHomEquiv_generator] using h W z

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem inverse_conjugate_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (δ : R₁ ⟶ R₂) [NatTrans.CommShift δ ℤ] :
    NatTrans.CommShift ((conjugateEquiv a₁ a₂).symm δ) ℤ := by
  dsimp [conjugateEquiv, mateEquiv, Iso.homCongr, TwoSquare.equivNatTrans,
    TwoSquare.natTrans, TwoSquare.mk]
  infer_instance

private theorem shifted_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F : C ⥤ D} {U : D ⥤ C} {G : D ⥤ E} {V : E ⥤ D}
    {H : C ⥤ E} {W : E ⥤ C}
    [U.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (ρ : V ⋙ U ≅ W)
    [NatTrans.CommShift ρ.hom ℤ]
    {X : C} {Y : D} {Z : E} (f : F.obj X ⟶ Y) (g : G.obj Y ⟶ Z)
    (h : H.obj X ⟶ Z)
    (hh : G.map f ≫ g = (Adjunction.leftAdjointCompIso a b c ρ).hom.app X ≫ h)
    (n : ℤ) :
    G.map ((Adjunction.LeftAdjointCommShift.iso a n).hom.app X ≫ f⟦n⟧') ≫
        (Adjunction.LeftAdjointCommShift.iso b n).hom.app Y ≫ g⟦n⟧' =
      (Adjunction.leftAdjointCompIso a b c ρ).hom.app (X⟦n⟧) ≫
        (Adjunction.LeftAdjointCommShift.iso c n).hom.app X ≫ h⟦n⟧' := by
  let := a.leftAdjointCommShift ℤ
  let := b.leftAdjointCommShift ℤ
  let := c.leftAdjointCommShift ℤ
  let : a.CommShift ℤ := a.commShift_of_rightAdjoint ℤ
  let : b.CommShift ℤ := b.commShift_of_rightAdjoint ℤ
  let : c.CommShift ℤ := c.commShift_of_rightAdjoint ℤ
  let α := Adjunction.leftAdjointCompIso a b c ρ
  have hc : NatTrans.CommShift α.hom ℤ :=
    inverse_conjugate_shift c (a.comp b) ρ.inv
  let := hc
  change G.map ((F.commShiftIso n).hom.app X ≫ f⟦n⟧') ≫
      (G.commShiftIso n).hom.app Y ≫ g⟦n⟧' =
    α.hom.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X ≫ h⟦n⟧'
  rw [Functor.map_comp, Category.assoc]
  have hn := (G.commShiftIso n).hom.naturality f
  change G.map (f⟦n⟧') ≫ (G.commShiftIso n).hom.app Y =
    (G.commShiftIso n).hom.app (F.obj X) ≫ (G.map f)⟦n⟧' at hn
  rw [reassoc_of% hn, ← (shiftFunctor E n).map_comp, hh,
    (shiftFunctor E n).map_comp]
  have hα := NatTrans.shift_app_comm α.hom n X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hα
  simpa only [α, Category.assoc] using congrArg (· ≫ h⟦n⟧') hα

private theorem constantSheaf_ext_top
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f g : ordinaryFiniteConstant A T ⟶ F)
    (h : f.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app _ (1 : A)) =
      g.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app _ (1 : A))) : f = g := by
  apply ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv
      (ModuleCat.of A A) F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

private theorem endpointUnitInsertion_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    b.unitInsertion = a.unitInsertion ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map e.unitInsertion ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (ordinaryFiniteConstant C T) := by
  apply constantSheaf_ext_top T
  change b.unitInsertion.hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app _ (1 : A)) =
    e.unitInsertion.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (a.unitInsertion.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app _ (1 : A)))
  rw [a.unit_normalization, e.unit_normalization, b.unit_normalization]
  rfl

private theorem endpointLineInsertion_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    b.lineInsertion = a.lineInsertion ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map e.lineInsertion ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (Scheme.finiteEtaleTateLine T N C hC) := by
  apply lineMap_ext
  intro W z
  change b.lineInsertion.hom.app W
      (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
    e.lineInsertion.hom.app W
      (a.lineInsertion.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z))
  rw [a.line_normalization, e.line_normalization, b.line_normalization]
  rfl

private theorem endpointUnitIso_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    (scalarExtension ψ T).map a.unitIso.hom ≫ e.unitIso.hom =
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (ordinaryFiniteUnit A T) ≫ b.unitIso.hom := by
  rw [a.unit_derived, e.unit_derived, b.unit_derived]
  unfold p1KummerDerivedInsertion
  exact SheafExactDegreeZero.scalarAdjointInsertion_comp T.smallEtaleTopology φ ψ
    a.unitInsertion e.unitInsertion b.unitInsertion (endpointUnitInsertion_comp a b e)

private theorem endpointLineIso_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    (scalarExtension ψ T).map a.lineIso.hom ≫ e.lineIso.hom =
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (ordinaryFiniteLine A N hA T) ≫ b.lineIso.hom := by
  rw [a.line_derived, e.line_derived, b.line_derived]
  unfold p1KummerDerivedInsertion
  exact SheafExactDegreeZero.scalarAdjointInsertion_comp T.smallEtaleTopology φ ψ
    a.lineInsertion e.lineInsertion b.lineInsertion (endpointLineInsertion_comp a b e)

private theorem endpointShiftedLineIso_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    (scalarExtension ψ T).map a.shiftedLineIso.hom ≫ e.shiftedLineIso.hom =
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫ b.shiftedLineIso.hom := by
  have hs : NatTrans.CommShift
      (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology (f := φ) (g := ψ) rfl).hom
      ℤ := by
    dsimp only [Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := hs
  exact shifted_comp
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (ψ.comp φ)))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl)
    a.lineIso.hom e.lineIso.hom b.lineIso.hom (endpointLineIso_comp a b e) (2 : ℤ)

/-- Normalized endpoint maps identify the specified scalar-composition components.
Source: Stacks 0D6D and the adjunction normalization of the endpoint record
(blueprint: lem-sp-p1-kummer-scalar-endpoint-composition).

Proof: the ordinary constant insertions compose, since both maps send a to psi(phi(a));
the constant-sheaf adjunction detects equality at one. The Tate insertions compose,
since both send a tensor z to psi(phi(a)) tensor z, and the tensor/sheafification
universal property detects equality on these generators. Compatibility of the exact
single-functor comparison with composition gives the same equations for their derived
units. Taking adjoints identifies their composites with the canonical left-adjoint
composition comparison, which is pbcFixedScalarExtensionComp. This proves the unit
and unshifted line equations. Restriction of scalars commutes with shifts, as does its
composition comparison. Its mate therefore commutes with the left-adjoint shift
comparisons. Shift the line equation by two and apply that compatibility to obtain
the displayed shifted equation. No hypothesis about a Chern class is used. -/
theorem p1KummerScalarEndpointComposition
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}} {N : ℕ}
    {hA : (N : A) = 0} {hB : (N : B) = 0} {hC : (N : C) = 0}
    (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T) :
    (scalarExtension ψ T).map a.unitIso.hom ≫ e.unitIso.hom =
        (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
          φ ψ (ψ.comp φ) rfl).hom.app (ordinaryFiniteUnit A T) ≫ b.unitIso.hom ∧
      (scalarExtension ψ T).map a.shiftedLineIso.hom ≫ e.shiftedLineIso.hom =
        (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
          φ ψ (ψ.comp φ) rfl).hom.app
            ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫ b.shiftedLineIso.hom := by
  exact ⟨endpointUnitIso_comp a b e, endpointShiftedLineIso_comp a b e⟩

end AlgebraicGeometry.Etale
