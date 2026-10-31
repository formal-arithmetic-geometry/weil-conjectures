/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.AlgebraicGeometry.FiniteCondensedConstructibilityComparison
import WeilConjectures.SixFunctors.FiniteDiscreteCoefficientTriangulated
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-! # Bounded constructibility of the Fourier–Deligne transform

Source: current Weil blueprint, sec-fourier-transform/sk-thm-inversion/
thm-fd-transform-well-defined.md (blueprint: thm-fd-transform-well-defined).

The three statements give finite etale, finite admissible pro-etale and ell-adic
preservation, using the same prime-field structure also on the empty product.
The exactness clause is expressed
using ambient distinguished triangles with bounded constructible vertices, so it does not
assume an extra triangulated structure on the full subcategories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem fourierConstructibleComapIff {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    IsConstructibleModuleObject S ((Mod.comap φ).obj M) ↔
      IsConstructibleModuleObject R M := by
  constructor
  · intro h
    exact constructible_of_iso ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm
      (constructible_comap _ h)
  · exact constructible_comap φ

private theorem fourierBoundedComapIff {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible R K := by
  rw [mem_boundedConstructible_iff, mem_boundedConstructible_iff]
  apply and_congr
  · constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (h i hi)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)⟩
  · apply forall_congr'
    intro n
    let e := ((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K
    exact ⟨fun h ↦ (fourierConstructibleComapIff φ _).1 (constructible_of_iso e.symm h),
      fun h ↦ constructible_of_iso e ((fourierConstructibleComapIff φ _).2 h)⟩

private theorem fourierTriangulatedOfIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    [(boundedConstructible (condensedRingObj Λ' X)).IsTriangulated] :
    (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
  let T := (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv.hom X)).mapDerivedCategory
  have heq : boundedConstructible (condensedRingObj Λ X) =
      (boundedConstructible (condensedRingObj Λ' X)).inverseImage T := by
    funext K
    exact propext (fourierBoundedComapIff (coefficientMap e.inv.hom X) K).symm
  rw [heq]
  infer_instance

private theorem fourierProperOfIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, boundedConstructible (condensedRingObj Λ' X) K →
      boundedConstructible (condensedRingObj Λ' Y) ((lowerStar Λ' f).rightDerivedFunctor.obj K))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ Y) ((lowerStar Λ f).rightDerivedFunctor.obj K) := by
  let φ := e.inv.hom
  have (Z : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (coefficientMap φ Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  apply (fourierBoundedComapIff (coefficientMap φ Y) _).mp
  exact (boundedConstructible _).prop_of_iso
    ((derivedComapLowerStarIso φ f).app K).symm
    (h _ ((fourierBoundedComapIff (coefficientMap φ X) K).mpr hK))

/-- Finite etale coefficients: the transform preserves every bounded
constructible object, and restricts as a functor with the same ambient objects and morphisms.
Only the target is required finite type over a field, and only p2 finite type/compactifiable.
Source: current blueprint, thm-fd-transform-well-defined.md, clause (1)
(blueprint: thm-fd-transform-well-defined).

Proof: the Artin--Schreier kernel is tensor-invertible, hence flat. Exact pullback
preserves bounded constructibility, and tensor with this flat constructible sheaf does
so without a Tor-amplitude hypothesis on the input. In the chosen compactification,
extension by zero preserves bounded constructibility. If the product is empty the
result is zero. Otherwise its map to Spec k shows that the coefficient exponent is
invertible in k; the existing proper-pushforward finiteness theorem applies. The
compactification is Noetherian by finite type over k, and its open subscheme is
Noetherian too. Shift the resulting bounded interval and lift the ambient functor
to the full bounded constructible subcategories. -/
theorem primeFieldFourierTransform_boundedConstructible_finite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (p : ℕ) [Fact p.Prime] [Invertible (p : A)]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    [HasInvertibleExponent A S]
    [(pullback π π').Over (Spec (.of (ULift.{u} (ZMod p))))]
    [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
    (c : Compactification (pullback.snd π π'))
    (k : Type u) [Field k] (aV' : V' ⟶ Spec (.of k))
    [LocallyOfFiniteType aV'] [QuasiCompact aV']
    (Ψ : AddChar (ZMod p) A) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    (∀ K, Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V K →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V'
        ((Etale.primeFieldFourierTransform A p π π' Ψ b c r).obj K)) ∧
    ∃ F : Etale.DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} A) V ⥤
        Etale.DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} A) V',
      Nonempty (F ⋙ Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} A) V' ≅
        Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} A) V ⋙
          Etale.primeFieldFourierTransform A p π π' Ψ b c r) := by
  classical
  let L := Etale.artinSchreierSheafOf (pullback π π')
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
  have hL : ObjectProperty.flat L := by
    obtain ⟨e⟩ := Etale.nonempty_iso_artinSchreierSheafOf_neg (pullback π π')
      (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
    exact ObjectProperty.flat_of_tensorIso e
  have hpres : ∀ K,
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V K →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V'
        ((Etale.primeFieldFourierTransform A p π π' Ψ b c r).obj K) := by
    intro K hK
    have h₁ := hK.mapDerivedCategory_upperStar (pullback.fst π π')
    have h₂ := Etale.boundedConstructible_tensor A _ h₁
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj L 0)
      ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_obj_of_flat A L hL⟩
    have h₃ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V'
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj
          ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) (pullback π π')
            ((DerivedCategory.singleFunctor _ 0).obj L)).obj
            ((Etale.upperStar (ModuleCat.{u + 1} A)
              (pullback.fst π π')).mapDerivedCategory.obj K))) := by
      cases isEmpty_or_nonempty (pullback π π' : Scheme.{u}) with
      | inl hW =>
        exact Etale.boundedConstructible_of_isZero A
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} A) c).map_isZero
              (Etale.isZero_derivedCategory_of_isEmpty _ (pullback π π') _))
      | inr hW =>
        have : HasInvertibleExponent A (pullback π π') :=
          HasInvertibleExponent.of_hom (pullback.fst π π' ≫ π)
        have : HasInvertibleExponent A (Spec (.of k)) :=
          HasInvertibleExponent.of_hom_of_nonempty (Λ := A) (pullback.snd π π' ≫ aV')
        have : HasInvertibleExponent A c.Z :=
          HasInvertibleExponent.of_hom (c.g ≫ aV')
        have : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace aV'
        have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
        have : IsNoetherian c.Z :=
          { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aV') }
        have : TopologicalSpace.NoetherianSpace (pullback π π' : Scheme.{u}) :=
          c.i.isOpenEmbedding.isInducing.noetherianSpace
        exact Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent A
          c.g (c.g ≫ aV') aV' rfl _
          (Etale.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek A c.i h₂)
    exact (Etale.DerivedCategory.boundedConstructible _ V').le_shift r _ h₃
  refine ⟨hpres, ?_⟩
  let F := Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} A) V ⋙
    Etale.primeFieldFourierTransform A p π π' Ψ b c r
  exact ⟨(Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) V').lift F
    (fun K ↦ hpres K.obj K.property), ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩

/-- Finite admissible coefficients: the pro-étale transform preserves every bounded
constructible object, and restricts as a functor with the same ambient objects and morphisms.
Only the target is required finite type over a field, and only p2 finite type/compactifiable.
Source: current blueprint, thm-fd-transform-well-defined.md, clause (1)
(blueprint: thm-fd-transform-well-defined).

Proof: the rank-one local trivializations of the condensed kernel make it locally
free. Pullback and tensor with its degree-zero complex preserve bounded
constructibility, and exact extension by zero does too, by its cohomology comparison.
The finite coefficient equivalence carries this intermediate object to an ordinary
pro-etale bounded constructible complex. For a nonempty product, the coefficient
exponent descends to an invertible element of k. Apply finite-coefficient proper
pushforward and its commutation with the coefficient equivalence, then reflect
bounded constructibility using the finite condensed comparison theorem. The empty
product gives zero. Shift and lift to the full subcategories. -/
theorem condensedFourierTransform_boundedConstructible_finite
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : IsAdmissibleCoefficient (Profinite.continuousMapRingObj.{u} A))
    (p : ℕ) [Fact p.Prime] [Invertible (p : A)]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    [HasInvertibleExponent A S]
    [(pullback π π').Over (Spec (.of (ULift.{u} (ZMod p))))]
    [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
    (c : Compactification (pullback.snd π π'))
    (k : Type u) [Field k] (aV' : V' ⟶ Spec (.of k))
    [LocallyOfFiniteType aV'] [QuasiCompact aV']
    (Ψ : AddChar (ZMod p) (MonObj.Γ (Profinite.continuousMapRingObj.{u} A)))
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    (∀ K, boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V) K →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V')
        ((primeFieldCondensedFourierTransform (Profinite.continuousMapRingObj.{u} A)
          p π π' Ψ b c r).obj K)) ∧
    ∃ F : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V) ⥤
        BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V'),
      Nonempty (F ⋙ (boundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V')).ι ≅
        (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} A) V)).ι ⋙
          primeFieldCondensedFourierTransform (Profinite.continuousMapRingObj.{u} A)
            p π π' Ψ b c r) := by
  classical
  let Λ := Profinite.continuousMapRingObj.{u} A
  have hp : IsUnit (p : MonObj.Γ Λ) := by
    simpa only [map_natCast] using
      (isUnit_of_invertible (p : A)).map (Profinite.continuousMapConstRingHom.{u} A)
  have : IsNoetherian V' := isNoetherian_of_locallyOfFiniteType aV'
  have : IsNoetherian c.Z :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aV')
      __ := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aV') }
  have : TopologicalSpace.NoetherianSpace (pullback π π' : Scheme.{u}) :=
    c.i.isOpenEmbedding.isInducing.noetherianSpace
  let L := condensedFourierKernel Λ (ULift.{u} (ZMod p)) π π'
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
  have hL : IsLocallyFree (condensedRingObj Λ (pullback π π')) L := by
    obtain ⟨U, hU⟩ := (Etale.prop_kernel_lisse.2.2.1 Λ p hp hA
      (pullback π π') Ψ Ψ b).2.1
    apply (isLocallyFree_iff L).2
    refine ⟨U, fun i ↦ ⟨1, ⟨?_⟩⟩⟩
    exact (hU i).some ≪≫
      (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj Λ (U.X i)))).symm
  have hpres : ∀ K, boundedConstructible (condensedRingObj Λ V) K →
      boundedConstructible (condensedRingObj Λ V')
        ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).obj K) := by
    intro K hK
    have h₁ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ (pullback.fst π π') K hK
    have h₂ : boundedConstructible (condensedRingObj Λ (pullback π π'))
        ((CategoryTheory.MonoidalCategory.tensorRight
          ((DerivedCategory.singleFunctor _ 0).obj L)).obj
          ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K)) := by
      obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (pullback π π')) Ab.{u + 1})
          (condensedRingObj Λ (pullback π π')))
      exact (boundedConstructible _).prop_of_iso (β_ _ _)
        (boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree hL h₁)
    have hj : boundedConstructible (condensedRingObj Λ c.Z)
        ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj
          ((CategoryTheory.MonoidalCategory.tensorRight
            ((DerivedCategory.singleFunctor _ 0).obj L)).obj
            ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K))) := by
      obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ _).1 h₂
      refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
      · exact ((openImmersionLowerShriek Λ c.i).map_isZero (hab i hi)).of_iso
          ((Functor.mapDerivedCategoryHomologyFunctorIso _ i).app _).symm
      · exact (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ c.i _ (hc n)).of_iso
          ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app _)
    have h₃ : boundedConstructible (condensedRingObj Λ V')
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((CategoryTheory.MonoidalCategory.tensorRight
            ((DerivedCategory.singleFunctor _ 0).obj L)).obj
            ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K))) := by
      cases isEmpty_or_nonempty (pullback π π' : Scheme.{u}) with
      | inl hW =>
        exact boundedConstructible_of_isZero Λ
          ((rightDerivedLowerShriekOfCompactification Λ c).map_isZero
            (isZero_derivedCategory_of_isEmpty' Λ _))
      | inr hW =>
        have : HasInvertibleExponent A (pullback π π') :=
          HasInvertibleExponent.of_hom (pullback.fst π π' ≫ π)
        have : HasInvertibleExponent A (Spec (.of k)) :=
          HasInvertibleExponent.of_hom_of_nonempty
            (Λ := A) (pullback.snd π π' ≫ aV')
        obtain ⟨N, _, hNA, hNu⟩ :=
          HasInvertibleExponent.exists_isUnit_natCast (Λ := A) (X := Spec (.of k))
        have hNk : (N : k) ≠ 0 := by
          have h := hNu.map (Scheme.ΓSpecIso (.of k)).hom.hom
          simpa only [map_natCast] using h.ne_zero
        have hN : (N : ULift.{u + 1} A) = 0 := by
          apply ULift.ext
          exact hNA
        have hcomp := Functor.rightDerivedFunctorCommIso
          (lowerStarFiniteCoefficientModEquivalenceIso c.g A)
        apply (boundedConstructible_finiteCoefficientDerivedEquivalence_iff A V' _).mpr
        apply (ProEtale.DerivedCategory.boundedConstructible _ V').prop_of_iso
          (hcomp.app _).symm
        exact ProEtale.boundedConstructible_rightDerivedLowerStar
          (ULift.{u + 1} A) N hNk (fun M ↦ by
            ext x
            change N • x = 0
            rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} A), hN, zero_smul])
          aV' c.g (isEtaleOrigin_of_isConstructible A hj)
    simpa only [primeFieldCondensedFourierTransform, condensedFourierTransform,
      Functor.comp_obj, ObjectProperty.shift, L] using
      (boundedConstructible _).le_shift r _ h₃
  refine ⟨hpres, ?_⟩
  let F := (boundedConstructible (condensedRingObj Λ V)).ι ⋙
    primeFieldCondensedFourierTransform Λ p π π' Ψ b c r
  exact ⟨(boundedConstructible (condensedRingObj Λ V')).lift F
    (fun K ↦ hpres K.obj K.property), ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩


set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- Allow elaboration of the full coefficient-family and distinguished-triangle signature.
/-- Ell-adic coefficients: bounded constructible objects are preserved and the transform
restricts to an exact functor. The natural shift comparison and distinguished-triangle clause
express exactness on the inherited full subcategories. Coefficients are the actual condensed
rings (up to ring isomorphism), with the finite-subextension convention for Qbar.
Source: current blueprint, thm-fd-transform-well-defined.md, clause (2)
(blueprint: thm-fd-transform-well-defined).

Proof: use the rank-one trivializations, exact pullback, tensor by a locally free
sheaf in degree zero, and exact extension by zero. For a nonempty product, its
prime-field and k-structures imply char(k)=p, so the coefficient prime is invertible.
The three existing proper-pushforward finiteness theorems apply to the Noetherian
target; restriction of scalars along the given coefficient isomorphism transports
both bounded constructibility and proper pushforward. The empty product gives zero.
Shift and lift to the full subcategories. Finally exact pullback agrees with its
termwise derived functor, while tensor, open extension, proper derived pushforward
and shift are triangulated. Their composite supplies the shift comparison and sends
distinguished triangles to distinguished triangles. -/
theorem condensedFourierTransform_boundedConstructible_ellAdic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (p : ℕ) [Fact p.Prime]
    (hΛ : ∃ (l : ℕ) (_hl : Fact l.Prime), l ≠ p ∧ (
      (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} l))))
    (hp : IsUnit (p : MonObj.Γ Λ))
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    {S V V' : Scheme.{u}} [S.Over (Spec (.of k))]
    [V.Over (Spec (.of k))] [V'.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (V' ↘ Spec (.of k))] [QuasiCompact (V' ↘ Spec (.of k))]
    (π : V ⟶ S) (π' : V' ⟶ S)
    [(pullback π π').Over (Spec (.of (ULift.{u} (ZMod p))))]
    [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
    (c : Compactification (pullback.snd π π'))
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    (∀ K, boundedConstructible (condensedRingObj Λ V) K →
      boundedConstructible (condensedRingObj Λ V')
        ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).obj K)) ∧
    (∃ F : BoundedConstructible (condensedRingObj Λ V) ⥤
        BoundedConstructible (condensedRingObj Λ V'),
      Nonempty (F ⋙ (boundedConstructible (condensedRingObj Λ V')).ι ≅
        (boundedConstructible (condensedRingObj Λ V)).ι ⋙
          primeFieldCondensedFourierTransform Λ p π π' Ψ b c r)) ∧
    ∃ e : primeFieldCondensedFourierTransform Λ p π π' Ψ b c r ⋙ shiftFunctor _ (1 : ℤ) ≅
        shiftFunctor _ (1 : ℤ) ⋙ primeFieldCondensedFourierTransform Λ p π π' Ψ b c r,
      ∀ T : Triangle (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))),
        T ∈ distTriang _ →
        boundedConstructible (condensedRingObj Λ V) T.obj₁ →
        boundedConstructible (condensedRingObj Λ V) T.obj₂ →
        boundedConstructible (condensedRingObj Λ V) T.obj₃ →
        Triangle.mk
          ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).map T.mor₁)
          ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).map T.mor₂)
          ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).map T.mor₃ ≫
            e.inv.app T.obj₁) ∈ distTriang _ := by
  classical
  have _hfield := hk
  obtain ⟨l, hl, hneq, hCoeff⟩ := hΛ
  have : Fact l.Prime := hl
  have had : IsAdmissibleCoefficient Λ :=
    ⟨l, hl, Or.inr (Or.inr (Or.inr hCoeff))⟩
  have htri (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
      (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
    rcases hCoeff with ⟨E, ⟨e⟩⟩ | ⟨E, ⟨e⟩⟩ | hq
    · exact fourierTriangulatedOfIso e X
    · exact fourierTriangulatedOfIso e X
    · obtain ⟨e⟩ := hq
      exact fourierTriangulatedOfIso e X
  have hproper {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
      (f : X ⟶ Y) [IsProper f] (hchar : ringChar k ≠ l)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) (hK : boundedConstructible (condensedRingObj Λ X) K) :
      boundedConstructible (condensedRingObj Λ Y) ((lowerStar Λ f).rightDerivedFunctor.obj K) := by
    have : Fact (ringChar k ≠ l) := ⟨hchar⟩
    rcases hCoeff with ⟨E, ⟨e⟩⟩ | ⟨E, ⟨e⟩⟩ | hq
    · exact fourierProperOfIso e f
        (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj
          l E aY f K hK) K hK
    · exact fourierProperOfIso e f
        (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj
          l E aY f K hK) K hK
    · obtain ⟨e⟩ := hq
      exact fourierProperOfIso e f
        (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj
          l aY f K hK) K hK
  have : IsNoetherian V' := isNoetherian_of_locallyOfFiniteType (V' ↘ Spec (.of k))
  have : IsNoetherian c.Z :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ (V' ↘ Spec (.of k)))
      __ := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ (V' ↘ Spec (.of k))) }
  have : TopologicalSpace.NoetherianSpace (pullback π π' : Scheme.{u}) :=
    c.i.isOpenEmbedding.isInducing.noetherianSpace
  have := htri (pullback π π')
  have := htri V'
  let L := condensedFourierKernel Λ (ULift.{u} (ZMod p)) π π'
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
  have hL : IsLocallyFree (condensedRingObj Λ (pullback π π')) L := by
    obtain ⟨U, hU⟩ := (Etale.prop_kernel_lisse.2.2.1 Λ p hp had
      (pullback π π') Ψ Ψ b).2.1
    apply (isLocallyFree_iff L).2
    refine ⟨U, fun i ↦ ⟨1, ⟨?_⟩⟩⟩
    exact (hU i).some ≪≫
      (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj Λ (U.X i)))).symm
  have hpres : ∀ K, boundedConstructible (condensedRingObj Λ V) K →
      boundedConstructible (condensedRingObj Λ V')
        ((primeFieldCondensedFourierTransform Λ p π π' Ψ b c r).obj K) := by
    intro K hK
    have h₁ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ (pullback.fst π π') K hK
    have h₂ : boundedConstructible (condensedRingObj Λ (pullback π π'))
        ((CategoryTheory.MonoidalCategory.tensorRight
          ((DerivedCategory.singleFunctor _ 0).obj L)).obj
          ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K)) := by
      obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (pullback π π')) Ab.{u + 1})
          (condensedRingObj Λ (pullback π π')))
      exact (boundedConstructible _).prop_of_iso (β_ _ _)
        (boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree hL h₁)
    have hj : boundedConstructible (condensedRingObj Λ c.Z)
        ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj
          ((CategoryTheory.MonoidalCategory.tensorRight
            ((DerivedCategory.singleFunctor _ 0).obj L)).obj
            ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K))) := by
      obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ _).1 h₂
      refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
      · exact ((openImmersionLowerShriek Λ c.i).map_isZero (hab i hi)).of_iso
          ((Functor.mapDerivedCategoryHomologyFunctorIso _ i).app _).symm
      · exact (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ c.i _ (hc n)).of_iso
          ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app _)
    have h₃ : boundedConstructible (condensedRingObj Λ V')
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((CategoryTheory.MonoidalCategory.tensorRight
            ((DerivedCategory.singleFunctor _ 0).obj L)).obj
            ((upperStar Λ (pullback.fst π π')).leftDerivedFunctor.obj K))) := by
      cases isEmpty_or_nonempty (pullback π π' : Scheme.{u}) with
      | inl hW =>
        exact boundedConstructible_of_isZero Λ
          ((rightDerivedLowerShriekOfCompactification Λ c).map_isZero
            (isZero_derivedCategory_of_isEmpty' Λ _))
      | inr hW =>
        have hchar : ringChar k = p := by
          let W : Scheme.{u} := pullback π π'
          let aW : W ⟶ Spec (.of k) := pullback.snd π π' ≫ (V' ↘ Spec (.of k))
          let φ : k →+* Γ(W, ⊤) := aW.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
          have hpW : (p : Γ(W, ⊤)) = 0 := by
            let ap := W ↘ Spec (.of (ULift.{u} (ZMod p)))
            rw [← map_natCast ap.appTop.hom,
              ← map_natCast (Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv.hom]
            simp
          apply CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime)
          apply φ.injective
          simpa using hpW
        exact hproper (V' ↘ Spec (.of k)) c.g (by simpa [hchar] using hneq.symm) _ hj
    simpa only [primeFieldCondensedFourierTransform, condensedFourierTransform,
      Functor.comp_obj, ObjectProperty.shift, L] using
      (boundedConstructible _).le_shift r _ h₃
  refine ⟨hpres, ?_, ?_⟩
  · let F := (boundedConstructible (condensedRingObj Λ V)).ι ⋙
      primeFieldCondensedFourierTransform Λ p π π' Ψ b c r
    exact ⟨(boundedConstructible (condensedRingObj Λ V')).lift F
      (fun K ↦ hpres K.obj K.property), ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩
  · let P := upperStar Λ (pullback.fst π π')
    let eP := leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst π π')
    -- Keep this local instance reducible for the transported shift compatibility.
    let : P.leftDerivedFunctor.CommShift ℤ := Functor.CommShift.ofIso eP.symm ℤ
    have := Functor.CommShift.ofIso_compatibility eP.symm ℤ
    have : P.leftDerivedFunctor.IsTriangulated := Functor.isTriangulated_of_iso eP.symm
    let F := primeFieldCondensedFourierTransform Λ p π π' Ψ b c r
    let : F.CommShift ℤ := by
      unfold F primeFieldCondensedFourierTransform condensedFourierTransform
      infer_instance
    have : F.IsTriangulated := by
      unfold F primeFieldCondensedFourierTransform condensedFourierTransform
      infer_instance
    refine ⟨(F.commShiftIso (1 : ℤ)).symm, fun T hT _ _ _ ↦ ?_⟩
    exact F.map_distinguished T hT


end AlgebraicGeometry.ProEtale.CondensedRing
