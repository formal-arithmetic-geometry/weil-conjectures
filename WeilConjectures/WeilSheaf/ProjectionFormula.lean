/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersionRestriction
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.WeilSheaf.UpperStarDual
public import WeilConjectures.WeilSheaf.UpperStarTensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseTensor
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# The projection formula for the compact-support direct image of Weil complexes

For a separated quasi-compact morphism `f : X ⟶ Y` locally of finite type of `k₀`-schemes of finite
type and a lisse Weil sheaf `G` on `Y`, `Rf₀!(f^* G ⊗ K) ≅ G ⊗ Rf₀! K` naturally in the Weil
complex `K` (`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse`,
blueprint `prop-weil-operations`).

The tensor product `G ⊗ -` with a lisse Weil sheaf is the internal hom `[G^∨, -]` out of its dual.
Write `f = g ∘ i` for the chosen compactification, `i` an open immersion and `g` proper, so that
`Rf₀! = Rg_* ∘ i_!`. Then:

- for the direct image, `g_*[g^* A, -] ≅ [A, g_* -]` for every pro-étale Weil sheaf `A`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso`), and `[g^* A, -]` is exact
  and preserves K-injective complexes when `A` is lisse, its left adjoint `- ⊗ g^* A` being exact;
  so `Rg_* [g^* A, -] ≅ [A, -] Rg_*`;
- for the extension by zero, `i_! [i^* B, -] ≅ [B, i_! -]` for lisse `B`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompIhomFunctorIso`);
- the pullback of the dual of a lisse sheaf is the dual of the pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product with a pro-étale Weil sheaf whose underlying sheaf is lisse is exact. -/
instance preservesFiniteLimits_tensorFunctor (C : ProEtaleWeilSheaf k₀ l X)
    [Fact (IsAdicLisseSheaf C.carrier)] :
    PreservesFiniteLimits (ProEtaleWeilSheaf.tensorFunctor k₀ l X C) := by
  have : (ProEtaleWeilSheaf.tensorFunctor k₀ l X C).Additive :=
    (tensorIhomAdjunction k₀ l X C).left_adjoint_additive
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.tensorFunctor k₀ l X C) := by
    have := (tensorIhomAdjunction k₀ l X C).leftAdjoint_preservesColimits.{0, 0}
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  refine ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 inferInstance
    S hS).1, ?_⟩
  have := hS.mono_f
  have : (Mod.tensorLeft C.carrier).PreservesMonomorphisms :=
    IsAdicLisseSheaf.preservesMonomorphisms_tensorLeft (Fact.out)
  have : Mono ((IsoAlgebra.forget _).map S.f) := inferInstance
  have : Mono ((IsoAlgebra.forget _).map ((ProEtaleWeilSheaf.tensorFunctor k₀ l X C).map S.f)) :=
    (Mod.tensorLeft C.carrier).map_mono ((IsoAlgebra.forget _).map S.f)
  exact (IsoAlgebra.forget _).mono_of_mono_map this

instance (C : ProEtaleWeilSheaf k₀ l X) : (ProEtaleWeilSheaf.tensorFunctor k₀ l X C).Additive :=
  (tensorIhomAdjunction k₀ l X C).left_adjoint_additive

instance (C : ProEtaleWeilSheaf k₀ l X) :
    PreservesFiniteColimits (ProEtaleWeilSheaf.tensorFunctor k₀ l X C) := by
  have := (tensorIhomAdjunction k₀ l X C).leftAdjoint_preservesColimits.{0, 0}
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The internal hom out of a pro-étale Weil sheaf whose underlying sheaf is lisse preserves
K-injective complexes: it is right adjoint to the exact tensor product. -/
instance preservesKInjectiveComplexes_ihomFunctor (C : ProEtaleWeilSheaf k₀ l X)
    [Fact (IsAdicLisseSheaf C.carrier)] :
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X C).PreservesKInjectiveComplexes :=
  have : (ProEtaleWeilSheaf.tensorFunctor k₀ l X C).PreservesHomology := by
    have h := (Functor.exact_tfae (ProEtaleWeilSheaf.tensorFunctor k₀ l X C)).out 3 2
    exact h.1 ⟨inferInstance, inferInstance⟩
  (tensorIhomAdjunction k₀ l X C).preservesKInjectiveComplexes

end Lisse

section Derived

variable {X Z Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  (i : X ⟶ Z) [IsOpenImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

section ExtensionByZero

variable (B : ProEtaleWeilSheaf k₀ l Z)

set_option hygiene false in
local notation "ib" => Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k₀)))

/-- The comparison `[B, i_! F] ⟶ [B, i_* F]` induced by `i_! ⟶ i_*`. -/
noncomputable abbrev ihomExtensionByZeroToLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).obj ((ProEtaleWeilSheaf.extensionByZero k₀ l i).obj F) ⟶
      (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).obj ((ProEtaleWeilSheaf.lowerStar k₀ l i).obj F) :=
  (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).map
    ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app F)

/-- The comparison `i_! [i^* B, F] ⟶ i_* [i^* B, F] ≅ [B, i_* F]`. -/
noncomputable abbrev extensionByZeroIhomToIhomLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.extensionByZero k₀ l i).obj
        ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l i).obj B)).obj F) ⟶
      (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).obj ((ProEtaleWeilSheaf.lowerStar k₀ l i).obj F) :=
  (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app _ ≫
    (lowerStarCompIhomFunctorIso k₀ l i B).inv.app F

lemma mono_extensionByZeroToLowerStar_app (F : ProEtaleWeilSheaf k₀ l X) :
    Mono ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app F) :=
  (IsoAlgebra.forget _).mono_of_mono_map (inferInstanceAs
    (Mono ((adicOpenImmersionLowerShriekToLowerStar l ib).app F.carrier)))

instance mono_ihomExtensionByZeroToLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    Mono (ihomExtensionByZeroToLowerStar i B F) :=
  have := mono_extensionByZeroToLowerStar_app i F
  (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).map_mono _

instance mono_extensionByZeroIhomToIhomLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    Mono (extensionByZeroIhomToIhomLowerStar i B F) :=
  have := mono_extensionByZeroToLowerStar_app i
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l i).obj B)).obj F)
  mono_comp _ _

instance isIso_upperStar_map_ihomExtensionByZeroToLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    IsIso ((ProEtaleWeilSheaf.upperStar k₀ l i).map (ihomExtensionByZeroToLowerStar i B F)) := by
  have h1 : IsIso ((ib)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l ib).app
      F.carrier)) :=
    inferInstanceAs (IsIso ((IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.upperStar k₀ l i).map
        ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app F))))
  have h2 : IsIso ((ib)^*ᵃ[l].map ((AdicSheaf.ihom B.carrier).map
      ((adicOpenImmersionLowerShriekToLowerStar l ib).app F.carrier))) := by
    have := NatIso.naturality_2 (adicUpperStarIhomIso l ib B.carrier)
      ((adicOpenImmersionLowerShriekToLowerStar l ib).app F.carrier)
    simp only [Functor.comp_map] at this
    rw [← this]
    infer_instance
  have : IsIso ((IsoAlgebra.forget _).map ((ProEtaleWeilSheaf.upperStar k₀ l i).map
      (ihomExtensionByZeroToLowerStar i B F))) := h2
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

instance isIso_upperStar_map_extensionByZeroIhomToIhomLowerStar (F : ProEtaleWeilSheaf k₀ l X) :
    IsIso ((ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhomLowerStar i B F)) := by
  simp only [extensionByZeroIhomToIhomLowerStar, Functor.map_comp]
  infer_instance

lemma extensionByZeroIhomToIhomLowerStar_comp_cokernel_π (F : ProEtaleWeilSheaf k₀ l X) :
    extensionByZeroIhomToIhomLowerStar i B F ≫
      cokernel.π (ihomExtensionByZeroToLowerStar i B F) = 0 := by
  set Fg := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  have hZ : IsZero ((ib)^*ᵃ[l].obj (Fg.obj (cokernel (ihomExtensionByZeroToLowerStar i B F)))) := by
    have : IsIso ((ib)^*ᵃ[l].map (Fg.map (ihomExtensionByZeroToLowerStar i B F))) :=
      inferInstanceAs (IsIso ((IsoAlgebra.forget _).map
        ((ProEtaleWeilSheaf.upperStar k₀ l i).map (ihomExtensionByZeroToLowerStar i B F))))
    have : Epi ((ib)^*ᵃ[l].map (Fg.map (ihomExtensionByZeroToLowerStar i B F))) :=
      IsIso.epi_of_iso _
    exact (isZero_cokernel_of_epi _).of_iso ((ib)^*ᵃ[l].mapIso
      (PreservesCokernel.iso Fg (ihomExtensionByZeroToLowerStar i B F)) ≪≫
        PreservesCokernel.iso (ib)^*ᵃ[l] _)
  apply Fg.map_injective
  rw [Functor.map_comp, Functor.map_zero]
  apply ((adicOpenImmersionLowerShriekAdjunction l ib).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact hZ.eq_of_tgt _ _

/-- The comparison `i_! [i^* B, F] ⟶ [B, i_! F]`, lifting `i_! [i^* B, F] ⟶ [B, i_* F]` along
the monomorphism `[B, i_! F] ⟶ [B, i_* F]`. -/
noncomputable def extensionByZeroIhomToIhom (F : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.extensionByZero k₀ l i).obj
        ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l i).obj B)).obj F) ⟶
      (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).obj ((ProEtaleWeilSheaf.extensionByZero k₀ l i).obj F) :=
  Abelian.monoLift _ _ (extensionByZeroIhomToIhomLowerStar_comp_cokernel_π i B F)

@[reassoc (attr := simp)]
lemma extensionByZeroIhomToIhom_comp (F : ProEtaleWeilSheaf k₀ l X) :
    extensionByZeroIhomToIhom i B F ≫ ihomExtensionByZeroToLowerStar i B F =
      extensionByZeroIhomToIhomLowerStar i B F :=
  Abelian.monoLift_comp _ _ _

lemma mono_extensionByZeroIhomToIhom (F : ProEtaleWeilSheaf k₀ l X) :
    Mono (extensionByZeroIhomToIhom i B F) :=
  mono_of_mono_fac (extensionByZeroIhomToIhom_comp i B F)

lemma isIso_upperStar_map_extensionByZeroIhomToIhom (F : ProEtaleWeilSheaf k₀ l X) :
    IsIso ((ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhom i B F)) := by
  have hc : (ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhom i B F) ≫
      (ProEtaleWeilSheaf.upperStar k₀ l i).map (ihomExtensionByZeroToLowerStar i B F) =
      (ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhomLowerStar i B F) := by
    rw [← Functor.map_comp, extensionByZeroIhomToIhom_comp]
  have : IsIso ((ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhom i B F) ≫
      (ProEtaleWeilSheaf.upperStar k₀ l i).map (ihomExtensionByZeroToLowerStar i B F)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ProEtaleWeilSheaf.upperStar k₀ l i).map (ihomExtensionByZeroToLowerStar i B F))

lemma isIso_extensionByZeroIhomToIhom [QuasiCompact i] (hB : IsAdicLisseSheaf B.carrier)
    (F : ProEtaleWeilSheaf k₀ l X) : IsIso (extensionByZeroIhomToIhom i B F) := by
  set Fg := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  set k := (Scheme.Hom.opensRange ib).closedComplement
  have hij : IsCompl (Set.range k.base) (Set.range (ib).base) := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Hom.coe_opensRange]
    exact isCompl_compl.symm
  have hdisj : Set.range (ib).base ∩ Set.range k.base = ∅ :=
    Set.disjoint_iff_inter_eq_empty.1 hij.symm.disjoint
  have := mono_extensionByZeroIhomToIhom i B F
  have : Epi (extensionByZeroIhomToIhom i B F) := by
    refine Preadditive.epi_of_isZero_cokernel _ ((ProEtaleWeilSheaf.isZero_iff _).2 ?_)
    have hCi : IsZero ((ib)^*ᵃ[l].obj (Fg.obj (cokernel (extensionByZeroIhomToIhom i B F)))) := by
      have := isIso_upperStar_map_extensionByZeroIhomToIhom i B F
      have : IsIso ((ib)^*ᵃ[l].map (Fg.map (extensionByZeroIhomToIhom i B F))) :=
        inferInstanceAs (IsIso ((IsoAlgebra.forget _).map
          ((ProEtaleWeilSheaf.upperStar k₀ l i).map (extensionByZeroIhomToIhom i B F))))
      have : Epi ((ib)^*ᵃ[l].map (Fg.map (extensionByZeroIhomToIhom i B F))) :=
        IsIso.epi_of_iso _
      exact (isZero_cokernel_of_epi _).of_iso ((ib)^*ᵃ[l].mapIso
        (PreservesCokernel.iso Fg (extensionByZeroIhomToIhom i B F)) ≪≫
          PreservesCokernel.iso (ib)^*ᵃ[l] _)
    have hCk : IsZero ((k)^*ᵃ[l].obj (Fg.obj (cokernel (extensionByZeroIhomToIhom i B F)))) := by
      have h0 : IsZero ((k)^*ᵃ[l].obj ((AdicSheaf.ihom B.carrier).obj
          ((ib)_!ᵃ[l].obj F.carrier))) :=
        IsAdicLisseSheaf.isZero_upperStar_ihom k hB
          (isZero_adicUpperStar_adicOpenImmersionLowerShriek ib k hdisj F.carrier)
      have : Epi (Fg.map (cokernel.π (extensionByZeroIhomToIhom i B F))) := inferInstance
      have : Epi ((k)^*ᵃ[l].map (Fg.map (cokernel.π (extensionByZeroIhomToIhom i B F)))) :=
        inferInstance
      exact h0.of_epi ((k)^*ᵃ[l].map (Fg.map (cokernel.π (extensionByZeroIhomToIhom i B F))))
    exact AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl k ib hij _ hCk hCi
  exact isIso_of_mono_of_epi _

theorem nonempty_extensionByZeroCompIhomFunctorIso [QuasiCompact i]
    (hB : IsAdicLisseSheaf B.carrier) :
    Nonempty (ProEtaleWeilSheaf.extensionByZero k₀ l i ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l Z B ≅
      ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l i).obj B) ⋙
        ProEtaleWeilSheaf.extensionByZero k₀ l i) := by
  have := isIso_extensionByZeroIhomToIhom i B hB
  set ρ := ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i
  refine ⟨(NatIso.ofComponents (fun F ↦ asIso (extensionByZeroIhomToIhom i B F))
    fun {F F'} f ↦ ?_).symm⟩
  have h1 : (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).map
      ((ProEtaleWeilSheaf.extensionByZero k₀ l i).map f) ≫ ihomExtensionByZeroToLowerStar i B F' =
      ihomExtensionByZeroToLowerStar i B F ≫
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).map ((ProEtaleWeilSheaf.lowerStar k₀ l i).map f) := by
    simp only [ihomExtensionByZeroToLowerStar, ← Functor.map_comp]
    congr 1
    exact ρ.naturality f
  have h2 : (ProEtaleWeilSheaf.extensionByZero k₀ l i).map
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l i).obj B)).map f) ≫
      extensionByZeroIhomToIhomLowerStar i B F' =
      extensionByZeroIhomToIhomLowerStar i B F ≫
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Z B).map ((ProEtaleWeilSheaf.lowerStar k₀ l i).map f) := by
    simp only [extensionByZeroIhomToIhomLowerStar, Category.assoc]
    rw [ρ.naturality_assoc]
    congr 1
    exact (lowerStarCompIhomFunctorIso k₀ l i B).inv.naturality f
  rw [← cancel_mono (ihomExtensionByZeroToLowerStar i B F')]
  simp only [Functor.comp_map, asIso_hom, Category.assoc, extensionByZeroIhomToIhom_comp]
  rw [h1, extensionByZeroIhomToIhom_comp_assoc, h2]
  simp only [extensionByZeroIhomToIhomLowerStar, Category.assoc]

end ExtensionByZero

/-- The projection formula for `Rg_* ∘ i_!`, on the derived categories of pro-étale Weil
sheaves. -/
theorem nonempty_rightDerived_projection [QuasiCompact i] (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : IsAdicLisseSheaf A.carrier) (B : ProEtaleWeilSheaf k₀ l X)
    (hB : IsAdicLisseSheaf B.carrier)
    (e : (ProEtaleWeilSheaf.upperStar k₀ l i).obj ((ProEtaleWeilSheaf.upperStar k₀ l g).obj A) ≅
      B) :
    Nonempty ((ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X B).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor) := by
  set A' := (ProEtaleWeilSheaf.upperStar k₀ l g).obj A
  set B' := (ProEtaleWeilSheaf.upperStar k₀ l i).obj A'
  have hA' : IsAdicLisseSheaf A'.carrier := IsAdicLisseSheaf.upperStar _ hA
  have : Fact (IsAdicLisseSheaf A'.carrier) := ⟨hA'⟩
  have := preservesFiniteColimits_ihomFunctor A hA
  have := preservesFiniteColimits_ihomFunctor A' hA'
  have := preservesFiniteColimits_ihomFunctor B hB
  have := preservesFiniteColimits_ihomFunctor B' (IsAdicLisseSheaf.upperStar _ hA')
  obtain ⟨c⟩ := nonempty_extensionByZeroCompIhomFunctorIso i A' hA'
  exact ⟨Functor.isoWhiskerLeft (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory
      (Functor.isoWhiskerLeft (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor
          (ProEtaleWeilSheaf.ihomFunctor k₀ l Y A).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
        Functor.rightDerivedFunctorNatIso (lowerStarCompIhomFunctorIso k₀ l g A) ≪≫
        Functor.rightDerivedFunctorCompIso _ _ ≪≫
        Functor.isoWhiskerRight
          (ProEtaleWeilSheaf.ihomFunctor k₀ l Z A').rightDerivedFunctorIsoMapDerivedCategory _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (ihomFunctorMapIsoLeft e).symm ≪≫
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X B).rightDerivedFunctorIsoMapDerivedCategory.symm) _⟩

end Derived

end ProEtaleWeilSheaf

section DualPullback

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

theorem WeilSheaf.nonempty_upperStar_dual_iso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj (G.dual hG).obj ≅
      (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj) := by
  have h₁ : (G.dual hG).obj =
      ProEtaleWeilSheaf.ihom k₀ l Y G.obj (ProEtaleWeilSheaf.adicConstant k₀ l Y) := rfl
  have h₂ : (ProEtaleWeilSheaf.upperStar k₀ l φ).obj G.obj = ((WeilSheaf.upperStar φ).obj G).obj :=
    rfl
  have h₃ : ProEtaleWeilSheaf.ihom k₀ l X ((WeilSheaf.upperStar φ).obj G).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X) =
      (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj := rfl
  exact ⟨eqToIso (congrArg (ProEtaleWeilSheaf.upperStar k₀ l φ).obj h₁) ≪≫
    WeilSheaf.upperStarDualIso φ G hG ≪≫
    eqToIso ((congrArg (fun A ↦ ProEtaleWeilSheaf.ihom k₀ l X A
      (ProEtaleWeilSheaf.adicConstant k₀ l X)) h₂).trans h₃)⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] [Fact (ringChar k₀ ≠ l)] in
lemma ProEtaleWeilSheaf.nonempty_upperStar_congr {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    Nonempty (ProEtaleWeilSheaf.upperStar k₀ l φ ≅ ProEtaleWeilSheaf.upperStar k₀ l φ') := by
  subst h
  exact ⟨Iso.refl _⟩

end DualPullback

attribute [local instance] Compactification.over

/-- Blueprint `prop-weil-operations`: Six operations on Weil complexes (the projection
formula). For a separated quasi-compact morphism `f : X ⟶ Y` locally of finite type of
`k₀`-schemes of finite type and a lisse Weil sheaf `G` on `Y`, `Rf₀!(f^* G ⊗ K) ≅ G ⊗ Rf₀! K`
naturally in the Weil complex `K` (`G`, lisse, is in particular of finite Tor-amplitude). -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.tensorLisse G hG ≅
      WeilComplex.tensorLisse ((WeilSheaf.upperStar f).obj G)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        WeilComplex.derivedLowerShriek k₀ l f) := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : QuasiCompact c.i := inferInstance
  set G' := (WeilSheaf.upperStar f).obj G
  have hG' : G'.IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ hG
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_upperStar_dual_iso f G hG
  obtain ⟨e₂⟩ := ProEtaleWeilSheaf.nonempty_upperStar_congr (k₀ := k₀) (l := l) c.comm.symm
  have e : (ProEtaleWeilSheaf.upperStar k₀ l c.i).obj
      ((ProEtaleWeilSheaf.upperStar k₀ l c.g).obj (G.dual hG).obj) ≅ (G'.dual hG').obj :=
    ((ProEtaleWeilSheaf.upperStarCompIso k₀ l c.i c.g).app _).symm ≪≫ e₂.app _ ≪≫ e₁
  have hA : IsAdicLisseSheaf (G.dual hG).obj.carrier := hG.dual
  have hB : IsAdicLisseSheaf (G'.dual hG').obj.carrier := hG'.dual
  obtain ⟨E⟩ := ProEtaleWeilSheaf.nonempty_rightDerived_projection c.i c.g _ hA _ hB e
  refine ⟨((WeilComplex.objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso (G.dual hG) hG.dual) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ E ≪≫
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso (G'.dual hG') hG'.dual) _ ≪≫
      Functor.associator _ _ _).symm

end AlgebraicGeometry
