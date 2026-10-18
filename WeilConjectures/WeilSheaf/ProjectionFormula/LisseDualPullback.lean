/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LisseDuality
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian

/-!
# The pullback of the dual of a lisse sheaf, on locally Noetherian schemes

A morphism of lisse sheaves on a locally Noetherian scheme `Y` is a monomorphism (an
epimorphism) as soon as it is injective (surjective) on the stalks at geometric points `s`
with values in a fixed algebraically closed field `K`, provided every point of `Y` specializes
to the image of such a point: its kernel (cokernel) is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.kernel_cokernel`) with vanishing stalks at these
points, hence zero
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_of_subsingleton_globalSections_upperStar`).

Hence the comparison `g^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(g^* G, ℚ̄_ℓ)` is an isomorphism for every lisse
`G` and every morphism `g : Z ⟶ Y` from such a scheme
(`AlgebraicGeometry.ProEtale.isIso_adicUpperStarDualComparison_of_specializes`), without the
irreducibility assumption of `AlgebraicGeometry.ProEtale.isIso_adicUpperStarDualComparison`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry

/-- Every point of a quasi-compact scheme locally of finite type over an algebraically closed
field `k` specializes to a `k`-rational point: the closure of the point contains a closed point,
whose residue field is finite over `k`, hence equal to `k`. -/
lemma Scheme.Hom.exists_specializes_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    ∃ σ : Spec (.of k) ⟶ X, x ⤳ σ.base (IsLocalRing.closedPoint k) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := {x})).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have : IsClosedImmersion (X.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hyc
  let g := X.fromSpecResidueField y ≫ f
  have : IsFinite g := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k (X.residueField y) := hfin
  have hbij : Function.Bijective φ.hom :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := X.residueField y)
  let e : k ≃+* X.residueField y := RingEquiv.ofBijective φ.hom hbij
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField y, ?_⟩
  rw [Scheme.Hom.comp_apply]
  convert specializes_iff_mem_closure.2 hy using 1
  exact X.fromSpecResidueField_apply y _

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} [IsLocallyNoetherian Y] {K : Type u} [Field K]
  [IsAlgClosed K]

/-- A morphism of lisse sheaves on a locally Noetherian scheme is a monomorphism as soon as it is
injective on the stalks at geometric points to which every point specializes. -/
theorem IsAdicLisseSheaf.mono_of_injective_stalkFunctor_map_of_specializes {F G : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (f : F ⟶ G)
    (hK : ∀ y : Y, ∃ s : Spec (.of K) ⟶ Y, y ⤳ s.base (IsLocalRing.closedPoint K))
    (hf : ∀ s : Spec (.of K) ⟶ Y, Function.Injective ((stalkFunctor l s).map f.hom).hom) :
    Mono f := by
  refine Preadditive.mono_of_isZero_kernel f
    ((hF.kernel_cokernel hG f).1.isZero_of_subsingleton_globalSections_upperStar K fun y ↦ ?_)
  obtain ⟨s, hs⟩ := hK y
  refine ⟨y, s, specializes_rfl, hs, ⟨fun a b ↦ ?_⟩⟩
  have hι : Function.Injective ((stalkFunctor l s).map (kernel.ι f).hom).hom :=
    have : Mono (kernel.ι f).hom := (AdicSheaf.forget Y).map_mono (kernel.ι f)
    (ModuleCat.mono_iff_injective _).1 ((stalkFunctor l s).map_mono _)
  have h0 (x : (stalkFunctor l s).obj (kernel f).X) :
      ((stalkFunctor l s).map f.hom).hom (((stalkFunctor l s).map (kernel.ι f).hom).hom x) =
        0 := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', kernel.condition]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  exact hι (hf s ((h0 a).trans (h0 b).symm))

/-- A morphism of lisse sheaves on a locally Noetherian scheme is an epimorphism as soon as it is
surjective on the stalks at geometric points to which every point specializes. -/
theorem IsAdicLisseSheaf.epi_of_surjective_stalkFunctor_map_of_specializes {F G : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (f : F ⟶ G)
    (hK : ∀ y : Y, ∃ s : Spec (.of K) ⟶ Y, y ⤳ s.base (IsLocalRing.closedPoint K))
    (hf : ∀ s : Spec (.of K) ⟶ Y, Function.Surjective ((stalkFunctor l s).map f.hom).hom) :
    Epi f := by
  refine Preadditive.epi_of_isZero_cokernel f
    ((hF.kernel_cokernel hG f).2.isZero_of_subsingleton_globalSections_upperStar K fun y ↦ ?_)
  obtain ⟨s, hs⟩ := hK y
  refine ⟨y, s, specializes_rfl, hs, ⟨fun a b ↦ ?_⟩⟩
  have hπ : Function.Surjective ((stalkFunctor l s).map (cokernel.π f).hom).hom :=
    have : Epi (cokernel.π f).hom := (AdicSheaf.forget Y).map_epi (cokernel.π f)
    (ModuleCat.epi_iff_surjective _).1 ((stalkFunctor l s).map_epi _)
  have h0 (x : (stalkFunctor l s).obj F.X) :
      ((stalkFunctor l s).map (cokernel.π f).hom).hom (((stalkFunctor l s).map f.hom).hom x) =
        0 := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', cokernel.condition]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  obtain ⟨a', rfl⟩ := hπ a
  obtain ⟨b', rfl⟩ := hπ b
  obtain ⟨a'', rfl⟩ := hf s a'
  obtain ⟨b'', rfl⟩ := hf s b'
  exact (h0 a'').trans (h0 b'').symm

section Pullback

attribute [local instance] Sheaf.symmetricCategory

variable {X : Scheme.{u}} {Z : Scheme.{u}} [IsLocallyNoetherian Z] (g : Z ⟶ X)

/-- **The pullback of the dual of a lisse sheaf is the dual of the pullback**: for `G` lisse on
`X` and `g : Z ⟶ X` with `Z` locally Noetherian, such that every point of `Z` specializes to
the image of a geometric point with values in `K`, the comparison
`g^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(g^* G, ℚ̄_ℓ)` is an isomorphism. Both sides are lisse, and on the
stalks at each geometric point the evaluations induce perfect pairings. -/
theorem isIso_adicUpperStarDualComparison_of_specializes {G : AdicSheaf l X}
    (hG : IsAdicLisseSheaf G)
    (hK : ∀ z : Z, ∃ s : Spec (.of K) ⟶ Z, z ⤳ s.base (IsLocalRing.closedPoint K)) :
    IsIso (adicUpperStarDualComparison l g G) := by
  have h₁ : IsAdicLisseSheaf ((g)^*ᵃ[l].obj ((AdicSheaf.ihom G).obj (AdicSheaf.unit l X))) :=
    (hG.ihom (isAdicLisseSheaf_adicConstantSheaf X)).upperStar g
  have h₂ : IsAdicLisseSheaf ((AdicSheaf.ihom ((g)^*ᵃ[l].obj G)).obj (AdicSheaf.unit l Z)) :=
    (hG.upperStar g).ihom (isAdicLisseSheaf_adicConstantSheaf Z)
  have hbij (s : Spec (.of K) ⟶ Z) :
      Function.Bijective
        ((stalkFunctor l s).map (adicUpperStarDualComparison l g G).hom).hom := by
    have hP₁ := (hG.upperStar g).bijective_evaluationPairing s
    let τ : stalkFunctor l (s ≫ g) ≅ (g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s :=
      Functor.isoWhiskerRight (upperStarComp _ s g) _ ≪≫ Functor.associator _ _ _
    have : NatTrans.IsMonoidal τ.hom := by
      dsimp only [τ, Iso.trans_hom, Functor.isoWhiskerRight_hom]
      infer_instance
    have hP₂ := (Mod.bijective_evaluationPairing_iff_of_iso _ τ G (AdicSheaf.unit l X)).1
      (hG.bijective_evaluationPairing (s ≫ g))
    let u := (stalkFunctor l s).mapIso ((Mod.forget _).mapIso (adicUpperStarUnitIso l g))
    have hu (y) : u.hom.hom (u.inv.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
    have hrel := evaluationPairing_adicUpperStarDualComparison g G s
    refine ⟨fun f f' h ↦ hP₂.1 (LinearMap.ext fun x ↦ u.toLinearEquiv.injective (by
      have := LinearMap.congr_fun (congrArg (Mod.evaluationPairing (stalkFunctor l s) _ _) h) x
      rwa [hrel, hrel] at this)), fun w ↦ ?_⟩
    obtain ⟨f, hf⟩ := hP₂.2 (u.inv.hom ∘ₗ Mod.evaluationPairing (stalkFunctor l s) _ _ w)
    refine ⟨f, hP₁.1 (LinearMap.ext fun x ↦ ?_)⟩
    rw [hrel, hf, LinearMap.comp_apply]
    exact hu _
  have := h₁.mono_of_injective_stalkFunctor_map_of_specializes h₂ _ hK fun s ↦ (hbij s).1
  have := h₁.epi_of_surjective_stalkFunctor_map_of_specializes h₂ _ hK fun s ↦ (hbij s).2
  exact isIso_of_mono_of_epi _

end Pullback

end ProEtale

end AlgebraicGeometry
