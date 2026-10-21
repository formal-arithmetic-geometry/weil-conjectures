/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.IntegralReductionTriangulatedProperty
import Sheaf.Paper.IntegralReductionTensor
import Sheaf.Paper.IntegralConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Bounded constructibility of integral reduction

Source: Bhatt--Scholze, Proposition 6.8.11(3), and the finite free residue resolution.
(blueprint: lem-weil-pbc-integral-reduction-constructible)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Quotient

variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (q : R ⟶ S) [IsMonHom q] [Epi q]

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem full_comap_of_epi :
    (Mod.comap q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).Full where
  map_surjective {M N} f := by
    have : Epi (q ▷ M.X) := (tensorRight M.X).map_epi q
    refine ⟨Mod.homMk f.hom ?_, ?_⟩
    · apply (cancel_epi (q ▷ M.X)).1
      let t : M.X ⟶ N.X := f.hom
      have hf : q ▷ M.X ≫ γ[S,M.X] ≫ t = R ◁ t ≫ q ▷ N.X ≫ γ[S,N.X] := by
        simpa only [Mod.act, Mod.comap_obj_smul, Category.assoc] using Mod.act_hom f
      rw [whisker_exchange_assoc] at hf
      exact hf
    · apply Mod.hom_ext
      rfl

omit [IsCommMonObj R] in
private theorem fp_of_iso {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ e'⟩⟩

private noncomputable def regularExtendIso :
    (Mod.extendScalars q).obj (Mod.regular R) ≅ Mod.regular S := by
  let B := Bimod.ofMonHom q
  let e₀ := Mod.toBimodRegularIso (R := R)
  let e₁ : B.tensorBimod ((Mod.toBimod R).obj (Mod.regular R)) ≅
      B.tensorBimod (Bimod.regular (Mon.mk R)) :=
    { hom := Bimod.whiskerLeft B e₀.hom
      inv := Bimod.whiskerLeft B e₀.inv
      hom_inv_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, Iso.hom_inv_id]
        exact Bimod.whiskerLeft_id_bimod
      inv_hom_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, Iso.inv_hom_id]
        exact Bimod.whiskerLeft_id_bimod }
  let e := e₁ ≪≫ Bimod.rightUnitorBimod B
  exact Mod.isoMk
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bimod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Bimod.Hom.hom e.inv_hom_id }
    e.hom.left_act_hom

omit [IsCommMonObj S] [Epi q] in
private theorem fp_extend {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars q).obj M) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := h
  let F := Mod.extendScalars q
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ regularExtendIso R S q)
  let f' := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso e ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

omit [IsCommMonObj S] in
private theorem fp_reflect {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented R ((Mod.comap q).obj M)) :
    Mod.IsFinitelyPresented S M := by
  have : (Mod.comap q).Full := full_comap_of_epi R S q
  exact fp_of_iso S (fp_extend R S q h)
    (asIso ((Mod.extendRestrictAdjunction q).counit.app M))

omit [IsCommMonObj S] in
private theorem lfp_reflect {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented R ((Mod.comap q).obj M)) :
    IsLocallyFinitelyPresented S M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (U.f i)
  exact fp_reflect (F.obj R) (F.obj S) (F.map q)
    (fp_of_iso _ (hU i) ((F.mapModComapIso q).app M))

omit [IsCommMonObj S] in
private theorem constructible_reflect
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject R ((Mod.comap q).obj M)) :
    IsConstructibleModuleObject S M := by
  obtain ⟨V, hV⟩ := h
  refine ⟨V, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (V.immersion i)
  exact lfp_reflect (F.obj R) (F.obj S) (F.map q)
    (_root_.localFinitePresentation_of_iso ((F.mapModComapIso q).app M) (hV i))

end Quotient

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Derived reduction modulo ℓ preserves bounded constructible integral complexes.

Source: Bhatt--Scholze, Proposition 6.8.11(3), the two-term finite free residue resolution.
(blueprint: lem-weil-pbc-integral-reduction-constructible)

Proof. Constructible integral modules form a weak Serre class, so bounded constructible
integral complexes form a triangulated subcategory. Restricted derived reduction belongs
to this subcategory by the mapping-cone argument for multiplication by ℓ. Exact faithful
restriction of scalars reflects cohomological boundedness. It also reflects constructibility
along the quotient: restriction along an epimorphism of ring objects is fully faithful,
because an integral-linear map is residue-linear after cancellation of the epimorphism
q tensored with its source. Hence the extension-restriction counit is invertible.
Extension of scalars preserves finite presentations: apply it to the presentation,
identify the images of finite free modules with the corresponding residue finite free
modules, and use preservation of cokernels. Thus an integral finite presentation of a
restricted residue module gives a residue finite presentation. Inverse image commutes
with restriction, so the same argument on each presentation cover and stratum proves
reflection of constructibility. Apply it to each cohomology object, using exact
restriction's homology comparison. Empty covers, zero ranks, and zero modules are included.
-/
theorem integralReduction_boundedConstructible (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] (M : integralConstructible ℓ E X) :
    boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X)
      ((integralReduction ℓ E X).obj M.obj) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj (integralResidue ℓ E)) X
  let q := coefficientMap (integralReductionMap ℓ E) X
  have : Epi (integralReductionMap.{u} ℓ E) :=
    (integralReductionSequence_shortExact ℓ E).epi_g
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : Epi q := (upperStarFromPoint X).map_epi (integralReductionMap ℓ E)
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).1
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.1
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.2
  let : (boundedConstructible R).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre R
  have : (boundedConstructible R).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e h.1,
      fun n ↦ _root_.constructible_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩⟩
  obtain ⟨ε, hε⟩ := integralReduction_restrictTensor ℓ E X
  have h := integralReduction_restricted_mem ℓ E X (boundedConstructible R)
    M.obj M.property ε hε
  refine ⟨(Mod.comap q).bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
  apply constructible_reflect R S q
  exact _root_.constructible_of_iso
    (((Mod.comap q).mapDerivedCategoryHomologyFunctorIso n).symm.app _)
    (h.2 n)

end AlgebraicGeometry.ProEtale.CondensedRing
