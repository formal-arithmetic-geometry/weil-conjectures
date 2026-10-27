/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.CategoryTheory.InternalActionInflation
public import Sheaf.CategoryTheory.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.ExactFamilyDetection
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Grothendieck structure and exact restriction of internal sheaf actions

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated categorical input
(blueprint: lem-sfb-sheaf-action-grothendieck-inflation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]
  {K L : Cᵒᵖ ⥤ GrpCat.{u}} {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Exact inflation preserves the displayed kernels and cokernels.
Its definition already fixes the underlying module, all maps and the action θ(l).
Source: paragraph (3), categorical input, exact inflation
(blueprint: lem-sfb-sheaf-action-grothendieck-inflation). -/
structure ActionInflationExact (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u})
    (θ : L ⟶ K) : Prop where
  /-- Inflation leaves addition of component maps unchanged. -/
  [additive : (inflateSheaf J S θ).Additive]
  /-- Inflation preserves kernels, in particular the displayed induced action. -/
  finiteLimits : PreservesFiniteLimits (inflateSheaf J S θ)
  /-- Inflation preserves cokernels, including the sheafified quotient. -/
  finiteColimits : PreservesFiniteColimits (inflateSheaf J S θ)
  /-- Inflation is exact on every consecutive pair of a complex. -/
  exact (T : ShortComplex (EquivariantSheaf (K := K) J S)) :
    T.Exact → (T.map (inflateSheaf J S θ)).Exact

private theorem forget_additive (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    (forgetSheaf (K := K) J S).Additive where
  map_add := by intros; rfl

private theorem forget_faithful (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    (forgetSheaf (K := K) J S).Faithful where
  map_injective := by
    intro M N f g h
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact congrArg SheafOfModules.Hom.val h

private theorem forget_zero_iff (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u})
    (M : EquivariantSheaf (K := K) J S) :
    IsZero M ↔ IsZero ((forgetSheaf J S).obj M) := by
  let U := forgetSheaf (K := K) J S
  have : U.Additive := forget_additive J S
  have : U.Faithful := forget_faithful J S
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero, ← U.map_id, ← U.map_zero]
  exact ⟨congrArg U.map, fun h ↦ U.map_injective h⟩

@[instance_reducible]
private noncomputable def actionAbelian [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ S) :
    Abelian (EquivariantSheaf (K := K) J.toGrothendieck
      (baseRing J.toGrothendieck S)) := by
  let E := P.sheafEquivalence
  have : HasFiniteProducts (EquivariantSheaf (K := K) J.toGrothendieck
      (baseRing J.toGrothendieck S)) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  exact abelianOfEquivalence E.functor

private theorem action_grothendieck [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ S) :
    @IsGrothendieckAbelian.{u} _ _ (actionAbelian J hJ S P) := by
  let := actionAbelian J hJ S P
  have : IsGrothendieckAbelian.{u} (ringedSiteModules (twistedRing K J hJ S)) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator
      (topology K J) (coefficientSheaf K J hJ S)).1
  exact IsGrothendieckAbelian.of_equivalence P.sheafEquivalence.symm

private theorem module_cokernel (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u})
    {M N : ringedSiteModules S} (f : M ⟶ N) :
    Nonempty (cokernel f ≅ (PresheafOfModules.sheafification (𝟙 S.obj)).obj
      (cokernel ((SheafOfModules.forget S).map f))) := by
  let F := PresheafOfModules.sheafification (𝟙 S.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)
  let e := asIso adj.counit
  exact ⟨(cokernel.mapIso _ f (e.app M) (e.app N)
    (adj.counit.naturality f) |>.symm) ≪≫
      (PreservesCokernel.iso F ((SheafOfModules.forget S).map f)).symm⟩

private theorem action_forget_exact [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ S)
    :
    ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck S) K := by
  let := actionAbelian J hJ S P
  let U := forgetSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  have : U.Additive := forget_additive _ _
  have : U.Faithful := forget_faithful _ _
  have {M N} (f : M ⟶ N) : PreservesLimit (parallelPair f 0) U := by
    have := (P.createsKernels M N f).some
    infer_instance
  have {M N} (f : M ⟶ N) : PreservesColimit (parallelPair f 0) U := by
    have := (P.createsCokernels M N f).some
    infer_instance
  have : PreservesFiniteLimits U := U.preservesFiniteLimits_of_preservesKernels
  have : PreservesFiniteColimits U := U.preservesFiniteColimits_of_preservesCokernels
  refine { additive := inferInstance
           finiteLimits := inferInstance
           finiteColimits := inferInstance
           exact_iff := ?_
           zero_iff := forget_zero_iff _ _
           createsKernels := P.createsKernels
           createsCokernels := P.createsCokernels
           sectionwiseKernel := ?_
           sheafifiedCokernel := ?_ }
  · intro T
    have : ∀ _ : Unit, U.Additive := fun _ ↦ inferInstance
    have : ∀ _ : Unit, PreservesFiniteLimits U := fun _ ↦ inferInstance
    have : ∀ _ : Unit, PreservesFiniteColimits U := fun _ ↦ inferInstance
    have h := (exact_family_detection (fun _ : Unit ↦ U)
      (fun M h ↦ (forget_zero_iff _ _ M).mpr (h ()))).2.2.1 T
    simpa only [forall_const] using h
  · intros
    infer_instance
  · intro M N f
    exact module_cokernel _ _ (U.map f)

private theorem action_inflation_exact [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u})
    (PK : Presentation K J hJ S) (PL : Presentation L J hJ S) (θ : L ⟶ K) :
    ActionInflationExact J.toGrothendieck (baseRing J.toGrothendieck S) θ := by
  let := actionAbelian J hJ S PK
  let := actionAbelian J hJ S PL
  let U := forgetSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  let V := forgetSheaf (K := L) J.toGrothendieck (baseRing J.toGrothendieck S)
  let F := inflateSheaf J.toGrothendieck (baseRing J.toGrothendieck S) θ
  have hU := action_forget_exact J hJ S PK
  have hV := action_forget_exact J hJ S PL
  have : U.Additive := hU.additive
  have : V.Additive := hV.additive
  have : PreservesFiniteLimits U := hU.finiteLimits
  have : PreservesFiniteColimits U := hU.finiteColimits
  have : PreservesFiniteLimits V := hV.finiteLimits
  have : PreservesFiniteColimits V := hV.finiteColimits
  have : F.Additive := ⟨by intros; rfl⟩
  have : ∀ _ : Unit, V.Additive := fun _ ↦ inferInstance
  have : ∀ _ : Unit, PreservesFiniteLimits V := fun _ ↦ inferInstance
  have : ∀ _ : Unit, PreservesFiniteColimits V := fun _ ↦ inferInstance
  have hv := exact_family_detection (fun _ : Unit ↦ V)
    (fun M h ↦ (hV.zero_iff M).mpr (h ()))
  have : V.ReflectsIsomorphisms := ⟨fun f hf ↦ hv.2.1 f (fun _ ↦ hf)⟩
  have : PreservesFiniteLimits (F ⋙ V) := show PreservesFiniteLimits U from inferInstance
  have : PreservesFiniteColimits (F ⋙ V) := show PreservesFiniteColimits U from inferInstance
  refine { additive := inferInstance
           finiteLimits := preservesFiniteLimits_of_reflects_of_preserves F V
           finiteColimits := preservesFiniteColimits_of_reflects_of_preserves F V
           exact := ?_ }
  intro T hT
  apply (hV.exact_iff (T.map F)).mpr
  exact (hU.exact_iff T).mp hT

/-- Internal linear action sheaves are Grothendieck abelian with their specified
sectionwise addition; forgetting creates kernels and sheafified cokernels and
detects exactness and zero; restriction along every group-sheaf map is additive exact.

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated categorical input
(blueprint: lem-sfb-sheaf-action-grothendieck-inflation).

Proof:
1. Apply lem-sfb-internal-action-site-presentation to the small site, coefficient
   ring with trivial action, and K. Its additive equivalence retains all section maps.
2. Apply lem-pur-ringed-site-grothendieck-abelian on the small twisted site.
   Transfer zero objects, biproducts, kernels and cokernels across the equivalence
   (lem-galois-equivalence-preserves-limits). Monos and epis are normal after this
   transfer, giving def-sp-abelian with the specified sectionwise addition.
3. Transfer small colimits and a generator through the equivalence: fullness identifies
   the tests for a generator and faithfulness reflects their equalities.
4. Transfer exact filtered colimits. Both directions preserve images as kernels of
   cokernels and hence preserve the exactness test def-weil-pbc-exact-sequence.
   This gives every condition of def-sp-grothendieck-abelian.
5. The presentation creates sectionwise kernels and module-sheafified cokernels,
   with induced actions, and detects zero on restriction to the original site.
6. The underlying functor preserves addition, zero and biproducts, kernels and cokernels.
   Equalizers are kernels of differences and coequalizers are cokernels of differences.
   Apply lem-per-exact-family-detection to its singleton family to detect exactness.
7. Precompose each action with θ. Its homomorphism and naturality equations give
   the action laws and restriction compatibility. Equivariant maps remain equivariant.
8. On kernels the restricted action is θ(l); on quotient presheaves it is [θ(l)n].
   Unique equivariant extension through module sheafification, as in
   lem-sfb-equivariant-module-sheafification-reflector (also contained in the
   presentation's adjunction and unit comparison), identifies the cokernel action.
   Underlying modules do not change, so exactness follows from zero/exactness detection.
   No step uses nontriviality of K or L or a nonzero coefficient ring.
-/
theorem sheaf_action_grothendieck_inflation [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u}))
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) (θ : L ⟶ K) :
    (∃ aK : Abelian (EquivariantSheaf (K := K) J.toGrothendieck
        (baseRing J.toGrothendieck S)),
      aK.toPreadditive = (inferInstance : Preadditive (EquivariantSheaf
        (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))) ∧
      @IsGrothendieckAbelian.{u} _ _ aK) ∧
    (∃ aL : Abelian (EquivariantSheaf (K := L) J.toGrothendieck
        (baseRing J.toGrothendieck S)),
      aL.toPreadditive = (inferInstance : Preadditive (EquivariantSheaf
        (K := L) J.toGrothendieck (baseRing J.toGrothendieck S))) ∧
      @IsGrothendieckAbelian.{u} _ _ aL) ∧
    ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck S) K ∧
    ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck S) L ∧
    ActionInflationExact J.toGrothendieck (baseRing J.toGrothendieck S) θ := by
  obtain ⟨PK⟩ := presentation K J hJ hK S
  obtain ⟨PL⟩ := presentation L J hJ hL S
  exact ⟨⟨actionAbelian J hJ S PK, rfl, action_grothendieck J hJ S PK⟩,
    ⟨actionAbelian J hJ S PL, rfl, action_grothendieck J hJ S PL⟩,
    action_forget_exact J hJ S PK, action_forget_exact J hJ S PL,
    action_inflation_exact J hJ S PK PL θ⟩

end CategoryTheory.InternalActionSite
