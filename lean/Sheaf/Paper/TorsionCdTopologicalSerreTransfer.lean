/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.TorsionCdBoundedSerreKernel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Sheaf.Paper.FiniteConstructibleComplexHeartCd
import Sheaf.Paper.ConstructibleFiniteHeart
import Sheaf.Paper.CondensedSectionsIndVanishing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Sheaf.Paper.FiniteDiscreteSerreHeartCd
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# From torsion dimension to topological-coefficient weak Serre heart vanishing

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; the agent-formulated
coefficient transfer obligation (blueprint: lem-sfb-torsion-cd-topological-serre-transfer).
An exact reference in the full stated generality is WANTED; Hemo--Richarz--Scholbach,
Section 8, condition (8.1) and Lemma 8.6 motivate but do not assert this statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩


/-- Ordinary uncompleted module-derived sections vanish above `d + 2` on the weak
Serre coproduct hull of finite constant scalar-model constructible modules.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
agent coefficient-transfer obligation; compare Hemo--Richarz--Scholbach, Section 8,
condition (8.1) and Lemma 8.6. Exact reference WANTED.
(blueprint: lem-sfb-torsion-cd-topological-serre-transfer)

Proof: intersect the weak Serre coproduct hull P with the property B that all
ordinary derived section cohomology above d+2 vanishes. The existing finite-complex
heart estimate, applied to the single complex, puts every constructible generator
in P ∩ B. The long exact sequence gives extension closure. Filtered continuity
and finite partial sums give small coproduct closure. The new bounded-kernel lemma
supplies kernel closure of P ∩ B; its two input bounds are already available.
Two short exact sequences, through the coimage, then give cokernel closure.
Minimality of P completes the argument. The remaining kernel obligation is isolated
in `Sheaf.Paper.TorsionCdBoundedSerreKernel`; this is a decomposition, not a closed
proof of the disputed geometric input. No finite-heart approximation is used.
-/
-- STATEMENT-DISPUTED: the arbitrary-affine bounded-kernel input remains unproved.
-- The former filtered finite-heart approximation was refuted. The new reduction
-- isolates cohomological kernel closure without asserting that false presentation.
theorem torsionCd_topological_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : Zero A := HasZeroObject.zero' A
  let H := fun q : ℤ ↦ DerivedCategory.singleFunctor A 0 ⋙
    (condensedModuleSections Λ X).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q
  let B : ObjectProperty A := fun N ↦ ∀ q : ℤ, (d : ℤ) + 2 < q → IsZero ((H q).obj N)
  let P := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible Λ X)
  let Q : ObjectProperty A := fun N ↦ P N ∧ B N
  have hgen : IsConstantModelConstructible Λ X ≤ Q := by
    intro N hN
    refine ⟨ObjectProperty.le_weakSerreCoproductClosure _ _ hN, ?_⟩
    obtain ⟨K, hK, ⟨e⟩⟩ := constructible_le_finiteConstructibleComplexHearts Λ X N hN
    intro r hr
    let U : X.ProEt := Scheme.ProEt.mk (𝟙 X)
    have : IsAffine U.left := by change IsAffine X; infer_instance
    have hv := finite_constructible_complex_heart_cohomology_vanishes
      ℓ Λ hΛ X d hcd K hK.1 hK.2 U r hr
    let e' : (CondensedRing.upperStar Λ U.hom).obj (K.homology 0) ≅ N :=
      (CondensedRing.upperStarId Λ X).app (K.homology 0) ≪≫ e.symm
    exact hv.of_iso ((H r).mapIso e').symm
  have : B.IsClosedUnderIsomorphisms := ⟨fun e h r hr ↦
    (h r hr).of_iso ((H r).mapIso e.symm)⟩
  have : B.ContainsZero := ⟨0, isZero_zero _, fun r _ ↦
    (H r).map_isZero (isZero_zero _)⟩
  have : B.IsClosedUnderExtensions := ⟨by
    intro S hS h₁ h₃ r hr
    exact ((condensedModuleSections Λ X).rightDerivedHomologySequence_exact₂ hS r)
      |>.isZero_of_both_isZero (h₁ r hr) (h₃ r hr)⟩
  have : B.IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      exact B.prop_of_iso
        ((biprod.isoCoprod _ _) ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
        (B.prop_biprod (hF _) (hF _)))
  have : B.IsClosedUnderFiniteCoproducts := .mk'
  have hsum (I : Type (u + 1)) : B.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let f : I → A := fun i ↦ F.obj ⟨i⟩
    have hind : B.ind.{u + 1} (∐ f) := by
      refine ⟨Finset (Discrete I), inferInstance, inferInstance,
        ⟨_, _, CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f⟩, ?_⟩
      intro s
      exact B.prop_coproduct (fun i ↦ hF i.1)
    intro r hr
    have hv := condensedModuleSections_ind_isZero Λ X B r (fun N hN ↦ hN r hr)
      (∐ f) hind
    exact hv.of_iso ((H r).mapIso
      (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))))
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    ⟨P.prop_of_iso e h.1, B.prop_of_iso e h.2⟩⟩
  have : Q.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦
    ⟨P.prop_X₂_of_shortExact hS h₁.1 h₃.1,
      B.prop_X₂_of_shortExact hS h₁.2 h₃.2⟩⟩
  have hQsum (I : Type (u + 1)) : Q.IsClosedUnderColimitsOfShape (Discrete I) := by
    have := hsum I
    exact ⟨fun N ⟨F, hF⟩ ↦
      ⟨P.prop_of_isColimit F.isColimit (fun i ↦ (hF i).1),
        B.prop_of_isColimit F.isColimit (fun i ↦ (hF i).2)⟩⟩
  have hker : Q.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, h⟩
    refine ⟨P.prop_of_isLimit_kernelFork hk h.1.1 h.2.1, ?_⟩
    intro r hr
    have hv := torsionCd_bounded_serre_kernel ℓ Λ hΛ X d hcd _ _ f
      h.1.1 h.2.1 h.1.2 h.2.2 r hr
    exact hv.of_iso ((H r).mapIso ((kernelIsKernel f).conePointUniqueUpToIso hk)).symm⟩
  have hcoker : Q.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, h⟩
    refine ⟨P.prop_of_isColimit_cokernelCofork hk h.1.1 h.2.1, ?_⟩
    let i := Abelian.factorThruCoimage f
    have hIb : B (Abelian.coimage f) := by
      let S₀ := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
        (cokernel.condition (kernel.ι f))
      have hS₀ : S₀.ShortExact :=
        { exact := ShortComplex.exact_cokernel (kernel.ι f)
          mono_f := by dsimp [S₀]; infer_instance
          epi_g := by dsimp [S₀]; infer_instance }
      intro r hr
      have hv := torsionCd_bounded_serre_kernel ℓ Λ hΛ X d hcd _ _ f
        h.1.1 h.2.1 h.1.2 h.2.2 (r + 1) (by omega)
      exact ((condensedModuleSections Λ X).rightDerivedHomologySequence_exact₃
        hS₀ r (r + 1) rfl).isZero_of_both_isZero (h.1.2 r hr) hv
    let S := ShortComplex.mk i k.π (by
      dsimp [i]
      rw [← cancel_epi (Abelian.coimage.π f), ← Category.assoc,
        Abelian.coimage.fac, k.condition, comp_zero])
    have hS : S.ShortExact :=
      { exact := S.exact_of_g_is_cokernel
          (isCokernelOfComp (Abelian.coimage.π f) f hk S.zero (Abelian.coimage.fac f))
        mono_f := by dsimp [S, i]; infer_instance
        epi_g := Cofork.IsColimit.epi hk }
    intro r hr
    exact ((condensedModuleSections Λ X).rightDerivedHomologySequence_exact₃
      hS r (r + 1) rfl).isZero_of_both_isZero (h.2.2 r hr) (hIb (r + 1) (by omega))⟩
  exact (hM Q hgen inferInstance hker hcoker inferInstance hQsum).2 q hq

/-- The finite discrete branch of the topological transfer on any affine scheme.
Source: Stacks Tags 03SA(3), 099Y, and exact etale/pro-etale comparison.
(blueprint: lem-sfb-finite-coefficient-serre-cd)
Proof: lift the finite ring into the scheme universe and transport the module along
the induced condensed coefficient isomorphism. Exact scalar restriction transports
the weak Serre coproduct hull. The finite discrete bound applies to the identity
etale test and gives vanishing above d. Sections commute with scalar restriction;
classical right-derived evaluation agrees with the displayed unbounded derived
functor on heart objects. The coefficient ring may be zero and the affine base may
be empty or non-Noetherian. -/
theorem finiteCoefficient_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A]
    (htors : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  -- A shorter proof uses étale origin directly and gives vanishing already above d.
  let B := ULift.{u} A
  let Λ' := FiniteDiscreteOrdinary.coefficient B
  let j : Mon.mk Λ ≅ Mon.mk Λ' := e ≪≫ (finiteCoefficientLiftIso A).some
  have : IsIso j.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map j.inv))
  let φ := (upperStarFromPoint X).map j.inv.hom
  let E := Mod.comapEquivalenceOfIsIso φ
  have : E.functor.Additive := inferInstanceAs (Mod.comap φ).Additive
  let P := IsConstantModelConstructible Λ' X
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1} P
  have hN : Q (E.functor.obj M) := by
    apply hM (Q.inverseImage E.functor) ?_ inferInstance inferInstance inferInstance
      inferInstance (fun _ ↦ inferInstance)
    intro N hN
    exact ObjectProperty.le_weakSerreCoproductClosure P _
      (constructible_comap j.inv.hom X N hN)
  have htorsB : ∃ n : ℕ, ∀ a : B, (ℓ ^ n) • a = 0 := by
    obtain ⟨n, hn⟩ := htors
    exact ⟨n, fun a ↦ ULift.ext _ _ (hn a.down)⟩
  have hq0 : 0 ≤ q := by omega
  lift q to ℕ using hq0
  have hz := FiniteDiscreteOrdinary.finiteDiscrete_serreHeart_cohomology_vanishes B
    ℓ htorsB X d (hcd X (𝟙 X)) (E.functor.obj M) hN q (by omega)
  let eΓ : condensedModuleSections Λ X ≅ E.functor ⋙ condensedModuleSections Λ' X :=
    NatIso.ofComponents (fun N ↦ Iso.refl _) (by intros; rfl)
  have hz' : IsZero (((condensedModuleSections Λ X).rightDerived q).obj M) :=
    hz.of_iso (Functor.rightDerivedObjIsoOfIso eΓ q M ≪≫
      Functor.compRightDerivedObjIso E.functor (condensedModuleSections Λ' X)
        (fun _ _ ↦ Functor.rightAcyclic_of_injective _) q M)
  exact hz'.of_iso
    ((condensedModuleSections Λ X).homologyRightDerivedFunctorObjSingleFunctorIso M q)
end AlgebraicGeometry.ProEtale
