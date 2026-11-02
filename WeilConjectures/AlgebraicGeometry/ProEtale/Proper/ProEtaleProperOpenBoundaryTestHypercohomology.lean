/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenProperClopenWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedInjectiveSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedInjectiveCohomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleDirectImageLeftExact

/-! # Local proper/open boundary hypercohomology

Source: Step 2 of the boundary-restriction proof, or Steps 5--7 of the
open-injective proper-acyclicity plan.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

private theorem acyclic_kernel_of_injective
    {C D T : Type*} [Category C] [Category D] [Category T]
    [Abelian C] [Abelian D] [Abelian T] [HasInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (E : D ⥤ T) [E.Additive] [E.PreservesHomology]
    (S : ShortComplex C) (hS : S.ShortExact) [Injective S.X₂]
    (hepi : Epi (E.map (F.map S.g)))
    (hzero : ∀ n : ℕ, IsZero (E.obj ((F.rightDerived (n + 1)).obj S.X₃))) :
    ∀ n : ℕ, IsZero (E.obj ((F.rightDerived (n + 1)).obj S.X₁)) := by
  intro n
  obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hS.exists_rightDerived_δ_exact F n
  have h₂' := h₂.map E
  apply h₂'.isZero_X₂_iff.mpr
  constructor
  · cases n with
    | zero =>
      have hepi' : Epi (E.map ((F.rightDerived 0).map S.g)) := by
        rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf S.g]
        simp only [E.map_comp]
        infer_instance
      have hw : E.map ((F.rightDerived 0).map S.g) ≫ E.map δ = 0 := by
        rw [← E.map_comp, w₁, E.map_zero]
      exact (cancel_epi (E.map ((F.rightDerived 0).map S.g))).1
        (hw.trans (comp_zero).symm)
    | succ n => exact (hzero n).eq_of_src _ _
  · exact (E.map_isZero (F.isZero_rightDerived_obj_injective_succ n S.X₂)).eq_of_tgt _ _

namespace AlgebraicGeometry.Scheme

private theorem injective_clopen_extension
    (A : Type u) [CommRing A] [Finite A]
    {C V : Scheme.{u}} (t : C ⟶ V) [IsOpenImmersion t] [IsClosedImmersion t]
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J] :
    Injective ((sfIntrinsicExtensionByZero t A).obj J) := by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let J₀ := (sfIntrinsicModuleEquivalence C A).inverse.obj J
  have : Injective J₀ := inferInstance
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range Λ t
    t.isClosedEmbedding.isClosed_range
  have : (ProEtale.lowerStar Λ t).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.upperStarLowerStarAdjunction Λ t)
  have hJ₀ : Injective ((ProEtale.openImmersionLowerShriek Λ t).obj J₀) :=
    Injective.of_iso
      (asIso ((ProEtale.openImmersionLowerShriekToLowerStar Λ t).app J₀)).symm
      inferInstance
  exact (sfIntrinsicModuleEquivalence V A).functor.injective_obj_of_injective hJ₀

private theorem cartesian_injective_extension
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r] [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J] :
    ∃ Jv : proEtaleRingModules (pullback p i) (proEtaleConstantRing (pullback p i) A),
      Injective Jv ∧ Nonempty
        ((sfIntrinsicExtensionByZero k A).obj J ≅
          (sfIntrinsicExtensionByZero (pullback.fst p i) A).obj Jv) := by
  let t : C ⟶ pullback p i := pullback.lift k r hcomm
  have ht : t ≫ pullback.fst p i = k := pullback.lift_fst _ _ _
  have hc := ProEtale.StrictTower.squareLift_clopen k r p i hcomm
  have : IsOpenImmersion t := hc.1
  have : IsClosedImmersion t := hc.2
  let Jv := (sfIntrinsicExtensionByZero t A).obj J
  refine ⟨Jv, injective_clopen_extension A t J, ⟨?_⟩⟩
  simpa only [ht, Functor.comp_obj] using
    (sfIntrinsicOpenComp A t (pullback.fst p i)).app J

private theorem evaluation_higherDirectImage
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (W : Y.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (Opposite.op W))) (q : ℤ) :
    IsZero (((SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A)) (Opposite.op W)) ⋙
        forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleConstantDerivedDirectImage f A).obj (DerivedCategory.Q.obj K)))) ↔
      IsZero ((ProEt.ringHypercohomology X
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing X A)) ((proEtaleBaseChange f).obj W) q).obj K) := by
  let RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)
  let RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let F := proEtaleConstantModuleDirectImage f A
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.evaluation.{u + 1} RY (Opposite.op W) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let : (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)).PreservesHomology :=
    ProEt.weaklyContractible_evaluation_preservesHomology Y (proEtaleConstantRing Y A) W hW
  let : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)) :=
    (ProEt.affine_weaklyContractible_evaluation_colimits Y (proEtaleConstantRing Y A) W hW).1
  let : PreservesFiniteLimits E := comp_preservesFiniteLimits
    (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W))
    (forget₂ (ModuleCat.{u + 1} (RY.obj.obj (Opposite.op W))) AddCommGrpCat.{u + 1})
  let : E.PreservesEpimorphisms := by
    dsimp only [E]
    infer_instance
  let : E.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels E
  let I := (ProEt.ringModuleResolutionFunctor RX).obj K
  have : I.IsKInjective := (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).1
  have : QuasiIso (ProEt.ringModuleResolutionMap RX K) :=
    (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).2
  let e := F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map (ProEt.ringModuleResolutionMap RX K))) ≪≫
    F.rightDerivedFunctorObjQIso I
  let h := (DerivedCategory.homologyFunctorFactors _ q).app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let c := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q).mapIso
    (HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by intros; rfl) :
      (E.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
        ((ProEt.ringModuleModelEvaluation RX ((proEtaleBaseChange f).obj W)).mapHomologicalComplex
          (.up ℤ)).obj ((ProEt.ringModuleModelResolutionFunctor RX).obj K))
  let : E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc q) := inferInstance
  exact (E.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫ h) ≪≫
    ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc q).mapHomologyIso E).symm ≪≫ c).isZero_iff

private theorem cartesian_boundary_vanishing_of_closed_injectives
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hepi : ∀ (I : Sheaf (ProEt.topology B)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I],
      Epi (((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology D)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing D A)) (op W))).map
        ((proEtaleConstantModuleDirectImage p A).map
          ((sfIntrinsicModuleEquivalence B A).functor.map
            ((ProEtale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
                (pullback.fst p i).closedComplement).unit.app I)))))
    (hclosed : ∀ (I : Sheaf (ProEt.topology B)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I] (n : ℕ),
      IsZero ((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology D)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing D A)) (op W)).obj
        (((proEtaleConstantModuleDirectImage p A).rightDerived (n + 1)).obj
          ((sfIntrinsicModuleEquivalence B A).functor.obj
            ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (pullback.fst p i).closedComplement).obj
              ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
                (pullback.fst p i).closedComplement).obj I))))))
    (J : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    IsZero ((ProEt.ringHypercohomology B
      ((sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing B A)) ((proEtaleBaseChange p).obj W) (q : ℤ)).obj
            ((CochainComplex.singleFunctor
              (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
                ((sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J))) := by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let b := pullback.fst p i
  let z := b.closedComplement
  let eB := sfIntrinsicModuleEquivalence B A
  let J₀ := (sfIntrinsicModuleEquivalence (pullback p i) A).inverse.obj J
  let L := ProEtale.openImmersionLowerShriek Λ b
  let R := ProEtale.upperStar Λ b
  let F₀ := L.obj J₀
  let I := Injective.under F₀
  let a : F₀ ⟶ I := Injective.ι F₀
  let adj := ProEtale.openImmersionLowerShriekUpperStarAdjunction Λ b
  let α : J₀ ⟶ R.obj I := adj.unit.app J₀ ≫ R.map a
  have : Mono α := by dsimp [α]; infer_instance
  have : Injective J₀ := inferInstance
  let β : R.obj I ⟶ J₀ := Injective.factorThru (𝟙 J₀) α
  have hαβ : α ≫ β = 𝟙 J₀ := Injective.comp_factorThru _ _
  let S₀ := ProEtale.openClosedShortComplex (ULift.{u + 1, u} A) z b
    (by simpa only [z, Scheme.Hom.range_closedComplement] using
      (isCompl_compl : IsCompl (Set.range b) (Set.range b)ᶜ).symm) I
  have hS₀ : S₀.ShortExact := ProEtale.shortExact_openClosedShortComplex z b _ I
  have : Mono S₀.f := hS₀.mono_f
  have : Epi S₀.g := hS₀.epi_g
  let S := S₀.map eB.functor
  have hS : S.ShortExact := hS₀.map eB.functor
  let P := proEtaleConstantModuleDirectImage p A
  let : PreservesFiniteLimits P :=
    (proEtaleConstantModuleDirectImage_additive_leftExact p A).2
  let EV := SheafOfModules.evaluation
    ((sheafCompose (ProEt.topology D)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing D A)) (op W)
  let : EV.Additive := ⟨by intros; rfl⟩
  let : EV.PreservesHomology :=
    ProEt.weaklyContractible_evaluation_preservesHomology D (proEtaleConstantRing D A) W hW
  let : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules B (proEtaleConstantRing B A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology B) (proEtaleConstantRing B A)).1
  have : Injective S.X₂ := inferInstanceAs (Injective (eB.functor.obj I))
  have hz : ∀ n : ℕ, IsZero (EV.obj ((P.rightDerived (n + 1)).obj S.X₁)) :=
    acyclic_kernel_of_injective P EV S hS (hepi I) (hclosed I)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let H := eB.functor ⋙ P.rightDerived (n + 1) ⋙ EV
  let f := H.map (L.map α)
  let g := H.map (L.map β)
  have hfg : f ≫ g = 𝟙 _ := by
    dsimp only [f, g]
    rw [← H.map_comp, ← L.map_comp, hαβ, L.map_id, H.map_id]
  have : Mono f := (IsSplitMono.mk' ⟨g, hfg⟩).mono
  have hfzero : IsZero (H.obj F₀) := IsZero.of_mono f (hz n)
  have hzH := (forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).map_isZero hfzero
  have heval := hzH.of_iso
    ((EV ⋙ forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).mapIso
      (P.homologyRightDerivedFunctorObjSingleFunctorIso
        ((sfIntrinsicExtensionByZero b A).obj J) (n + 1)))
  let K := (CochainComplex.singleFunctor
    (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
      ((sfIntrinsicExtensionByZero b A).obj J)
  have heval' := heval.of_iso
    ((EV ⋙ forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).mapIso
      ((DerivedCategory.homologyFunctor _ ((n + 1 : ℕ) : ℤ)).mapIso
        (P.rightDerivedFunctor.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
            ((sfIntrinsicExtensionByZero b A).obj J)).symm)))
  exact (evaluation_higherDirectImage A p K W hW ((n + 1 : ℕ) : ℤ)).1 heval'

/-- The local cohomology calculation at a boundary-specializing affine test.
The conclusion is a group of derived sections on the proper pullback, not the
vanishing of a higher direct image sheaf or its closed restriction.

Source: the arbitrary-injective boundary step in
`lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction`, Step 2;
parent `lem-sp-proetale-open-injective-proper-acyclic`, Steps 5--7. Stacks
Tag 0F7B supplies the etale analogue, not a pro-etale base-change theorem.
(blueprint: lem-sp-proetale-proper-open-boundary-test-hypercohomology).

Proof plan: Put P = B times_D W, U = C times_D W and E_W = E times_D W.
Restriction along P to B and U to C is weakly etale and preserves injectives.
The open-extension base-change isomorphism identifies the restricted input with
k_W! J_W. The base change of the clopen factor t in the witness identifies U with
a clopen part of P times_W E_W. Compute derived sections using a bounded-below
injective resolution of k_W! J_W on P, rather than a resolution of J_W on U.
The w-contractible evaluation hypothesis makes evaluation at W exact. Use the
finite-principal-open and complementary closed-localization cover of W. Sections
supported in the open have zero restriction on every affine piece specializing
to the closed part; properness keeps the image of a closed support closed. The
injective lifting property of J_W on the clopen open part supplies primitives for
positive cocycles, compatible after refinement, and the zero closed restrictions
allow them to glue across the complementary localization. Hence the positive
cohomology of the section complex is zero. The restriction/injective-resolution
comparison identifies it with the displayed hypercohomology group. This is the
arbitrary-injective calculation still to be proved: no etale-origin witness or
proper base change for arbitrary pro-etale sheaves is assumed. -/
theorem isZero_properOpen_boundary_test_hypercohomology
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (w : OpenProperClopenWitness p r k i)
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((ProEt.ringHypercohomology B
      ((sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing B A)) ((proEtaleBaseChange p).obj W) (q : ℤ)).obj
            ((CochainComplex.singleFunctor
              (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
                ((sfIntrinsicExtensionByZero k A).obj J))) := by
  -- The canonical pullback factorization reconstructs the supplied clopen witness.
  cases w
  obtain ⟨Jv, hJv, ⟨e⟩⟩ := cartesian_injective_extension A p r k i hcomm J
  have := hJv
  have hz := cartesian_boundary_vanishing_of_closed_injectives A p i W hW
    (proper_closed_injective_sections_epi A p i W hW hspecializes)
    (isZero_proper_closed_injective_higherDirectImage A p i W hW hspecializes) Jv q hq
  exact hz.of_iso
    ((ProEt.ringHypercohomology B
      ((sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing B A)) ((proEtaleBaseChange p).obj W) (q : ℤ)).mapIso
      ((CochainComplex.singleFunctor
        (proEtaleRingModules B (proEtaleConstantRing B A)) 0).mapIso e))

end AlgebraicGeometry.Scheme
