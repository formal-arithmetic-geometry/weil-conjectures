/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteModuleLift
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteTensorScalar
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicFromFinite
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Sites.PreservesLimits
import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Galois representations attached to lisse sheaves

Source: Stacks Project, Tag 0DV5; the blueprint, `sec-poincare-duality`,
`sk-lem-finite` (blueprint: cor-galois-lisse-representations);
Deligne, Weil II (1.1.1), (1.1.6).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite ZeroObject
open scoped TensorProduct FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

private noncomputable def galoisUnderlyingStalkIso
    {Y : Scheme.{u}} (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (galoisUnderlyingSetSheaf R F) ≅
      (CategoryTheory.forget (ModuleCat.{u + 1} R)).obj
        (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((pointSmallEtale y).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F

private theorem galoisUnderlyingStalkIso_germ
    {Y : Scheme.{u}} (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj (op U)) :
    (galoisUnderlyingStalkIso R F y).symm.toEquiv
      ((pointSmallEtale y).toPresheafFiber U x F.obj s) =
      (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F).obj s := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have h := congrArg (fun k ↦ k s)
    ((pointSmallEtale y).toPresheafFiber_presheafFiberCompIso_hom_app
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) U x F.obj)
  apply (galoisUnderlyingStalkIso R F y).toEquiv.symm_apply_eq.mpr
  exact h.symm

private theorem galoisLisse_iff_finiteLocallyConstant
    {Y : Scheme.{u}} (R : Type (u + 1)) [Ring R] [Finite R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsLisseModuleSheaf F ↔ IsFiniteLocallyConstantSheaf F := by
  constructor
  · intro hF
    have hU := (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mp hF
    refine { toIsLocallyConstantSheaf := ?_, toIsFiniteSheaf := ?_ }
    · obtain ⟨𝒰, h𝒰⟩ := hF
      exact ⟨⟨⟨𝒰, fun i ↦ by
        obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
        exact Sheaf.isConstant_of_iso _ e⟩⟩⟩
    · refine ⟨fun Ω _ _ y ↦ ?_⟩
      have : Finite (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F)) := hU.finite_sheafFiber Ω y
      have : Finite (((pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R)).obj F) :=
        Finite.of_equiv _ (galoisUnderlyingStalkIso R F y).toEquiv
      exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite)
  · intro hF
    have := hF
    apply (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mpr
    apply isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber
    · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
      refine ⟨d.cover, fun i ↦ ?_⟩
      have := d.isConstant i
      change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
          (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    · intro Ω _ _ y
      have := (ModuleCat.isFinitelyGenerated_iff _).mp
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) Ω y)
      have : Finite (((pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R)).obj F) := Module.finite_of_finite R
      exact Finite.of_equiv _ (galoisUnderlyingStalkIso R F y).toEquiv.symm

private theorem galoisLisse_closedUnderIsomorphisms
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] [Finite R] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsLisseModuleSheaf (Y := Y) (Λ := R)) where
  of_iso e h := by
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp h
    exact (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso e)

private theorem galoisLisse_closedUnderKernels
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] [Finite R] :
    ObjectProperty.IsClosedUnderKernels (IsLisseModuleSheaf (Y := Y) (Λ := R)) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hH⟩
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp hF
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp hH
    have := IsFiniteLocallyConstantSheaf.kernel f
    exact (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso (F := kernel f)
        ((kernelIsKernel f).conePointUniqueUpToIso hk))

private theorem galoisLisse_closedUnderCokernels
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] [Finite R] :
    ObjectProperty.IsClosedUnderCokernels (IsLisseModuleSheaf (Y := Y) (Λ := R)) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hH⟩
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp hF
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp hH
    have := IsFiniteLocallyConstantSheaf.cokernel f
    exact (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso (F := cokernel f)
        ((cokernelIsCokernel f).coconePointUniqueUpToIso hk))

private theorem galoisLisse_abelian
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] [Finite R] :
    Nonempty (Abelian (LisseModuleSheafCategory Y R)) := by
  let P : ObjectProperty (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsLisseModuleSheaf
  have : P.IsClosedUnderIsomorphisms := galoisLisse_closedUnderIsomorphisms Y R
  have : P.IsClosedUnderKernels := galoisLisse_closedUnderKernels Y R
  have : P.IsClosedUnderCokernels := galoisLisse_closedUnderCokernels Y R
  have : P.ContainsZero := ⟨⟨0, isZero_zero _,
    (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _))⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp (hD ⟨.left⟩)
    have := (galoisLisse_iff_finiteLocallyConstant R _).mp (hD ⟨.right⟩)
    have := IsFiniteLocallyConstantSheaf.biprod (D.obj ⟨.left⟩) (D.obj ⟨.right⟩)
    exact (galoisLisse_iff_finiteLocallyConstant R _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso ((biprod.isoProd _ _) ≪≫
        (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact ⟨inferInstanceAs (Abelian P.FullSubcategory)⟩

private theorem galoisFiniteEtaleComparison
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace Y]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (α : Φ.functor ⋙ E.functor ≅ (FiniteEtale.equivalenceContAction y G).functor)
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (hτ : ∀ (F : Y.FLC) (g : G) (z : ULift.{u + 1} (E.functor.obj F).obj.V),
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ g).hom.app F (τ.hom.app F z)) :
    ∃ η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
        (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
        FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u},
      ∀ (P : Y.FiniteEtale) (g : G) (z : ((pointSmallEtale y).sheafFiber
          (A := Type (u + 1))).obj (Φ.functor.obj P).obj),
        η.hom.app P ((γ g).hom.app (Φ.functor.obj P) z) =
          ⟨g • (η.hom.app P z).down⟩ := by
  let B := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
    CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  let η := Functor.isoWhiskerLeft Φ.functor τ.symm ≪≫
    (Functor.associator Φ.functor E.functor B).symm ≪≫ Functor.isoWhiskerRight α B
  refine ⟨η, ?_⟩
  intro P g z
  have hinv (F : Y.FLC) (w) : τ.hom.app F (τ.inv.app F w) = w :=
    ConcreteCategory.congr_hom (τ.inv_hom_id_app F) w
  have he : τ.inv.app (Φ.functor.obj P) ((γ g).hom.app (Φ.functor.obj P) z) =
      ⟨((E.functor.obj (Φ.functor.obj P)).obj.ρ g).hom
        (τ.inv.app (Φ.functor.obj P) z).down⟩ := by
    apply (τ.app (Φ.functor.obj P)).toEquiv.injective
    change τ.hom.app _ (τ.inv.app _ _) = τ.hom.app _ _
    rw [hinv, hτ, hinv]
  change ULift.up ((α.hom.app P).hom.hom
      (τ.inv.app (Φ.functor.obj P) ((γ g).hom.app (Φ.functor.obj P) z)).down) = _
  rw [he]
  apply congrArg ULift.up
  exact ConcreteCategory.congr_hom ((α.hom.app P).hom.comm g)
    (τ.inv.app (Φ.functor.obj P) z).down

private theorem galoisConstantModule_lisse (Y : Scheme.{u})
    (R : Type (u + 1)) [Ring R] [Finite R] (M : ModuleCat.{u + 1} R) [Finite M] :
    IsLisseModuleSheaf ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  apply (galoisLisse_iff_finiteLocallyConstant R _).mpr
  refine { toIsLocallyConstantSheaf := ?_, toIsFiniteSheaf := ?_ }
  · exact Sheaf.IsConstant.isLocallyConstantSheaf (Sheaf.isConstant_of_iso _ (Iso.refl _))
  · refine ⟨fun Ω _ _ y ↦ ?_⟩
    let : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := (pointSmallEtale y).sheafFiberConstantSheafIso
      (J := Y.smallEtaleTopology) M
    apply (ModuleCat.isFinitelyGenerated_iff _).mpr
    have : Module.Finite R M := Module.Finite.of_finite
    exact Module.Finite.equiv e.symm.toLinearEquiv

private theorem galoisLisseTensorStructure (Y : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R] :
    ∃ (m : MonoidalCategory (LisseModuleSheafCategory Y R))
      (b : @BraidedCategory (LisseModuleSheafCategory Y R) _ m),
      Nonempty (@Functor.Braided (LisseModuleSheafCategory Y R) _ m b
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) _
        (Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (Sheaf.braidedCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (ObjectProperty.ι _)) := by
  let :=  Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let :=  Sheaf.braidedCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let P : ObjectProperty (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsLisseModuleSheaf
  let : P.IsMonoidal :=
    { prop_unit := galoisConstantModule_lisse Y R (ModuleCat.of R R)
      prop_tensor := fun F H hF hH ↦
        (galoisLisse_iff_finiteLocallyConstant R _).mpr
          (lisse_tensor_and_scalar_extension F H
            ((galoisLisse_iff_finiteLocallyConstant R _).mp hF)
            ((galoisLisse_iff_finiteLocallyConstant R _).mp hH)) }
  exact ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩

private theorem galois_constant_action_trivial
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R] [Finite R]
    (M : ModuleCat.{u + 1} R) [Finite M]
    (σ : Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)))) :
    let C := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
    ∀ (h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R C))
      (z : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (galoisUnderlyingSetSheaf R C)),
      σ.hom.app (galoisUnderlyingFLC R C h) z = z := by
  classical
  dsimp only
  let p := pointSmallEtale y
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let C := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  let Z := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R PUnit.{u + 2})
  have hZ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R Z) :=
    (lisseModuleSheaf_iff_underlying_finiteLocallyConstant Z).mp
      (galoisConstantModule_lisse Y R _)
  let EZ := (galoisUnderlyingStalkIso R Z y) ≪≫
    (CategoryTheory.forget (ModuleCat.{u + 1} R)).mapIso
      (p.sheafFiberConstantSheafIso (J := Y.smallEtaleTopology)
        (ModuleCat.of R PUnit.{u + 2}))
  let z₀ := EZ.inv PUnit.unit
  have hz₀ : σ.hom.app (galoisUnderlyingFLC R Z hZ) z₀ = z₀ := by
    apply EZ.toEquiv.injective
    exact Subsingleton.elim _ _
  intro h z
  let a := (p.sheafFiberConstantSheafIso (J := Y.smallEtaleTopology) M).hom
    ((galoisUnderlyingStalkIso R C y).hom z)
  let j := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let f : galoisUnderlyingFLC R Z hZ ⟶ galoisUnderlyingFLC R C h :=
    ObjectProperty.homMk
      { hom :=
          { app := fun U ↦ TypeCat.ofHom (fun _ ↦ j.app U a)
            naturality := fun U V f ↦ by
              apply ConcreteCategory.hom_ext
              intro s
              exact congrArg (fun k ↦ k a) (j.naturality f) } }
  have hf : ((ObjectProperty.ι _ ⋙ p.sheafFiber).map f) z₀ = z := by
    obtain ⟨U, x, s, hs⟩ := p.toPresheafFiber_jointly_surjective
      (P := (galoisUnderlyingSetSheaf R Z).obj) z₀
    rw [← hs]
    have hn := congrArg (fun k ↦ k s) (p.toPresheafFiber_naturality f.hom.hom U x)
    change p.presheafFiber.map f.hom.hom
      (p.toPresheafFiber U x (galoisUnderlyingSetSheaf R Z).obj s) = _
    change p.presheafFiber.map f.hom.hom
        (p.toPresheafFiber U x (galoisUnderlyingSetSheaf R Z).obj s) =
      p.toPresheafFiber U x (galoisUnderlyingSetSheaf R C).obj (j.app (op U) a) at hn
    refine hn.trans ?_
    change p.toPresheafFiber U x (galoisUnderlyingSetSheaf R C).obj (j.app (op U) a) = z
    apply (galoisUnderlyingStalkIso R C y).toEquiv.injective
    have hc := congrArg (fun k ↦ k (j.app (op U) a))
      (p.toPresheafFiber_presheafFiberCompIso_hom_app
        (CategoryTheory.forget (ModuleCat.{u + 1} R)) U x C.obj)
    change (galoisUnderlyingStalkIso R C y).hom
      (p.toPresheafFiber U x (galoisUnderlyingSetSheaf R C).obj (j.app (op U) a)) = _
    change (galoisUnderlyingStalkIso R C y).hom
        (p.toPresheafFiber U x (galoisUnderlyingSetSheaf R C).obj (j.app (op U) a)) =
      p.toPresheafFiber U x C.obj (j.app (op U) a) at hc
    rw [hc]
    apply (p.sheafFiberConstantSheafIso (J := Y.smallEtaleTopology) M).toLinearEquiv.injective
    have hj := congrArg (fun k ↦ k a) (p.toPresheafFiber_naturality j U x)
    change p.presheafFiber.map j
        (p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) a) =
      p.toPresheafFiber U x C.obj (j.app (op U) a) at hj
    rw [← hj]
    change (p.presheafFiberConstIso M).hom
      ((inv (p.presheafFiber.map j)) ((p.presheafFiber.map j)
        (p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) a))) = a
    have hi := ConcreteCategory.congr_hom (IsIso.hom_inv_id (p.presheafFiber.map j))
      (p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) a)
    change (inv (p.presheafFiber.map j)) ((p.presheafFiber.map j)
        (p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) a)) =
      p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) a at hi
    rw [hi]
    exact congrArg (fun k ↦ k a)
      (p.toPresheafFiber_presheafFiberConstIso_hom M U x)
  have hn := congrArg (fun k ↦ k z₀) (σ.hom.naturality f)
  symm at hn
  change ((ObjectProperty.ι _ ⋙ p.sheafFiber).map f)
      (σ.hom.app (galoisUnderlyingFLC R Z hZ) z₀) =
    σ.hom.app (galoisUnderlyingFLC R C h)
      (((ObjectProperty.ι _ ⋙ p.sheafFiber).map f) z₀) at hn
  rw [hz₀, hf] at hn
  exact hn.symm


private theorem galoisFiniteUnit_of_evaluation
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) (heval : galoisFiniteEvaluationAction y G d) :
    galoisFiniteUnit y G d := by
  classical
  intro R _ _
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let C : LisseModuleSheafCategory Y R :=
    ⟨(constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R),
      galoisConstantModule_lisse Y R (ModuleCat.of R R)⟩
  obtain ⟨h, κ, _, hκ⟩ := heval R C
  have hrho (g : G) (z : ((d.e R).functor.obj C).obj.V) :
      ((d.e R).functor.obj C).obj.ρ g z = z := by
    apply ((d.τ R).app C).toLinearEquiv.injective
    apply κ.injective
    exact (hκ g z).trans (galois_constant_action_trivial y R (ModuleCat.of R R)
      (d.γ g) h _)
  let e := ((d.τ R).app C ≪≫
    (pointSmallEtale y).sheafFiberConstantSheafIso (J := Y.smallEtaleTopology)
      (ModuleCat.of R R)).toLinearEquiv
  refine ⟨C, rfl, ⟨Rep.mkIso { e with isIntertwining' := ?_ }⟩⟩
  intro g
  ext z
  change e (((d.e R).functor.obj C).obj.ρ g z) = e z
  rw [hrho]


private theorem galoisFiniteEtale_preservesFiniteLimits (Y : Scheme.{u}) : PreservesFiniteLimits
    (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).HasOfPostcompProperty
      (@IsFinite ⊓ @Etale) := by
    refine ⟨fun {X Y Z} f g hg hfg ↦ ?_⟩
    have := hg.1; have := hg.2; have := hfg.1; have := hfg.2
    exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩
  let H := MorphismProperty.Over.changeProp (Q := ⊤) (Q' := ⊤) Y
    (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale) le_rfl
  have : PreservesFiniteLimits H :=
    MorphismProperty.Over.preservesFiniteLimits_changeProp Y
      (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale)
  have : PreservesFiniteLimits (FiniteEtale.toFiniteEtaleOver Y ⋙ H) := inferInstance
  exact this

private theorem galoisFLC_preservesFiniteLimits
    {Y : Scheme.{u}}
    (Φ : Y.FiniteEtale ≌ Y.FLC)
    (hΦ : Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1})) :
    PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))) := by
  obtain ⟨α⟩ := hΦ
  let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let : PreservesFiniteLimits
      (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) :=
    galoisFiniteEtale_preservesFiniteLimits Y
  let : PreservesFiniteLimits Y.smallEtaleTopology.uliftYoneda.{u + 1} :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits (Φ.functor ⋙ I) :=
    preservesFiniteLimits_of_natIso α.symm
  let e : Φ.inverse ⋙ (Φ.functor ⋙ I) ≅ I :=
    (Functor.associator Φ.inverse Φ.functor I).symm ≪≫
      Functor.isoWhiskerRight Φ.counitIso I ≪≫ Functor.leftUnitor I
  exact preservesFiniteLimits_of_natIso e


private def galoisFiniteCarrierLift (R : Type (u + 1)) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    FiniteContinuousModule.{u + 1, u, u} R G ⥤ galoisFiniteRepresentations R G := by
  let F : FiniteContinuousModule.{u + 1, u, u} R G ⥤ Rep.{u + 1} R G :=
    ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction R G ⋙
      (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G ⋙ Rep.ActionToRep R G
  refine ObjectProperty.lift _ F ?_
  intro X
  have : Finite X.obj.obj.V := X.property
  refine ⟨?_, ?_⟩
  · change Finite (ULift.{u + 1} X.obj.obj.V)
    infer_instance
  · intro z
    change IsOpen {g : G | ULift.up (X.obj.obj.ρ g z.down) = z}
    simpa only [ULift.ext_iff, ULift.up_down] using X.obj.property z.down

private theorem galoisFiniteCarrierLift_isEquivalence
    (R : Type (u + 1)) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (galoisFiniteCarrierLift R G).IsEquivalence := by
  classical
  let F := galoisFiniteCarrierLift R G
  let H : FiniteContinuousModule.{u + 1, u, u} R G ⥤ Rep.{u + 1} R G :=
    ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction R G ⋙
      (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G ⋙ Rep.ActionToRep R G
  let hH : H.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp
      ((ObjectProperty.fullyFaithfulι _).comp
        ((Rep.repIsoAction R G).fullyFaithfulFunctor.comp
          (((ModuleCat.fullyFaithfulUliftFunctor.{u + 1, u} R).mapAction G).comp
            (Rep.repIsoAction R G).fullyFaithfulInverse)))
  have : H.Full := hH.full
  have : H.Faithful := hH.faithful
  let : F.Full := by
    change (ObjectProperty.lift _ H _).Full
    infer_instance
  let : F.Faithful := by
    change (ObjectProperty.lift _ H _).Faithful
    infer_instance
  let : F.EssSurj := ⟨fun X ↦ by
    have : Finite X.obj.V := X.property.1
    let : Small.{u} X.obj.V := inferInstance
    let e : Shrink.{u} X.obj.V ≃ₗ[R] X.obj.V := Shrink.linearEquiv R X.obj.V
    let ρ : Representation R G (Shrink.{u} X.obj.V) :=
      { toFun := fun g ↦ e.symm.toLinearMap ∘ₗ (X.obj.ρ g) ∘ₗ e.toLinearMap
        map_one' := by
          apply LinearMap.ext
          intro z
          change e.symm (X.obj.ρ 1 (e z)) = z
          rw [X.obj.ρ.map_one]
          exact e.symm_apply_apply z
        map_mul' := fun g h ↦ by
          apply LinearMap.ext
          intro z
          change e.symm (X.obj.ρ (g * h) (e z)) =
            e.symm (X.obj.ρ g (e (e.symm (X.obj.ρ h (e z)))))
          rw [e.apply_symm_apply, X.obj.ρ.map_mul]
          rfl }
    let A : FiniteContinuousModule.{u + 1, u, u} R G :=
      ⟨⟨Rep.of ρ, fun z ↦ by
        change IsOpen {g : G | e.symm (X.obj.ρ g (e z)) = z}
        simpa only [e.symm_apply_eq] using X.property.2 (e z)⟩, inferInstance⟩
    refine ⟨A, ⟨ObjectProperty.isoMk _ (Rep.mkIso
      { (ULift.moduleEquiv.trans e) with isIntertwining' := ?_ })⟩⟩
    intro g
    ext z
    change e (e.symm (X.obj.ρ g (e z.down))) = X.obj.ρ g (e z.down)
    exact e.apply_symm_apply _⟩
  exact {}


private theorem galoisFiniteCarrierComparison
    (R : Type (u + 1)) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ ε : FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G,
      Nonempty (ε.functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G) := by
  let : (galoisFiniteCarrierLift R G).IsEquivalence :=
    galoisFiniteCarrierLift_isEquivalence R G
  refine ⟨(galoisFiniteCarrierLift R G).asEquivalence, ⟨?_⟩⟩
  let H : FiniteContinuousModule.{u + 1, u, u} R G ⥤ Action (ModuleCat.{u + 1} R) G :=
    ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
      (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G
  change (H ⋙ (Rep.repIsoAction R G).inverse) ⋙ (Rep.repIsoAction R G).functor ≅ H
  exact Functor.associator H _ _ ≪≫
    Functor.isoWhiskerLeft H (Rep.repIsoAction R G).counitIso ≪≫ Functor.rightUnitor H


section ModuleObjectBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def galoisModuleObjectInternal
    {Y : Scheme.{u}} {R : Type (u + 1)} [Ring R]
    {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (S : ModuleObjectStruct R A) :
    InternalModule R (Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  X := A
  add := S.add
  zero := S.zero
  neg := S.neg
  smul := S.smul
  add_assoc T a b c := by
    have h := congrArg (fun f ↦ prod.lift (prod.lift a b) c ≫ f) S.add_assoc
    simpa [← Category.assoc] using h
  zero_add T a := by
    have h := congrArg (fun f ↦ a ≫ f) S.zero_add
    simpa [← Category.assoc] using h
  add_zero T a := by
    have hc := congrArg (fun f ↦ prod.lift a (terminal.from T ≫ S.zero) ≫ f) S.add_comm
    have hz := congrArg (fun f ↦ a ≫ f) S.zero_add
    simpa [← Category.assoc] using hc.symm.trans (by simpa [← Category.assoc] using hz)
  neg_add T a := by
    have h := congrArg (fun f ↦ a ≫ f) S.neg_add_cancel
    simpa [← Category.assoc] using h
  add_comm T a b := by
    have h := congrArg (fun f ↦ prod.lift b a ≫ f) S.add_comm
    simpa [← Category.assoc] using h
  one_smul := S.one_smul
  mul_smul := S.mul_smul
  smul_add r T a b := by
    have h := congrArg (fun f ↦ prod.lift a b ≫ f) (S.smul_add r)
    simpa [← Category.assoc] using h
  add_smul r s T a := by
    have h := congrArg (fun f ↦ a ≫ f) (S.add_smul r s)
    simpa [← Category.assoc] using h
  zero_smul := S.zero_smul
  smul_zero := S.smul_zero

private abbrev galoisModuleObjectSets {Y : Scheme.{u}} {R : Type (u + 1)} [Ring R]
    (A : LambdaModuleObject Y R) : Y.FLC := ⟨A.sheaf, A.isFLC⟩

private noncomputable abbrev galoisModuleObjectRestrict
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {R : Type (u + 1)} [Ring R] (A : LambdaModuleObject Y R) :
    InternalModule R Y.FLC := by
  let I : Y.FLC ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
    ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let X := galoisModuleObjectSets A
  let S := galoisModuleObjectInternal A.str
  let add : X ⨯ X ⟶ X := I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add)
  let zero : ⊤_ Y.FLC ⟶ X := I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero)
  let neg : X ⟶ X := I.preimage (X := X) (Y := X) A.str.neg
  let smul : R → (X ⟶ X) := fun r ↦ I.preimage (X := X) (Y := X) (A.str.smul r)
  have hadd {T : Y.FLC} (a b : T ⟶ X) :
      I.map (prod.lift a b ≫ add) = prod.lift (I.map a) (I.map b) ≫ A.str.add := by
    rw [I.map_comp, I.map_preimage, ← Category.assoc]
    congr 1
    apply prod.hom_ext <;> simp [prodComparison, ← I.map_comp]
  have hzero (T : Y.FLC) :
      I.map (terminal.from T ≫ zero) = terminal.from (I.obj T) ≫ A.str.zero := by
    rw [I.map_comp, I.map_preimage, ← Category.assoc]
    congr 1
    exact terminal.hom_ext _ _
  refine
    { X := X
      add := add
      zero := zero
      neg := neg
      smul := smul
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add := ?_
      add_comm := ?_
      one_smul := ?_
      mul_smul := ?_
      smul_add := ?_
      add_smul := ?_
      zero_smul := ?_
      smul_zero := ?_ }
  · intro T a b c
    apply I.map_injective
    simp only [hadd]
    exact S.add_assoc (I.obj T) (I.map a) (I.map b) (I.map c)
  · intro T a
    apply I.map_injective
    rw [hadd, hzero]
    exact S.zero_add (I.obj T) (I.map a)
  · intro T a
    apply I.map_injective
    rw [hadd, hzero]
    exact S.add_zero (I.obj T) (I.map a)
  · intro T a
    apply I.map_injective
    rw [hadd, hzero, I.map_comp]
    simp only [neg, I.map_preimage]
    exact S.neg_add (I.obj T) (I.map a)
  · intro T a b
    apply I.map_injective
    rw [hadd, hadd]
    exact S.add_comm (I.obj T) (I.map a) (I.map b)
  · apply I.map_injective
    simp only [smul, I.map_preimage, I.map_id]
    exact A.str.one_smul
  · intro r s
    apply I.map_injective
    simp only [smul, I.map_comp, I.map_preimage]
    exact A.str.mul_smul r s
  · intro r T a b
    apply I.map_injective
    rw [← Category.assoc, I.map_comp, hadd, hadd, I.map_comp, I.map_comp]
    simp only [smul, I.map_preimage]
    exact S.smul_add r (I.obj T) (I.map a) (I.map b)
  · intro r s T a
    apply I.map_injective
    rw [I.map_comp, hadd, I.map_comp, I.map_comp]
    simp only [smul, I.map_preimage]
    exact S.add_smul r s (I.obj T) (I.map a)
  · apply I.map_injective
    simp only [smul, I.map_preimage]
    rw [hzero]
    exact A.str.zero_smul
  · intro r
    apply I.map_injective
    simp only [zero, smul, I.map_comp, I.map_preimage, Category.assoc]
    rw [A.str.smul_zero]

private noncomputable abbrev galoisInternalAmbient
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {R : Type (u + 1)} [Ring R] (A : InternalModule R Y.FLC) :
    ModuleObjectStruct R A.X.obj := by
  let I : Y.FLC ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
    ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let X := A.X
  let add := inv (prodComparison I X X) ≫ I.map A.add
  let zero := inv (terminalComparison I) ≫ I.map A.zero
  let neg := I.map A.neg
  let smul := fun r ↦ I.map (A.smul r)
  have hpair {T : Y.FLC} (a b : T ⟶ X) :
      prod.lift (I.map a) (I.map b) ≫ inv (prodComparison I X X) =
        I.map (prod.lift a b) := by
    apply (cancel_mono (prodComparison I X X)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply prod.hom_ext <;> simp [prodComparison, ← I.map_comp]
  have hadd {T : Y.FLC} (a b : T ⟶ X) :
      prod.lift (I.map a) (I.map b) ≫ add = I.map (prod.lift a b ≫ A.add) := by
    rw [← Category.assoc, hpair, I.map_comp]
  have hzero (T : Y.FLC) :
      terminal.from (I.obj T) ≫ zero = I.map (terminal.from T ≫ A.zero) := by
    rw [← Category.assoc, I.map_comp]
    congr 1
    apply (cancel_mono (terminalComparison I)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact terminal.hom_ext _ _
  change ModuleObjectStruct R (I.obj X)
  refine
    { add := add
      zero := zero
      neg := neg
      smul := smul
      add_assoc := ?_
      add_comm := ?_
      zero_add := ?_
      neg_add_cancel := ?_
      one_smul := ?_
      mul_smul := ?_
      smul_add := ?_
      add_smul := ?_
      smul_zero := ?_
      zero_smul := ?_ }
  · let k := prodComparison I (X ⨯ X) X ≫
      prod.map (prodComparison I X X) (𝟙 (I.obj X))
    have hk : IsIso k := by dsimp [k]; infer_instance
    apply (cancel_epi k).1
    have hk' : k = prod.lift
        (prod.lift (I.map (prod.fst ≫ prod.fst)) (I.map (prod.fst ≫ prod.snd)))
        (I.map (prod.snd : (X ⨯ X) ⨯ X ⟶ X)) := by
      apply prod.hom_ext
      · apply prod.hom_ext <;>
          simp only [k, prodComparison, prod.comp_lift, prod.map_fst, prod.lift_fst,
            prod.lift_snd, Category.assoc, prod.lift_fst_assoc, ← I.map_comp]
      · simp [k, prodComparison]
    rw [hk']
    simp only [prod.associator_hom, prod.comp_lift, prod.lift_fst,
      prod.lift_snd, prod.lift_map, Category.comp_id, ← Category.assoc]
    simp only [hadd]
    exact congrArg I.map (A.add_assoc _ (prod.fst ≫ prod.fst)
      (prod.fst ≫ prod.snd) prod.snd)
  · apply (cancel_epi (prodComparison I X X)).1
    have hp : prodComparison I X X = prod.lift
        (I.map (prod.fst : X ⨯ X ⟶ X)) (I.map (prod.snd : X ⨯ X ⟶ X)) := rfl
    rw [hp]
    simp only [prod.braiding_hom, ← Category.assoc, prod.comp_lift, prod.lift_fst, prod.lift_snd]
    rw [hadd, hadd]
    exact congrArg I.map (A.add_comm _ prod.snd prod.fst)
  · have h := congrArg I.map (A.zero_add X (𝟙 X))
    simp only [I.map_id] at h
    have hp := hadd (terminal.from X ≫ A.zero) (𝟙 X)
    simpa only [I.map_id, ← hzero] using hp.trans h
  · change prod.lift (I.map A.neg) (𝟙 (I.obj X)) ≫ add =
      terminal.from (I.obj X) ≫ zero
    rw [← I.map_id X, hadd, hzero]
    exact congrArg I.map (by simpa only [Category.id_comp] using A.neg_add X (𝟙 X))
  · change I.map (A.smul 1) = I.map (𝟙 A.X)
    exact congrArg I.map A.one_smul
  · intro r s
    simpa [smul] using congrArg I.map (A.mul_smul r s)
  · intro r
    apply (cancel_epi (prodComparison I X X)).1
    change prodComparison I X X ≫ add ≫ smul r = _
    have hp : prodComparison I X X = prod.lift
        (I.map (prod.fst : X ⨯ X ⟶ X)) (I.map (prod.snd : X ⨯ X ⟶ X)) := rfl
    rw [hp]
    simp only [← Category.assoc, prod.lift_map]
    simp only [smul, ← I.map_comp, hadd]
    exact congrArg I.map (A.smul_add r _ prod.fst prod.snd)
  · intro r s
    have h := congrArg I.map (A.add_smul r s X (𝟙 X))
    simp only [Category.id_comp] at h
    simpa only [smul, hadd, ← I.map_comp] using h
  · intro r
    dsimp only [zero, smul]
    rw [Category.assoc, ← I.map_comp, A.smul_zero]
  · simpa only [smul, ← hzero] using congrArg I.map A.zero_smul

private theorem galoisModuleObjectRestrict_isHom
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {R : Type (u + 1)} [Ring R] (A B : LambdaModuleObject Y R)
    (f : galoisModuleObjectSets A ⟶ galoisModuleObjectSets B) :
    InternalModule.IsHom (galoisModuleObjectRestrict A) (galoisModuleObjectRestrict B) f ↔
      A.str.add ≫ f.hom = prod.map f.hom f.hom ≫ B.str.add ∧
      A.str.zero ≫ f.hom = B.str.zero ∧ A.str.neg ≫ f.hom = f.hom ≫ B.str.neg ∧
      ∀ r, A.str.smul r ≫ f.hom = f.hom ≫ B.str.smul r := by
  let I : Y.FLC ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
    ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let X := galoisModuleObjectSets A
  let Z := galoisModuleObjectSets B
  have hf : I.map f = f.hom := rfl
  have hp := prodComparison_natural I f f
  change
    (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add) ≫ f =
      prod.map f f ≫ I.preimage (X := Z ⨯ Z) (Y := Z) (prodComparison I Z Z ≫ B.str.add)) ∧
    (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero) ≫ f =
      I.preimage (X := ⊤_ Y.FLC) (Y := Z) (terminalComparison I ≫ B.str.zero)) ∧
    (I.preimage (X := X) (Y := X) A.str.neg ≫ f = f ≫ I.preimage (X := Z) (Y := Z) B.str.neg) ∧
    (∀ r, I.preimage (X := X) (Y := X) (A.str.smul r) ≫ f =
      f ≫ I.preimage (X := Z) (Y := Z) (B.str.smul r)) ↔ _
  have hadd :
      (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add) ≫ f =
        prod.map f f ≫ I.preimage (X := Z ⨯ Z) (Y := Z) (prodComparison I Z Z ≫ B.str.add)) ↔
        A.str.add ≫ f.hom = prod.map f.hom f.hom ≫ B.str.add := by
    constructor
    · intro h
      apply (cancel_epi (prodComparison I X X)).1
      have h' := congrArg I.map h
      simp only [I.map_comp, I.map_preimage] at h'
      rw [← Category.assoc, hp, Category.assoc, hf] at h'
      simpa only [Category.assoc] using h'
    · intro h
      apply I.map_injective
      simp only [I.map_comp, I.map_preimage]
      rw [← Category.assoc, hp, Category.assoc, hf]
      simpa only [Category.assoc] using congrArg (fun k ↦ prodComparison I X X ≫ k) h
  have hzero :
      (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero) ≫ f =
        I.preimage (X := ⊤_ Y.FLC) (Y := Z) (terminalComparison I ≫ B.str.zero)) ↔
        A.str.zero ≫ f.hom = B.str.zero := by
    constructor
    · intro h
      apply (cancel_epi (terminalComparison I)).1
      simpa only [I.map_comp, I.map_preimage, Category.assoc, hf] using congrArg I.map h
    · intro h
      apply I.map_injective
      simpa only [I.map_comp, I.map_preimage, Category.assoc, hf] using
        congrArg (fun k ↦ terminalComparison I ≫ k) h
  have hneg : (I.preimage (X := X) (Y := X) A.str.neg ≫ f =
      f ≫ I.preimage (X := Z) (Y := Z) B.str.neg) ↔
      A.str.neg ≫ f.hom = f.hom ≫ B.str.neg := by
    constructor
    · intro h
      simpa only [I.map_comp, I.map_preimage, hf] using congrArg I.map h
    · intro h
      apply I.map_injective
      simpa only [I.map_comp, I.map_preimage, hf] using h
  have hsmul (r : R) :
      (I.preimage (X := X) (Y := X) (A.str.smul r) ≫ f =
        f ≫ I.preimage (X := Z) (Y := Z) (B.str.smul r)) ↔
        A.str.smul r ≫ f.hom = f.hom ≫ B.str.smul r := by
    constructor
    · intro h
      simpa only [I.map_comp, I.map_preimage, hf] using congrArg I.map h
    · intro h
      apply I.map_injective
      simpa only [I.map_comp, I.map_preimage, hf] using h
  exact and_congr hadd (and_congr hzero (and_congr hneg (forall_congr' hsmul)))

private noncomputable abbrev galoisModuleObjectFunctor
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (R : Type (u + 1)) [Ring R] :
    LambdaModuleObject Y R ⥤ InternalModule R Y.FLC where
  obj := galoisModuleObjectRestrict
  map f := ⟨ObjectProperty.homMk f.hom,
    (galoisModuleObjectRestrict_isHom _ _ _).2 ⟨f.add, f.zero, f.neg, f.smul⟩⟩
  map_id _ := Subtype.ext (ObjectProperty.hom_ext _ rfl)
  map_comp _ _ := Subtype.ext (ObjectProperty.hom_ext _ rfl)

private noncomputable def galoisModuleObjectFunctor_fullyFaithful
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (R : Type (u + 1)) [Ring R] : (galoisModuleObjectFunctor (Y := Y) R).FullyFaithful where
  preimage {A B} f :=
    let h := (galoisModuleObjectRestrict_isHom A B f.val).1 f.property
    ⟨f.val.hom, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  map_preimage _ := Subtype.ext (ObjectProperty.hom_ext _ rfl)
  preimage_map _ := LambdaModuleObject.Hom.ext rfl

private theorem galoisInternal_ext
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    {R : Type (u + 1)} [Ring R] (A B : InternalModule R Y.FLC)
    (hX : A.X = B.X) (ha : HEq A.add B.add) (hz : HEq A.zero B.zero)
    (hn : HEq A.neg B.neg) (hs : HEq A.smul B.smul) : A = B := by
  cases A
  cases B
  cases hX
  cases ha
  cases hz
  cases hn
  cases hs
  rfl

private theorem galoisModuleObjectFunctor_essSurj
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (R : Type (u + 1)) [Ring R] : (galoisModuleObjectFunctor (Y := Y) R).EssSurj := by
  refine ⟨fun A ↦ ?_⟩
  let B : LambdaModuleObject Y R := ⟨A.X.obj, A.X.property, galoisInternalAmbient A⟩
  have h : galoisModuleObjectRestrict B = A := by
    let I : Y.FLC ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
      ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
    apply galoisInternal_ext (galoisModuleObjectRestrict B) A rfl
    · apply heq_of_eq
      apply I.map_injective
      change I.map (I.preimage (prodComparison I A.X A.X ≫
        (inv (prodComparison I A.X A.X) ≫ I.map A.add))) = I.map A.add
      simp
    · apply heq_of_eq
      apply I.map_injective
      change I.map (I.preimage (terminalComparison I ≫
        (inv (terminalComparison I) ≫ I.map A.zero))) = I.map A.zero
      simp
    · apply heq_of_eq
      apply I.map_injective
      change I.map (I.preimage (I.map A.neg)) = I.map A.neg
      simp
    · apply heq_of_eq
      funext r
      apply I.map_injective
      change I.map (I.preimage (I.map (A.smul r))) = I.map (A.smul r)
      simp
  exact ⟨B, ⟨eqToIso h⟩⟩
private noncomputable def galoisModuleObjectEquivalence
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (R : Type (u + 1)) [Ring R] : LambdaModuleObject Y R ≌ InternalModule R Y.FLC := by
  let F := galoisModuleObjectFunctor (Y := Y) R
  let : F.Full := (galoisModuleObjectFunctor_fullyFaithful R).full
  let : F.Faithful := (galoisModuleObjectFunctor_fullyFaithful R).faithful
  let : F.EssSurj := galoisModuleObjectFunctor_essSurj R
  let : F.IsEquivalence := {}
  exact F.asEquivalence

end ModuleObjectBridge

section ScalarComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def galoisSheafScalarComp
    (Y : Scheme.{u}) {R S T : Type (u + 1)} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f ⋙
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g ≅
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (g.comp f) := by
  let J := Y.smallEtaleTopology
  let E₁ := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let E₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g).isLeftAdjoint
  let W₁ := (Functor.whiskeringRight Y.Etaleᵒᵖ _ _).obj E₁
  let W₂ := (Functor.whiskeringRight Y.Etaleᵒᵖ _ _).obj E₂
  let H := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ W₁
  let k := Functor.whiskerRight
    (Functor.whiskerLeft H (toSheafification J (ModuleCat.{u + 1} S)))
    (W₂ ⋙ presheafToSheaf J (ModuleCat.{u + 1} T))
  have hk (F : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (k.app F) := by
    change IsIso ((presheafToSheaf J (ModuleCat.{u + 1} T)).map
      (Functor.whiskerRight (toSheafify J (F.obj ⋙ E₁)) E₂))
    apply (J.W_iff _).mp
    exact J.W_of_preservesSheafification E₂ _ (J.W_toSheafify _)
  let : IsIso k := NatIso.isIso_of_isIso_app k
  let a := ModuleCat.ringExtensionComp.{u + 1, u + 1} f g
  let j := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u + 1} R))
      ((Functor.whiskeringRight Y.Etaleᵒᵖ _ _).mapIso a))
    (presheafToSheaf J (ModuleCat.{u + 1} T))
  exact (asIso k).symm ≪≫ j

private theorem galoisScalarMapTmul {R S : Type (u + 1)} [Ring R] [Ring S]
    (f : R →+* S)
    {M N : ModuleCat.{u + 1} R} (φ : M ⟶ N) (b : S) (m : M) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).map φ
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f M b m) =
      ModuleCat.ringExtensionTmul.{u + 1, u + 1} f N b (φ m) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  have h := congrArg (fun k ↦ k m) (adj.unit.naturality φ)
  change adj.unit.app N (φ m) = E.map φ (adj.unit.app M m) at h
  have h' : (E.map φ) (show E.obj M from adj.unit.app M m) =
      (show E.obj N from adj.unit.app N (φ m)) := h.symm
  simpa only [ModuleCat.ringExtensionTmul, map_smul] using! congrArg (fun z ↦ b • z) h'

private theorem galoisScalarCompTmul {R S T : Type (u + 1)}
    [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u + 1} R)
    (s : S) (d : T) (m : M) :
    (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom.app M
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ d
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f M s m)) =
      ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) M (d * g s) m := by
  let adj₁ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let adj₂ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g
  let adj₃ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)
  let a := ModuleCat.ringExtensionComp.{u + 1, u + 1} f g
  have h := congrArg (fun k ↦ k m)
    ((adj₁.comp adj₂).unit_leftAdjointUniq_hom_app
      (adj₃.ofNatIsoRight (ModuleCat.restrictScalarsComp f g)) M)
  change a.hom.app M (adj₂.unit.app _ (adj₁.unit.app M m)) = adj₃.unit.app M m at h
  simp only [ModuleCat.ringExtensionTmul, map_smul]
  change d • a.hom.app M
      (g s • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} g).obj _ from
        adj₂.unit.app _ (adj₁.unit.app M m))) =
    (d * g s) • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)).obj M from
      adj₃.unit.app M m)
  rw [map_smul, h, mul_smul]

private theorem galoisSheafScalarComp_sections
    (Y : Scheme.{u}) {R S T : Type (u + 1)} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    let J := Y.smallEtaleTopology
    let E₁ := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
    let E₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
    let E₃ := ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)
    let F₁ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj F
    Functor.whiskerRight (toSheafify J (F.obj ⋙ E₁)) E₂ ≫
      toSheafify J (F₁.obj ⋙ E₂) ≫ ((galoisSheafScalarComp Y f g).hom.app F).hom =
      Functor.whiskerLeft F.obj
        (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom ≫
        toSheafify J (F.obj ⋙ E₃) := by
  let J := Y.smallEtaleTopology
  let E₁ := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let E₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
  let F₁ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj F
  let k := (presheafToSheaf J (ModuleCat.{u + 1} T)).map
    (Functor.whiskerRight (toSheafify J (F.obj ⋙ E₁)) E₂)
  have hk : IsIso k := by
    let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g).isLeftAdjoint
    apply (J.W_iff _).mp
    exact J.W_of_preservesSheafification E₂ _ (J.W_toSheafify _)
  dsimp only
  simp only [galoisSheafScalarComp, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    NatTrans.comp_app, NatIso.isIso_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  change Functor.whiskerRight (toSheafify J (F.obj ⋙ E₁)) E₂ ≫
    toSheafify J (sheafify J (F.obj ⋙ E₁) ⋙ E₂) ≫
    (sheafToPresheaf J _).map (inv k) ≫
      sheafifyMap J (Functor.whiskerLeft F.obj
        (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom) = _
  rw [toSheafify_naturality_assoc]
  change toSheafify J _ ≫ (sheafToPresheaf J _).map k ≫
    (sheafToPresheaf J _).map (inv k) ≫
      sheafifyMap J (Functor.whiskerLeft F.obj
        (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom) = _
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (toSheafify_naturality J (Functor.whiskerLeft F.obj
    (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom)).symm

private theorem galoisSheafScalarComp_tmul
    (Y : Scheme.{u}) {R S T : Type (u + 1)} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (a : S) (b : T) (z : F.obj.obj (op U)) :
    let J := Y.smallEtaleTopology
    let E₁ := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
    let E₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
    let E₃ := ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)
    let F₁ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj F
    ((galoisSheafScalarComp Y f g).hom.app F).hom.app (op U)
      ((toSheafify J (F₁.obj ⋙ E₂)).app (op U)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b
          ((toSheafify J (F.obj ⋙ E₁)).app (op U)
            (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a z)))) =
      (toSheafify J (F.obj ⋙ E₃)).app (op U)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z) := by
  have h := NatTrans.congr_app (galoisSheafScalarComp_sections Y f g F) (op U)
  have h' := congrArg (fun k ↦ k
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a z))) h
  dsimp only [Sheaf.ringExtendScalars, Functor.comp_obj] at h'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ModuleCat.comp_apply] at h'
  erw [galoisScalarMapTmul, galoisScalarCompTmul] at h'
  exact h'

private theorem galoisModuleSmallLimits (R : Type (u + 1)) [Ring R] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

attribute [local instance] galoisModuleSmallLimits

private noncomputable def galoisScalarStalkIso
    {Y : Scheme.{u}} {R S : Type (u + 1)} [Ring R] [Ring S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (f : R →+* S) :
    (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
      ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
    (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f :
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) ⋙
      (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S) := by
  let p := pointSmallEtale y
  let J := Y.smallEtaleTopology
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S :=
    ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  exact Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u + 1} R))
      (p.presheafFiberCompIso E).symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙
      (Functor.whiskeringRight Y.Etaleᵒᵖ
        (ModuleCat.{u + 1} R) (ModuleCat.{u + 1} S)).obj E)
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).symm

private theorem galoisScalarStalkIso_germ
    {Y : Scheme.{u}} {R S : Type (u + 1)} [Ring R] [Ring S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (a : S)
    (s : F.obj.obj (op U)) :
    ((galoisScalarStalkIso y f).hom.app F)
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a
        ((pointSmallEtale y).toPresheafFiber U x F.obj s)) =
      (pointSmallEtale y).toPresheafFiber U x
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).obj
        ((toSheafify Y.smallEtaleTopology
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a s)) := by
  let p := pointSmallEtale y
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  have h : E.map (p.toPresheafFiber U x F.obj) ≫
      (p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ E) =
      (toSheafify Y.smallEtaleTopology (F.obj ⋙ E)).app (op U) ≫
        p.toPresheafFiber U x ((presheafToSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} S)).obj (F.obj ⋙ E)).obj := by
    rw [← p.toPresheafFiber_presheafFiberCompIso_hom_app E U x F.obj]
    rw [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    exact p.toPresheafFiber_naturality
      (toSheafify Y.smallEtaleTopology (F.obj ⋙ E)) U x
  have h' := congrArg (fun k ↦ k (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a s)) h
  simp only [ModuleCat.comp_apply] at h'
  erw [galoisScalarMapTmul] at h'
  simpa [galoisScalarStalkIso, p, E, Sheaf.ringExtendScalars,
    GrothendieckTopology.Point.sheafFiber] using h'

end ScalarComposition

private theorem galoisProfiniteModel
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G] :
    ∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P) := by
  let e := toAutHomeo (FiniteEtale.fiber y) G
  let : T2Space G := T2Space.of_injective_continuous e.injective e.continuous
  let : TotallyDisconnectedSpace G :=
    e.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  exact ⟨ProfiniteGrp.of G, ⟨ContinuousMulEquiv.refl G⟩⟩

/-- Finite and adic Galois correspondence, with the evaluation action.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: cor-galois-lisse-representations).
Proof: the proved finite-etale/FLC equivalence supplies the finite-set correspondence,
its Yoneda comparison and its evaluation action. The Yoneda comparison and the
finite-etale inclusion give finite limits in FLC and their preservation by its sheaf
inclusion. Pull the ambient module operations back through this inclusion; their diagram
axioms imply the generalized-element axioms of `InternalModule`. Conversely map internal
operations to ambient sheaves using inverse product and terminal comparisons; their
module laws give all ten ambient diagrams. The morphism compatibility equations coincide,
and the reverse objects give essential surjectivity. This proves the normalized module
object equivalence. Module ULift and finite Shrink give the carrier-universe equivalence,
with its comparison as linear G-actions. The finite-module component composes these
interfaces with the known internal-module transport and supplies the linear stalk
comparison and normalized evaluation. Kernels, cokernels and finite products remain lisse,
so the full module subcategory is abelian. Its equivalence preserves finite limits and
colimits. Naturality on the set maps from the constant zero module shows that every fibre
automorphism fixes every constant germ; normalized evaluation gives the trivial unit.
The lisse subcategory inherits the actual sheaf tensor structure, and actual sheafified
scalar extension restricts to it. The natural scalar composite comparison inverts the
sheafification of the first unit after the second extension and sheafifies the module
associator. Naturality and the adjunction units prove its section formula. The tensor/scalar
component supplies the equivariant representation comparisons and their composite identity.
For the integral adic correspondence, apply the finite correspondence at every quotient
and use lem-pod-adic-limit-finite-modules to reconstruct the finite module, its topology,
and all equivariant maps from the inverse system. The projections fix the action.
Rationalize the Hom modules and fibres; invariant Hom commutes with inverting the
uniformizer since their torsion is killed by one fixed power. Essential surjectivity
uses the stable lattice of lem-pod-profinite-stable-lattice. Finally pass to the
coefficient localization: each representation descends to a finite coefficient field
by Representation.IsLAdic, and finitely many matrices give full faithfulness over a
common finite extension. Kernels and cokernels of the rational representations are
continuous over a finite field of definition, giving abelianity and exactness. Tensor
and scalar comparison maps are fixed on pure tensors and commute with finite-level
reduction, inverse limits, rationalization and extension of coefficient fields. -/
theorem galois_lisse_representations
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G] :
    ∃ c : GaloisLisseFiniteCorrespondence y G,
      ∀ (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l :
        Y.residueField x)] (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q],
        Nonempty (GaloisLisseAdicCorrespondence y G c l Q) := by
  classical
  obtain ⟨Φ, E, γ, hΦ, ⟨α⟩, ⟨τ, hτ⟩, _⟩ :=
    FiniteEtale.exists_fiber_flc_equivalence y G
  obtain ⟨η, hη⟩ := galoisFiniteEtaleComparison y G Φ E γ α τ hτ
  let : HasFiniteLimits Y.FLC :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence Φ.inverse⟩
  let : PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))) :=
    galoisFLC_preservesFiniteLimits Φ hΦ
  let ε (R : Type (u + 1)) [Ring R] := (galoisFiniteCarrierComparison R G).choose
  have εaction (R : Type (u + 1)) [Ring R] :
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G) :=
    (galoisFiniteCarrierComparison R G).choose_spec
  let κ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R) :=
    (galoisUnderlyingStalkIso R F.obj y).symm.toEquiv
  have κgerm : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R)
      (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)),
      κ R F ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F.obj).obj s := by
    intro R _ _ F U x t
    exact galoisUnderlyingStalkIso_germ R F.obj y U x t
  let L (R : Type (u + 1)) [Ring R] [Finite R] :=
    galoisModuleObjectEquivalence (Y := Y) R
  have Lops : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (A : LambdaModuleObject Y R),
      let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
      let X : Y.FLC := ⟨A.sheaf, A.isFLC⟩
      ((L R).functor.obj A).X = X ∧
      HEq ((L R).functor.obj A).add
        (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add)) ∧
      HEq ((L R).functor.obj A).zero
        (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero)) ∧
      HEq ((L R).functor.obj A).neg (I.preimage (X := X) (Y := X) A.str.neg) ∧
      ∀ r, HEq (((L R).functor.obj A).smul r)
        (I.preimage (X := X) (Y := X) (A.str.smul r)) := by
    intro R _ _ A
    exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ ↦ HEq.rfl⟩
  have Lmaps : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (A B : LambdaModuleObject Y R) (f : A ⟶ B),
      HEq (((L R).functor.map f).val).hom f.hom := by
    intro R _ _ A B f
    exact HEq.rfl
  obtain ⟨e, τM, haction⟩ := galois_finite_module_lift y G Φ E γ η τ hτ
    κ κgerm L Lops Lmaps (fun R _ _ ↦ ε R) (fun R _ _ ↦ εaction R)
  let d : GaloisLisseFiniteData y G := ⟨γ, Φ, η, e, τM⟩
  have heval : galoisFiniteEvaluationAction y G d := by
    intro R _ _ F
    obtain ⟨h, hρ⟩ := haction R F
    exact ⟨h, κ R F, κgerm R F, hρ⟩
  have hunit : galoisFiniteUnit y G d := galoisFiniteUnit_of_evaluation y G d heval
  let B (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S) :
      LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S :=
    ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f)
      (fun F ↦ (galoisLisse_iff_finiteLocallyConstant S _).mpr
        (lisse_ring_scalar_extension f F.obj
          ((galoisLisse_iff_finiteLocallyConstant R _).mp F.property)))
  let αB (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S) :
      B R S f ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f := Iso.refl _
  let cB (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      [Ring T] [Finite T] (f : R →+* S) (g : S →+* T) :
      B R S f ⋙ B S T g ≅ B R T (g.comp f) :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight
      (LisseModuleSheafCategory Y R)).preimageIso
        (Functor.isoWhiskerLeft (ObjectProperty.ι _) (galoisSheafScalarComp Y f g))
  have hcB : ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), ∀ (F :
    LisseModuleSheafCategory Y R) (U : Y.Etale) (a : S) (b : T) (z : F.obj.obj.obj (op U)), ((αB R T
    (g.comp f)).hom.app F).hom.app (op U) (((cB R S T f g).hom.app F).hom.hom.app (op U) (((αB S T
      g).inv.app ((B
    R S f).obj F)).hom.app (op U) (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1}
    T)).app (((B R S f).obj F).obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} g)).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b (((αB R S f).inv.app F).hom.app (op U)
    (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} S)).app (F.obj.obj ⋙
    ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U) (ModuleCat.ringExtensionTmul.{u + 1, u
    + 1} f _ a z))))))) = ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} T)).app
    (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z) := by
    intro R S T _ _ _ _ _ _ f g F U a b z
    simpa [αB, cB, B, ModuleCat.id_apply] using galoisSheafScalarComp_tmul Y f g F.obj U a b z
  obtain ⟨hbraided, βB, hcomp⟩ :=
    galois_finite_tensor_scalar y G d heval hunit
      (fun R S _ _ _ _ f ↦ galoisScalarStalkIso y f)
      (fun R S _ _ _ _ f F U x a z ↦ galoisScalarStalkIso_germ y f F U x a z)
      B αB cB hcB
  have hscalar : galoisFiniteScalarExtension y G d := by
    refine ⟨B, αB, βB, ?_⟩
    intro R S T _ _ _ _ _ _ f g
    exact ⟨cB R S T f g, hcomp R S T f g, hcB R S T f g⟩
  have htensor : galoisFiniteTensor y G d := by
    unfold galoisFiniteTensor
    intro R _ _
    obtain ⟨m, b, hι⟩ := galoisLisseTensorStructure Y R
    exact ⟨m, b, hι, hbraided R m b hι, hunit R⟩
  let c : GaloisLisseFiniteCorrespondence y G :=
    { toGaloisLisseFiniteData := d
      yonedaComparison := by unfold galoisYonedaComparison; exact hΦ
      finiteEtaleAction := by unfold galoisFiniteEtaleAction; exact hη
      finiteAbelian := by
        unfold galoisFiniteAbelian
        intro R _ _
        exact galoisLisse_abelian Y R
      finiteKernels := by
        unfold galoisFiniteKernels
        intro R _ _
        exact galoisLisse_closedUnderKernels Y R
      finiteCokernels := by
        unfold galoisFiniteCokernels
        intro R _ _
        exact galoisLisse_closedUnderCokernels Y R
      finiteLimits := by unfold galoisFiniteLimits; intro R _ _; infer_instance
      finiteColimits := by unfold galoisFiniteColimits; intro R _ _; infer_instance
      finiteUnit := hunit
      finiteEvaluationAction := heval
      finiteTensor := htensor
      finiteScalarExtension := hscalar }
  obtain ⟨P, ⟨δ⟩⟩ := galoisProfiniteModel y G
  refine ⟨c, ?_⟩
  intro l _ _ _ _ Q _ _ _
  obtain ⟨a, _, _⟩ := galois_adic_from_finite y G c P δ l Q
  exact ⟨a⟩

end AlgebraicGeometry.Scheme
