/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Paper.GaloisLisseRepresentationData
public import Sheaf.Paper.LisseModuleSheaves
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.Paper.GaloisLisseFiniteModuleLift
import Sheaf.Paper.GaloisLisseFiniteCompatibility
import Sheaf.Paper.GaloisLisseAdicEquivalences
import Sheaf.Paper.GaloisLisseAdicCompatibility
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.Transfer
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves

/-!
# Galois representations attached to lisse sheaves

Source: Stacks Project, Tag 0DV5; the blueprint, `sec-poincare-duality`,
`sk-lem-finite` (blueprint: cor-galois-lisse-representations);
Deligne, Weil II (1.1.1), (1.1.6).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct FintypeCatDiscrete ZeroObject

namespace AlgebraicGeometry.Scheme

noncomputable section

attribute [local irreducible] Padic
attribute [local irreducible] IsLisseIntegralDiagram
attribute [local irreducible] lisseIntegralTensor lisseRationalTensor lisseAlgebraicTensor
attribute [local irreducible] lisseIntegralUnit lisseRationalUnit lisseAlgebraicUnit
attribute [local irreducible] Representation.IsContinuousIntegral
attribute [local irreducible] Representation.IsContinuousCoefficient Representation.IsLAdic
attribute [local irreducible] Padic.coefficientExtensionAbsoluteValue
attribute [local irreducible] spectralNorm.nontriviallyNormedField

-- Resolve torsion-freeness over the base field directly, without searching free modules.
local instance (priority := 100000) galoisAssemblyPadicTorsionFree
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] :
    Module.IsTorsionFree ℚ_[l] E := DivisionSemiring.to_moduleIsTorsionFree

-- The intermediate-field and integral scalar towers recur in each adic clause.
local instance (priority := 100000) galoisAssemblyIntermediateTorsionFree
    (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
    [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] (E : Padic.FiniteCoefficientFields l Q) :
    Module.IsTorsionFree E.val Q := DivisionSemiring.to_moduleIsTorsionFree

local instance (priority := 100000) galoisAssemblyIntegersTorsionFree
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Module.IsTorsionFree (Padic.coefficientExtensionIntegers l E) E := inferInstance

-- Fix the small-etale sheafification instance before elaborating the fibre clauses.
local instance (priority := 100000) galoisAssemblyModuleSheafify
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology
    (ModuleCat.{u + 1} R) Y).isRightAdjoint

private theorem galoisTensorIso (R : Type (u + 1)) [CommRing R]
    {G : Type u} [Group G] {X Z W : Rep.{u + 1} R G} (i : MonoidalCategory.tensorObj X Z ≅ W) :
    ∃ c : (X.V ⊗[R] Z.V) ≃ₗ[R] W.V,
      ∀ (g : G) (z : X.V ⊗[R] Z.V),
        c (galoisTensorAction R X Z g z) = W.ρ g (c z) := by
  refine ⟨((forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)).mapIso i).toLinearEquiv, ?_⟩
  intro g z
  change i.hom.hom ((MonoidalCategory.tensorObj X Z).ρ g z) = W.ρ g (i.hom.hom z)
  exact Rep.hom_comm_apply i.hom g z

private theorem galoisMonoidalTensor (R : Type (u + 1)) [CommRing R]
    {G : Type u} [Group G] {C : Type*} [Category C]
    (F : C ⥤ Rep.{u + 1} R G) (T : C → C → C) (U : C)
    (h : ∃ m : MonoidalCategory C, m.toMonoidalCategoryStruct.tensorObj = T ∧
      @MonoidalCategoryStruct.tensorUnit C _ m.toMonoidalCategoryStruct = U ∧
      Nonempty (@Functor.Monoidal C _ m (Rep.{u + 1} R G) _ _ F)) :
    ∀ X Z : C, ∃ c : ((F.obj X).V ⊗[R] (F.obj Z).V) ≃ₗ[R] (F.obj (T X Z)).V,
      ∀ (g : G) (z : (F.obj X).V ⊗[R] (F.obj Z).V),
        c (galoisTensorAction R (F.obj X) (F.obj Z) g z) =
          (F.obj (T X Z)).ρ g (c z) := by
  obtain ⟨m, ht, hu, ⟨hm⟩⟩ := h
  let := m
  let := hm
  intro X Z
  have hXZ : MonoidalCategory.tensorObj X Z = T X Z := congrFun (congrFun ht X) Z
  exact galoisTensorIso R
    (Functor.Monoidal.μIso F X Z ≪≫ F.mapIso (eqToIso hXZ))

private theorem galoisMonoidalUnit (R : Type (u + 1)) [CommRing R]
    {G : Type u} [Group G] {C : Type*} [Category C]
    (F : C ⥤ Rep.{u + 1} R G) (T : C → C → C) (U : C)
    (h : ∃ m : MonoidalCategory C, m.toMonoidalCategoryStruct.tensorObj = T ∧
      @MonoidalCategoryStruct.tensorUnit C _ m.toMonoidalCategoryStruct = U ∧
      Nonempty (@Functor.Monoidal C _ m (Rep.{u + 1} R G) _ _ F)) :
    Nonempty (F.obj U ≅ Rep.trivial R G R) := by
  obtain ⟨m, ht, hu, ⟨hm⟩⟩ := h
  let := m
  let := hm
  exact ⟨F.mapIso (eqToIso hu.symm) ≪≫ (Functor.Monoidal.εIso F).symm⟩

-- The two local-finiteness interfaces use the same local constant models.
private theorem galoisLisse_iff_finiteLocallyConstant
    {Y : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsLisseModuleSheaf F ↔ IsFiniteLocallyConstantSheaf F := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  constructor
  · intro hF
    have hs := (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mp hF
    obtain ⟨𝒰, h𝒰⟩ := hF
    refine { toIsLocallyConstantSheaf := ⟨⟨⟨𝒰, ?_⟩⟩⟩
             toIsFiniteSheaf := ⟨?_⟩ }
    · intro i
      obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
      exact Sheaf.isConstant_of_iso _ e
    · intro Ω _ _ s
      apply (ModuleCat.isFinitelyGenerated_iff _).mpr
      have hfin := hs.finite_sheafFiber Ω s
      have : Finite (((pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) :=
        @Finite.of_equiv _ _ hfin (((pointSmallEtale s).sheafFiberCompIso
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).toEquiv
      exact Module.Finite.of_finite
  · intro hF
    have := hF
    apply (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mpr
    refine ⟨?_, ⟨?_⟩⟩
    · obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
      refine ⟨𝒰, fun i ↦ ?_⟩
      have := h𝒰 i
      change ((sheafCompose (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        (F.over (𝒰.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    · intro Ω _ _ s
      apply (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr
      have := (ModuleCat.isFinitelyGenerated_iff _).mp
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) Ω s)
      have hfin : Finite (((pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) := Module.finite_of_finite Λ
      exact @Finite.of_equiv _ _ hfin (((pointSmallEtale s).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).symm.toEquiv

section FiniteAssembly

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]

private theorem galoisFiniteEtaleFiberComparison
    [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (hComp : Φ.functor ⋙ E.functor ≅ (FiniteEtale.equivalenceContAction y G).functor)
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (hτ : ∀ (F : Y.FLC) (g : G) (z : ULift.{u + 1} (E.functor.obj F).obj.V),
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ g).hom.app F (τ.hom.app F z)) :
    ∃ η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
        (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
        FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙
          uliftFunctor.{u + 1, u},
      ∀ (P : Y.FiniteEtale) (g : G)
        (z : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (Φ.functor.obj P).obj),
        η.hom.app P ((γ g).hom.app (Φ.functor.obj P) z) =
          ⟨g • (η.hom.app P z).down⟩ := by
  let U := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
    CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  let η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
      FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙
        uliftFunctor.{u + 1, u} :=
    (Functor.isoWhiskerLeft Φ.functor τ).symm ≪≫ Functor.isoWhiskerRight hComp U
  refine ⟨η, ?_⟩
  intro P g z
  have hz := hτ (Φ.functor.obj P) g (τ.inv.app (Φ.functor.obj P) z)
  have hz' : τ.inv.app (Φ.functor.obj P) ((γ g).hom.app (Φ.functor.obj P) z) =
      ⟨((E.functor.obj (Φ.functor.obj P)).obj.ρ g).hom
        (τ.inv.app (Φ.functor.obj P) z).down⟩ := by
    have hτz : τ.hom.app (Φ.functor.obj P) (τ.inv.app (Φ.functor.obj P) z) = z :=
      ConcreteCategory.congr_hom (τ.inv_hom_id_app (Φ.functor.obj P)) z
    rw [hτz] at hz
    exact (congrArg (τ.inv.app (Φ.functor.obj P)) hz.symm).trans
      (ConcreteCategory.congr_hom (τ.hom_inv_id_app (Φ.functor.obj P)) _)
  change ULift.up ((hComp.hom.app P).hom.hom
    (τ.inv.app (Φ.functor.obj P) ((γ g).hom.app (Φ.functor.obj P) z)).down) = _
  rw [hz']
  apply congrArg ULift.up
  exact ConcreteCategory.congr_hom ((hComp.hom.app P).hom.comm g)
    (τ.inv.app (Φ.functor.obj P) z).down

private theorem galoisFiniteKernels_of_data (d : GaloisLisseFiniteData y G) :
    galoisFiniteKernels y G d := by
  intro Λ _ _
  refine ⟨?_⟩
  rintro _ ⟨f, k, hk, hF, hH⟩
  have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp hF
  have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp hH
  have := IsFiniteLocallyConstantSheaf.kernel f
  apply (galoisLisse_iff_finiteLocallyConstant Λ k.pt).mpr
  let i := (kernelIsKernel f).conePointUniqueUpToIso hk
  change kernel f ≅ k.pt at i
  exact IsFiniteLocallyConstantSheaf.of_iso i

private theorem galoisFiniteCokernels_of_data (d : GaloisLisseFiniteData y G) :
    galoisFiniteCokernels y G d := by
  intro Λ _ _
  refine ⟨?_⟩
  rintro _ ⟨f, k, hk, hF, hH⟩
  have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp hF
  have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp hH
  have := IsFiniteLocallyConstantSheaf.cokernel f
  apply (galoisLisse_iff_finiteLocallyConstant Λ k.pt).mpr
  let i := (cokernelIsCokernel f).coconePointUniqueUpToIso hk
  change cokernel f ≅ k.pt at i
  exact IsFiniteLocallyConstantSheaf.of_iso i

private theorem galoisFiniteAbelian_of_data (d : GaloisLisseFiniteData y G) :
    galoisFiniteAbelian y G d := by
  intro Λ _ _
  let P : ObjectProperty (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsLisseModuleSheaf
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp h
    exact (galoisLisse_iff_finiteLocallyConstant Λ _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso e)⟩
  have : P.ContainsZero := ⟨⟨0, isZero_zero _,
    (galoisLisse_iff_finiteLocallyConstant Λ _).mpr
      (IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _))⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨H, hH⟩
    have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp (hH ⟨.left⟩)
    have := (galoisLisse_iff_finiteLocallyConstant Λ _).mp (hH ⟨.right⟩)
    have := IsFiniteLocallyConstantSheaf.biprod (H.obj ⟨.left⟩) (H.obj ⟨.right⟩)
    exact (galoisLisse_iff_finiteLocallyConstant Λ _).mpr
      (IsFiniteLocallyConstantSheaf.of_iso ((biprod.isoProd _ _) ≪≫
        (HasLimit.isoOfNatIso (diagramIsoPair H)).symm)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  have : P.IsClosedUnderKernels := galoisFiniteKernels_of_data y G d Λ
  have : P.IsClosedUnderCokernels := galoisFiniteCokernels_of_data y G d Λ
  exact ⟨inferInstanceAs (Abelian P.FullSubcategory)⟩

private theorem galoisFiniteLimits_of_data (d : GaloisLisseFiniteData y G) :
    galoisFiniteLimits y G d := by
  intro Λ _ _
  infer_instance

private theorem galoisFiniteColimits_of_data (d : GaloisLisseFiniteData y G) :
    galoisFiniteColimits y G d := by
  intro Λ _ _
  infer_instance

end FiniteAssembly

section AdicAssembly

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)

-- Cache the localization category; its object type need not be unfolded by these proofs.
local instance (priority := 100000) galoisAssemblyAlgebraicCategory :
    Category (LisseAlgebraicSheaf l Y Q) := inferInstance


private theorem galoisAbelianOfEquivalence {C : Type*} [Category C]
    {D : Type*} [Category D] [Abelian D] (e : C ≌ D) : Nonempty (Abelian C) := by
  let : Preadditive C := .ofFullyFaithful e.fullyFaithfulFunctor
  have : HasFiniteProducts C :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact ⟨abelianOfEquivalence e.functor⟩

private theorem galoisRationalSheavesAbelian_of_representations
    (h : galoisRationalRepresentationsAbelian y G c l Q d) :
    galoisRationalSheavesAbelian y G c l Q d := by
  intro E
  obtain ⟨hE⟩ := h E
  have := hE
  exact galoisAbelianOfEquivalence (d.eR E)

private theorem galoisAlgebraicSheavesAbelian_of_representations
    (h : galoisAlgebraicRepresentationsAbelian y G c l Q d) :
    galoisAlgebraicSheavesAbelian y G c l Q d := by
  obtain ⟨hA⟩ := h
  have := hA
  exact galoisAbelianOfEquivalence d.eA

private theorem galoisRationalFiniteLimits_of_data :
    galoisRationalFiniteLimits y G c l Q d := by
  intro E
  infer_instance

private theorem galoisRationalFiniteColimits_of_data :
    galoisRationalFiniteColimits y G c l Q d := by
  intro E
  infer_instance

private theorem galoisAlgebraicFiniteLimits_of_data :
    galoisAlgebraicFiniteLimits y G c l Q d := by
  change PreservesFiniteLimits d.eA.functor
  infer_instance

private theorem galoisAlgebraicFiniteColimits_of_data :
    galoisAlgebraicFiniteColimits y G c l Q d := by
  change PreservesFiniteColimits d.eA.functor
  infer_instance

private theorem galoisIntegralTensor_of_monoidal
    (h : galoisIntegralMonoidal y G c l Q d) :
    galoisIntegralTensor y G c l Q d := by
  intro E
  exact galoisMonoidalTensor (G := G) (C := LisseIntegralSheaf l E.val Y)
    (Padic.coefficientExtensionIntegers l E.val) ((d.eI E).functor ⋙ ObjectProperty.ι _)
    (lisseIntegralTensor l E.val Y) (lisseIntegralUnit l E.val Y) (h E)

private theorem galoisIntegralUnit_of_monoidal
    (h : galoisIntegralMonoidal y G c l Q d) :
    galoisIntegralUnit y G c l Q d := by
  intro E
  exact galoisMonoidalUnit (G := G) (C := LisseIntegralSheaf l E.val Y)
    (Padic.coefficientExtensionIntegers l E.val) ((d.eI E).functor ⋙ ObjectProperty.ι _)
    (lisseIntegralTensor l E.val Y) (lisseIntegralUnit l E.val Y) (h E)

private theorem galoisRationalTensor_of_monoidal
    (h : galoisRationalMonoidal y G c l Q d) :
    galoisRationalTensor y G c l Q d := by
  intro E
  exact galoisMonoidalTensor (G := G) (C := LisseRationalSheaf l E.val Y)
    (E.val) ((d.eR E).functor ⋙ ObjectProperty.ι _)
    (lisseRationalTensor l E.val Y) (lisseRationalUnit l E.val Y) (h E)

private theorem galoisRationalUnit_of_monoidal
    (h : galoisRationalMonoidal y G c l Q d) :
    galoisRationalUnit y G c l Q d := by
  intro E
  exact galoisMonoidalUnit (G := G) (C := LisseRationalSheaf l E.val Y)
    (E.val) ((d.eR E).functor ⋙ ObjectProperty.ι _)
    (lisseRationalTensor l E.val Y) (lisseRationalUnit l E.val Y) (h E)

private theorem galoisAlgebraicTensor_of_monoidal
    (h : galoisAlgebraicMonoidal y G c l Q d) :
    galoisAlgebraicTensor y G c l Q d := by
  exact galoisMonoidalTensor (G := G) (C := LisseAlgebraicSheaf l Y Q)
    (Q) (d.eA.functor ⋙ ObjectProperty.ι _)
    (lisseAlgebraicTensor l Y Q) (lisseAlgebraicUnit l Y Q) (h)

private theorem galoisAlgebraicUnit_of_monoidal
    (h : galoisAlgebraicMonoidal y G c l Q d) :
    galoisAlgebraicUnit y G c l Q d := by
  exact galoisMonoidalUnit (G := G) (C := LisseAlgebraicSheaf l Y Q)
    (Q) (d.eA.functor ⋙ ObjectProperty.ι _)
    (lisseAlgebraicTensor l Y Q) (lisseAlgebraicUnit l Y Q) (h)
end AdicAssembly

private theorem galoisProfiniteModel {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G] :
    ∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P) := by
  let e := toAutContinuousMulEquiv (FiniteEtale.fiber y) G
  let P := ProfiniteGrp.ofContinuousMulEquiv
    (G := ProfiniteGrp.of (Aut (FiniteEtale.fiber y))) e.symm
  exact ⟨P, ⟨ContinuousMulEquiv.refl G⟩⟩

/-- Finite and adic Galois correspondence, with the evaluation action.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: cor-galois-lisse-representations).
Proof: use thm-galois-lc-etale and thm-galois-fundamental to identify FLC sheaves
with finite continuous actions. Transport the module operations using
lem-pod-lisse-module-sheaves-as-module-objects and
lem-pod-equivalence-induces-module-objects. The underlying fibre is the module stalk;
naturality of the automorphisms makes the operations equivariant. By
lemma-constructible-flc-serre kernels and cokernels are again lisse; geometric stalks
are exact by prop-weil-pbc-geometric-stalks-exact. Thus the full subcategory is abelian
and the equivalence is exact. Tensor and unit compatibility use the stalk tensor
comparison and naturality on pure tensors (lem-pod-lisse-tensor-and-scalar-extension);
its associativity, commutativity and unit diagrams are those of the braided functors.
Scalar extension is sheafified balanced scalar extension, transported through the
representation/action equivalence; its action is `1 ⊗ σ`. For composable ring maps,
both comparison paths send `b ⊗ (a ⊗ z)` to `b g(a) ⊗ z`.
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
  obtain ⟨Φ, E, γ, hYoneda, ⟨hComp⟩, ⟨τ, hτ⟩, _⟩ :=
    FiniteEtale.exists_fiber_flc_equivalence y G
  obtain ⟨η, hη⟩ := galoisFiniteEtaleFiberComparison y G Φ E γ hComp τ hτ
  obtain ⟨e, τM, hEval⟩ := galois_lisse_finite_module_lift y G Φ E γ η τ hτ
  let d : GaloisLisseFiniteData y G := ⟨γ, Φ, η, e, τM⟩
  obtain ⟨hunit, htensor, hscalar⟩ := galois_lisse_finite_compatibility y G d hEval
  let c : GaloisLisseFiniteCorrespondence y G :=
    { toGaloisLisseFiniteData := d
      yonedaComparison := hYoneda
      finiteEtaleAction := hη
      finiteAbelian := galoisFiniteAbelian_of_data y G d
      finiteKernels := galoisFiniteKernels_of_data y G d
      finiteCokernels := galoisFiniteCokernels_of_data y G d
      finiteLimits := galoisFiniteLimits_of_data y G d
      finiteColimits := galoisFiniteColimits_of_data y G d
      finiteUnit := hunit
      finiteEvaluationAction := hEval
      finiteTensor := htensor
      finiteScalarExtension := hscalar }
  refine ⟨c, ?_⟩
  obtain ⟨P, ⟨δ⟩⟩ := galoisProfiniteModel y G
  intro l _ _ _ _ Q _ _ _
  obtain ⟨d, _, _, hI, hR, hA⟩ :=
    galois_lisse_adic_equivalences y G c l Q P δ
  obtain ⟨hRab, hAab, hIm, hRm, hAm, hIS, hRS⟩ :=
    galois_lisse_adic_compatibility y G c l Q d hI hR hA
  exact ⟨
    { toGaloisLisseAdicData := d
      rationalSheavesAbelian :=
        galoisRationalSheavesAbelian_of_representations y G c l Q d hRab
      rationalRepresentationsAbelian := hRab
      rationalFiniteLimits := galoisRationalFiniteLimits_of_data y G c l Q d
      rationalFiniteColimits := galoisRationalFiniteColimits_of_data y G c l Q d
      algebraicSheavesAbelian :=
        galoisAlgebraicSheavesAbelian_of_representations y G c l Q d hAab
      algebraicRepresentationsAbelian := hAab
      algebraicFiniteLimits := galoisAlgebraicFiniteLimits_of_data y G c l Q d
      algebraicFiniteColimits := galoisAlgebraicFiniteColimits_of_data y G c l Q d
      integralEvaluationAction := hI
      rationalEvaluationAction := hR
      integralMonoidal := hIm
      rationalMonoidal := hRm
      algebraicMonoidal := hAm
      integralTensor := galoisIntegralTensor_of_monoidal y G c l Q d hIm
      integralUnit := galoisIntegralUnit_of_monoidal y G c l Q d hIm
      rationalTensor := galoisRationalTensor_of_monoidal y G c l Q d hRm
      rationalUnit := galoisRationalUnit_of_monoidal y G c l Q d hRm
      algebraicTensor := galoisAlgebraicTensor_of_monoidal y G c l Q d hAm
      algebraicUnit := galoisAlgebraicUnit_of_monoidal y G c l Q d hAm
      algebraicModelScalarExtension := hA
      integralScalarExtension := hIS
      rationalScalarExtension := hRS }⟩

end

end AlgebraicGeometry.Scheme
