/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.HenselianBoundaryLocalData
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
import WeilConjectures.DeligneLaumon.CondensedLisseExtensionKernel
import WeilConjectures.DeligneLaumon.GeometricOpenInertiaKernel
import WeilConjectures.DeligneLaumon.ContinuousRepresentationInertiaClosure
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Underlying condensed lisse extension and inertia

Source: Stacks Project, Tags 0BTD and 0BSW; latest blueprint,
rem-dl-a1-conventions, proof steps 1--5 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-condensed-underlying-extension-inertia).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

set_option maxHeartbeats 0 in
-- Elaborate the actual coefficient-module functors and their comparisons.
/-- The underlying lisse module extends across the missing point if and only if
its normalized geometric monodromy kills the henselian residue kernel.

Source: Stacks Project, Tags 0BTD and 0BSW; rem-dl-a1-conventions,
lem-dl-a1-condensed-lisse-extension-inertia, proof steps 1--5.
(blueprint: lem-dl-a1-condensed-underlying-extension-inertia).

Proof: apply condensed_lisse_extension_kernel to replace existence of an extension
by annihilation of the actual fibre-group kernel. Apply geometric_open_inertia_kernel
to identify this kernel with the closed normal closure of the transported residue
inertia image. For each integral-closure witness h, the representation R.algebraic(M,h)
is in the essential image and hence satisfies definedRep. By fieldsOfDefinition it
is finite dimensional and has continuous action in moduleTopology. Its finite-basis
coordinate map is injective and continuous into a finite product of the Hausdorff
coefficient field, so this module topology is Hausdorff. The continuous-representation
closure lemma identifies annihilation of the closed normal closure with annihilation
of the transported inertia subgroup. Membership in this subgroup says eG(g) equals
B.decomposition(sigma) for a sigma in the residue kernel. Applying eG inverse yields
exactly the displayed pointwise action condition. Both implications use these actual
subgroup membership equations; no Frobenius or coefficient-data choice is introduced.
-/
theorem condensed_underlying_extension_inertia
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hU : U₀ ≤ (ProjectiveLine.affineChart (Spec (.of D.k₀))).opensRange)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (_hC : (C₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) =
      (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) ∪
        Set.range (ProjectiveLine.infinity (Spec (.of D.k₀))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (x : C)
    (_hx : (pullback.fst
      (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (eC.hom x) ∉
      Set.range ((ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC))
    (B : HenselianBoundaryLocalData j b x)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G) :
    (∃ L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) C),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L ∧
        Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M)) ↔
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ σ : B.Ω ≃ₐ[B.K] B.Ω, σ ∈ B.residueAction.ker →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ (eG.symm (B.decomposition σ)) = 1 := by
  have hk := geometric_open_inertia_kernel D U₀ C₀ _hU _hdense _hC hUC U C eU eC
    j₀ _hj₀ j _hj Ω b _hb x _hx B G eG
  have he := condensed_lisse_extension_kernel D l U₀ C₀ _hl _hdense hUC U C eU eC
    j₀ _hj₀ j _hj M _hM Ω b _hb G eG _haction R
  rw [he]
  apply exists_congr
  intro h
  let V := R.algebraic.functor.obj ⟨M, h⟩
  have hdef : LisseQlbar.definedRep l G V :=
    (R.algebraic.image V).mp ⟨⟨M, h⟩, ⟨Iso.refl _⟩⟩
  have hc := (R.fieldsOfDefinition V).mpr hdef
  have hfin : FiniteDimensional (PadicAlgCl l) V.V := hc.1
  let : TopologicalSpace V.V := moduleTopology (PadicAlgCl l) V.V
  let coords := (Module.finBasis (PadicAlgCl l) V.V).equivFun
  have hT2 : T2Space V.V := T2Space.of_injective_continuous coords.injective
    (IsModuleTopology.continuous_of_linearMap coords.toLinearMap)
  let S := (B.residueAction.ker.map B.decomposition).comap eG.toMonoidHom
  have hc' (v : V.V) : Continuous (fun g : G ↦ V.ρ g v) :=
    hc.2.comp (continuous_id.prodMk continuous_const)
  have hclosure := Representation.kills_topological_normalClosure_iff V.ρ hc' S
  have hmem (g : G) : (pullbackPathHom j b) (eG g) = 1 ↔
      g ∈ (Subgroup.normalClosure (S : Set G)).topologicalClosure := by
    change g ∈ ((pullbackPathHom j b).comp eG.toMonoidHom).ker ↔ _
    rw [hk]
  constructor
  · intro H σ hσ
    have HS : ∀ g ∈ S, V.ρ g = 1 := hclosure.mp
      (fun g hg ↦ H g ((hmem g).mpr hg))
    apply HS (eG.symm (B.decomposition σ))
    change eG (eG.symm (B.decomposition σ)) ∈ B.residueAction.ker.map B.decomposition
    rw [eG.apply_symm_apply]
    exact ⟨σ, hσ, rfl⟩
  · intro H g hg
    apply hclosure.mpr ?_ g ((hmem g).mp hg)
    intro a ha
    change eG a ∈ B.residueAction.ker.map B.decomposition at ha
    obtain ⟨σ, hσ, hσa⟩ := ha
    have ha' : a = eG.symm (B.decomposition σ) := by
      apply eG.injective
      rw [eG.apply_symm_apply]
      exact hσa.symm
    rw [ha']
    exact H σ hσ

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
