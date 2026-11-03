/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteBrown.FiniteBrownAdjointData
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.SixFunctors.Etale.Derived.Supports
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteBrown
/-- Local chart Hom bijections glue to a representing pair.
Source: `finiteRingCounit_localRepresentability`, proof step 6.
(blueprint: sk-lem-sp-finite-existence).
Proof plan: specialize the finite-ring local representability theorem to the two-open cover,
using `openTerm_ctf` and the chart counit equalities; the uniqueness conclusion is then the
prescribed counit-preserving isomorphism. -/
theorem finiteBrownAdjointExistence_gluing
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) [Smooth f]
    (d : ℕ) (_hcd : BaseFieldFiniteCD ell k) (B : BrownData ell n hn k f c)
    (C : FiniteBrownChartData ell n hn k f c B d) :
    Nonempty (FiniteBrownGluingData ell n hn k f c B d) := by
  classical
  letI : IsSeparated f := by
    have : IsSeparated (f ≫ (Y ↘ Spec (.of k))) := by
      simpa only [CategoryTheory.comp_over] using
        (inferInstance : IsSeparated (X ↘ Spec (.of k)))
    exact IsSeparated.of_comp f (Y ↘ Spec (.of k))
  refine ⟨⟨?_⟩⟩
  intro U V hcover K H hH ε hlocal
  let opens : Bool → X.Opens := fun b ↦ if b then U else V
  have hcov : iSup opens = ⊤ := by simpa only [iSup_bool_eq, opens, Bool.false_eq_true, ↓reduceIte] using hcover
  have hinter (J : Finset Bool) (hJ : J.Nonempty) :
      (⨅ i : J, opens i.val) = U ∨ (⨅ i : J, opens i.val) = V ∨
        (⨅ i : J, opens i.val) = U ⊓ V := by
    have casesJ : J = {true} ∨ J = {false} ∨ J = {true, false} := by
      have : J ⊆ {true, false} := by simp [Finset.subset_iff, Bool.forall_bool]
      obtain ⟨b, hb⟩ := hJ
      rcases Finset.eq_singleton_or_nontrivial hb with rfl | hj
      · cases b <;> simp
      · right; right
        apply Finset.Subset.antisymm this
        obtain ⟨a, ha, b, hb, hab⟩ := hj
        cases a <;> cases b <;> simp_all [Finset.subset_iff]
    have hi : (⨅ i : J, opens i.val) = J.inf opens := by
      simp only [Finset.inf_eq_iInf, iInf_subtype]
    rw [hi]
    rcases casesJ with rfl | rfl | rfl <;> simp [opens, inf_comm]
  have hloc : ∀ (J : Finset Bool), J.Nonempty → ∀ (W : X.Opens),
      W = ⨅ i : J, opens i.val → ∀ (P : D (Coeff ell n) W.toScheme),
      ctf (Coeff ell n) W.toScheme P →
      Function.Bijective (fun a : P ⟶
          (openImmersionRestriction (ModuleCat.{u + 1} (Coeff ell n))
            W.ι).mapDerivedCategory.obj H ↦
        (support (Coeff ell n) c).map
          (((unboundedOpenProEtaleAdjunction (Coeff ell n) W.ι).homEquiv P H).symm a) ≫ ε) := by
    intro J hJ W hW P hP
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (Coeff ell n)) W.ι
    let b := unboundedOpenProEtaleAdjunction (Coeff ell n) W.ι
    let e := (b.homEquiv P H).symm.trans (a.homEquiv P H)
    have hh := (hlocal W (hW ▸ hinter J hJ) ⟨P, hP⟩).comp e.bijective
    simpa only [Function.comp_def, e, Equiv.trans_apply, a, Equiv.symm_apply_apply] using hh
  have hglobal := (finiteRingCounit_localRepresentability k (Coeff ell n)
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) f (CategoryTheory.comp_over f (Spec (.of k)))
    c C.support_preserves H K.obj hH K.property ε Bool opens hcov hloc).1
  refine ⟨fun M ↦ hglobal M.obj M.property, ?_⟩
  let F := support (Coeff ell n) c
  have hBB (M : D (Coeff ell n) X) (hM : ctf (Coeff ell n) X M) :
      Function.Bijective (fun a : M ⟶ B.right.obj K ↦ F.map a ≫ B.counit.app K) := by
    have ho : (Etale.DerivedCategory.isBoundedConstructible (Coeff ell n) X).map
        (nu (Coeff ell n) X) M :=
      (congrFun (exceptionalTransport_constructible_comparison (Coeff ell n) X) M).mp
        ⟨hM.1, hM.2.1⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := ho
    have hN' : Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (Coeff ell n)) X N := by
      obtain ⟨hc, a, b, hab, hv⟩ := hN
      exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff N a).mpr
        (fun i hi ↦ hv i (Or.inl hi))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff N b).mpr
          (fun i hi ↦ hv i (Or.inr hi))⟩⟩,
        fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
          (hc i)⟩
    exact B.represents K M
      (DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
        M ⟨N, hN', ⟨e⟩⟩) hM.2.2
  obtain ⟨a, ha⟩ := (hBB H hH).2 ε
  obtain ⟨b, hb⟩ := (hglobal (B.right.obj K) (B.preserves K)).2 (B.counit.app K)
  change F.map a ≫ B.counit.app K = ε at ha
  change F.map b ≫ ε = B.counit.app K at hb
  have hab : a ≫ b = 𝟙 H := by
    apply (hglobal H hH).1
    change F.map (a ≫ b) ≫ ε = F.map (𝟙 H) ≫ ε
    rw [F.map_comp, Category.assoc, hb, ha, F.map_id, Category.id_comp]
  have hba : b ≫ a = 𝟙 (B.right.obj K) := by
    apply (hBB _ (B.preserves K)).1
    change F.map (b ≫ a) ≫ B.counit.app K = F.map (𝟙 _) ≫ B.counit.app K
    rw [F.map_comp, Category.assoc, ha, hb, F.map_id, Category.id_comp]
  let z : H ≅ B.right.obj K := ⟨a, b, hab, hba⟩
  refine ⟨z, ha, ?_⟩
  intro z' hz'
  apply Iso.ext
  exact (hBB H hH).1 (hz'.trans ha.symm)
end AlgebraicGeometry.ProEtale.FiniteBrown
