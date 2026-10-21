/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE, SHEAF group Q4
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.CoherentPowerComparison
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback
public import Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback

/-! Frobenius and the canonical coherent-etale comparisons.
Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH.
(blueprint: lem-weil-pbc-coherent-frobenius-comparison). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
noncomputable section

private theorem comparison_conjugate
    {A B C : Type*}
    (e : A ≃ B) (n : B ≃ C) (s : B → B) (t : C → C)
    (h : ∀ x, n (s x) = t (n x)) (x : C) :
    (e.trans n).symm (t x) = e.symm (s (e ((e.trans n).symm x))) := by
  apply (e.trans n).injective
  simp only [Equiv.apply_symm_apply, Equiv.trans_apply, h]
  exact congrArg t ((e.trans n).apply_symm_apply x).symm

/-- Frobenius commutes with the canonical comparisons and field extension.
Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH.
(blueprint: lem-weil-pbc-coherent-frobenius-comparison).

Proof: The coherent power comparison gives semilinearity and the normalized
power square. Conjugating the latter by the fixed module/abelian comparison
gives the etale-to-coherent square. Properness of the base change supplies the
target comparison; its structural pullback square and hb give the third claim.
Finally K-linearity gives b(a tensor v)=a*b(1 tensor v). Apply semilinearity on Y,
hb, structural Frobenius pullback naturality, then hb backwards. This proves the
tensor formula. No construction or new bijectivity proof of the supplied b is
needed, and neither field must be perfect. -/
theorem coherent_frobenius_comparison
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (g : Y ⟶ Spec (.of K)) (j : Y ⟶ X)
    (h : IsPullback j g f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ)
    (FrZ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
    (FrZK : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y) ⟶
      (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y))
    (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p)
    (hFrZK : ∀ (U : Y.Opensᵒᵖ) (s : Γ(Y, U.unop)), FrZK.hom.app U s = s ^ p)
    (FrE : structureTensorEtaleSheaf X ⟶ structureTensorEtaleSheaf X)
    (hFrE : ∀ (U : X.Etaleᵒᵖ) (s : (structureTensorEtaleSheaf X).obj.obj U),
      (tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ (FrE.hom.app U s).down =
        (@id Γ(U.unop.left, ⊤)
          ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ s.down)) ^ p)
    (u : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj
      (structureTensorEtaleSheaf X) ⟶ structureTensorEtaleSheaf Y)
    (hu : ∀ (U : X.Etale) (s : (structureTensorEtaleSheaf X).obj.obj (op U)),
      (tensorPullbackObjUnitToUnit
          ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U).hom).app ⊤
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
          (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y) u).hom.app
            (op U) s).down =
        (pullback.fst U.hom j).appTop
          ((tensorPullbackObjUnitToUnit U.hom).app ⊤ s.down))
    (b : (K ⊗[k] scalarCohomology f (unit X) q) ≃ₗ[K]
      scalarCohomology g (unit Y) q)
    (hb : ∀ v : scalarCohomology f (unit X) q,
      b ((1 : K) ⊗ₜ[k] v) =
        (moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q).hom v) :
    (∀ (a : k) (v : scalarCohomology f (unit X) q),
      structureCoherentFrobenius f q FrZ (a • v) =
        a ^ p • structureCoherentFrobenius f q FrZ v) ∧
    (∀ x : Sheaf.H (structureTensorEtaleSheaf X) q,
      structureCoherentEtaleComparison f q (Sheaf.H.map FrE q x) =
        structureCoherentFrobenius f q FrZ (structureCoherentEtaleComparison f q x)) ∧
    (∀ x : Sheaf.H (structureTensorEtaleSheaf X) q,
      structureCoherentEtaleComparisonOfPullback f g j
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) h q
          (Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x)) =
        b ((1 : K) ⊗ₜ[k] structureCoherentEtaleComparison f q x)) ∧
    ∀ (v : scalarCohomology f (unit X) q) (a : K),
      structureCoherentFrobenius g q FrZK (b (a ⊗ₜ[k] v)) =
        b ((a ^ p) ⊗ₜ[k] structureCoherentFrobenius f q FrZ v)  := by
  let : IsProper g := MorphismProperty.of_isPullback h inferInstance
  have hpower := coherentPowerComparison f p q FrZ hFrZ
  refine ⟨hpower.1, ?_, ?_, ?_⟩
  · intro x
    unfold structureCoherentEtaleComparison canonicalCoherentEtaleComparison
      structureCoherentFrobenius coherentAdditiveEndomorphism
    exact comparison_conjugate (moduleAbelianCohomologyLarge X (unit X) q).toEquiv
      (normalizedCoherentEtaleComparison f (unit X) q).toEquiv
      (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ FrZ q)
      (Sheaf.H.map FrE q)
      (hpower.2 FrE hFrE) x
  · intro x
    unfold structureCoherentEtaleComparisonOfPullback
    change structureCoherentEtaleComparison g q _ = _
    rw [hb]
    exact coherentEtaleComparison_pullback f g j q u hu x
  · intro v a
    have hp (w : scalarCohomology f (unit X) q) :
        structureCoherentFrobenius g q FrZK
          (moduleCohomologyFMap j
            (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q w) =
          moduleCohomologyFMap j
            (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q
            (structureCoherentFrobenius f q FrZ w) := by
      unfold structureCoherentFrobenius
      exact coherentFrobenius_pullback j p q FrZ FrZK hFrZ hFrZK w
    have ht (w : scalarCohomology f (unit X) q) (c : K) :
        b (c ⊗ₜ[k] w) = c • b ((1 : K) ⊗ₜ[k] w) := by
      rw [← b.map_smul]
      congr 1
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, (coherentPowerComparison g p q FrZK hFrZK).1, hb,
      hp,
      ← hb, ← ht]

end
end AlgebraicGeometry.Scheme.Modules
