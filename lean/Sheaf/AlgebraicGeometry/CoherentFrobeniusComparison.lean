/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE, SHEAF group Q4, SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.CoherentPowerComparison
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback
import WeilConjectures.AlgebraicGeometry.EtaleStructureSectionsEquiv
import Mathlib.Algebra.CharP.Lemmas

/-! Frobenius and the canonical coherent-etale comparisons.
Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH.
(blueprint: lem-weil-pbc-coherent-frobenius-comparison). -/

@[expose] public section
universe u v w u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackObjUnitToUnit

private theorem comparison_conjugate
    {A B C : Type*}
    (e : A ≃ B) (n : B ≃ C) (s : B → B) (t : C → C)
    (h : ∀ x, n (s x) = t (n x)) (x : C) :
    (e.trans n).symm (t x) = e.symm (s (e ((e.trans n).symm x))) := by
  apply (e.trans n).injective
  simp only [Equiv.apply_symm_apply, Equiv.trans_apply, h]
  exact congrArg t ((e.trans n).apply_symm_apply x).symm

/-- Transport Frobenius through additive section coordinates, including zero rings. -/
private def conjugatePower {A R : Type*} [AddCommGroup A] [CommRing R]
    (e : A ≃+ R) (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) : A →+ A where
  toFun x := e.symm (e x ^ p)
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    apply e.injective
    simp only [map_add, AddEquiv.apply_symm_apply]
    nontriviality R
    have : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact add_pow_char _ _ p

private theorem conjugatePower_spec {A R : Type*} [AddCommGroup A] [CommRing R]
    (e : A ≃+ R) (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) (x : A) :
    e (conjugatePower e p hp x) = e x ^ p := e.apply_symm_apply _

attribute [local irreducible] conjugatePower

private def powerNatTrans {C : Type v} [Category.{w} C]
    (F : C ⥤ AddCommGrpCat.{u₁}) (R : C → CommRingCat.{u₂})
    (r : ∀ {U V : C}, (U ⟶ V) → (R U ⟶ R V))
    (e : ∀ U : C, F.obj U ≃+ R U)
    (hn : ∀ (U V : C) (g : U ⟶ V) (x : F.obj U),
      e V (F.map g x) = r g (e U x))
    (p : ℕ) [Fact p.Prime] (hp : ∀ U, (p : R U) = 0) : F ⟶ F where
  app U := AddCommGrpCat.ofHom (conjugatePower (e U) p (hp U))
  naturality {U V} g := by
    ext x
    apply (e V).injective
    change e V (conjugatePower (e V) p (hp V) (F.map g x)) =
      e V (F.map g (conjugatePower (e U) p (hp U) x))
    rw [conjugatePower_spec, hn, hn, conjugatePower_spec, map_pow]

-- Use the explicit presentation of the canonical section equivalence, keeping
-- tensor restriction maps out of definitional-equality searches.
private abbrev tensorEtaleStructure (X : Scheme.{u}) :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf (unitObj X))

private def etalePower (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    tensorEtaleStructure X ⟶ tensorEtaleStructure X :=
  ⟨powerNatTrans (tensorEtaleStructure X).obj
    (fun U ↦ CommRingCat.of Γ(U.unop.left, ⊤)) (fun g ↦ g.unop.left.appTop)
    (etaleStructureSectionsEquiv X) (etaleStructureSectionsEquiv_naturality X) p
    (fun U ↦ by
      simpa only [map_natCast, map_zero] using congrArg U.unop.hom.appTop hp)⟩

private theorem etalePower_spec (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ)
    (s : (tensorEtaleStructure X).obj.obj U) :
    etaleStructureSectionsEquiv X U ((etalePower X p hp).hom.app U s) =
      etaleStructureSectionsEquiv X U s ^ p :=
  conjugatePower_spec (etaleStructureSectionsEquiv X U) p _ s

attribute [local irreducible] etalePower etaleStructureSectionsEquiv
  tensorStructureSectionsEquiv normalizedCoherentEtaleComparison moduleAbelianCohomologyLarge
  canonicalCoherentEtaleComparison coherentAdditiveEndomorphism structureCoherentFrobenius
  structureCoherentEtaleComparison

/-- Frobenius commutes with the canonical comparisons and field extension.
Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH.
(blueprint: lem-weil-pbc-coherent-frobenius-comparison).

Proof: The coherent power comparison gives semilinearity and the normalized
power square. Conjugating the latter by the fixed module/abelian comparison
gives the etale-to-coherent square. Properness of the base change supplies the
target comparison; its structural pullback square and hb give the third claim.
Construct the additive etale power map on Y by transporting p-th powers along
the canonical section equivalences. Characteristic p follows by pullback from k;
additivity also covers zero section rings. The section equation hu and map_pow
give its commutation with u, hence cohomology naturality gives the etale
Frobenius square. Transport this square through the two proper comparisons to
obtain coherent Frobenius pullback naturality. Finally K-linearity gives
b(a tensor v)=a*b(1 tensor v); semilinearity on Y and hb give the tensor formula.
No new bijectivity proof of b is needed, and neither field must be perfect. -/
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
        b ((a ^ p) ⊗ₜ[k] structureCoherentFrobenius f q FrZ v) := by
  let : IsProper g := MorphismProperty.of_isPullback h inferInstance
  have hpower := coherentPowerComparison f p q FrZ hFrZ
  have hs (x : Sheaf.H (structureTensorEtaleSheaf X) q) :
      structureCoherentEtaleComparison f q (Sheaf.H.map FrE q x) =
        structureCoherentFrobenius f q FrZ (structureCoherentEtaleComparison f q x) := by
    unfold structureCoherentEtaleComparison canonicalCoherentEtaleComparison
      structureCoherentFrobenius coherentAdditiveEndomorphism
    exact comparison_conjugate (moduleAbelianCohomologyLarge X (unit X) q).toEquiv
      (normalizedCoherentEtaleComparison f (unit X) q).toEquiv
      (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ FrZ q)
      (Sheaf.H.map FrE q)
      (hpower.2 FrE hFrE) x
  refine ⟨hpower.1, hs, ?_, ?_⟩
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
      have hpzero : (p : Γ(Y, ⊤)) = 0 := by
        let r : k →+* Γ(Y, ⊤) := j.appTop.hom.comp
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        simpa only [map_natCast, map_zero] using congrArg r (CharP.cast_eq_zero k p)
      let FrEY : structureTensorEtaleSheaf Y ⟶ structureTensorEtaleSheaf Y :=
        etalePower Y p hpzero
      have hFrEY (U : Y.Etaleᵒᵖ)
          (s : (structureTensorEtaleSheaf Y).obj.obj U) :
          (tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ (FrEY.hom.app U s).down =
            (@id Γ(U.unop.left, ⊤)
              ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ s.down)) ^ p := by
        have hh := etalePower_spec Y p hpzero U s
        unfold etaleStructureSectionsEquiv tensorStructureSectionsEquiv at hh
        exact hh
      have hc : (Etale.upperStar AddCommGrpCat.{u + 1} j).map FrE ≫ u = u ≫ FrEY := by
        apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
          (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y)).injective
        rw [Adjunction.homEquiv_naturality_left,
          Adjunction.homEquiv_naturality_right]
        ext U s
        have hi : IsIso (tensorPullbackObjUnitToUnit
            ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop).hom) :=
          (tensorPullbackObjUnitToUnit_isIso _).1
        apply ULift.down_injective
        apply (ConcreteCategory.bijective_of_isIso
          ((tensorPullbackObjUnitToUnit
            ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop).hom).app ⊤)).injective
        change (tensorPullbackObjUnitToUnit
            ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop).hom).app ⊤
          ((((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
            (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y) u).hom.app U
              (FrE.hom.app U s))).down = _
        rw [hu]
        change _ = (tensorPullbackObjUnitToUnit
            ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop).hom).app ⊤
          ((FrEY.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
              (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y) u).hom.app U
                s))).down
        rw [hFrEY (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U.unop)),
          hu, hFrE, map_pow]
        rfl
      have hn (x : Sheaf.H (structureTensorEtaleSheaf X) q) :
          Sheaf.H.map FrEY q
              (Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x)) =
            Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q
              (Sheaf.H.map FrE q x)) := by
        rw [Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply,
          ← Sheaf.H.map_comp_apply, hc]
      have hy (x : Sheaf.H (structureTensorEtaleSheaf Y) q) :
          structureCoherentEtaleComparison g q (Sheaf.H.map FrEY q x) =
            structureCoherentFrobenius g q FrZK (structureCoherentEtaleComparison g q x) := by
        unfold structureCoherentEtaleComparison canonicalCoherentEtaleComparison
          structureCoherentFrobenius coherentAdditiveEndomorphism
        exact comparison_conjugate (moduleAbelianCohomologyLarge Y (unit Y) q).toEquiv
          (normalizedCoherentEtaleComparison g (unit Y) q).toEquiv
          (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ FrZK q)
          (Sheaf.H.map FrEY q)
          ((coherentPowerComparison g p q FrZK hFrZK).2 FrEY hFrEY) x
      let x := (structureCoherentEtaleComparison f q).symm w
      have hx : structureCoherentEtaleComparison f q x = w :=
        (structureCoherentEtaleComparison f q).apply_symm_apply w
      have hxFr : structureCoherentEtaleComparison f q (Sheaf.H.map FrE q x) =
          structureCoherentFrobenius f q FrZ w :=
        (hs x).trans (congrArg (structureCoherentFrobenius f q FrZ) hx)
      calc
        _ = structureCoherentFrobenius g q FrZK
            (structureCoherentEtaleComparison g q
              (Sheaf.H.map u q
                (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x))) := by
          rw [coherentEtaleComparison_pullback f g j q u hu x, hx]
        _ = structureCoherentEtaleComparison g q
            (Sheaf.H.map FrEY q (Sheaf.H.map u q
              (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x))) := (hy _).symm
        _ = structureCoherentEtaleComparison g q
            (Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q
              (Sheaf.H.map FrE q x))) := congrArg _ (hn x)
        _ = _ := (coherentEtaleComparison_pullback f g j q u hu
          (Sheaf.H.map FrE q x)).trans (congrArg _ hxFr)
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
