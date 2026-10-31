/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpecifiedHomScalarEvaluation
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom

/-! # Specified scalar Hom evaluation on arbitrary schemes

Source: current Weil blueprint, sec-poincare-duality/sk-thm-frobenius,
prop-pod-dual-tate-data-compatibility, proof Step 5; Stacks Tag 08J9,
sites-cohomology.tex, lemma-internal-hom
(blueprint: lem-pod-specified-hom-scalar-evaluation).

The completion maps retain their quotient and zero shifted-product coordinates.
The chain statement identifies the specified completed operation on every permitted
K-flat/K-injective presentation, using the fixed localized resolution augmentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The specified completed Hom comparison is the ordinary evaluation transpose
conjugated by precisely the three quotient-augmentation comparisons.
Source: blueprint prop-pod-dual-tate-data-compatibility, proof Step 5; Stacks 08J9
(blueprint: lem-pod-specified-hom-scalar-evaluation).
Proof:
1. FiniteFreeCompletedScalarComparison gives finite freeness and the three invertible
quotient-augmentation maps, including their zero shifted-product coordinates.
RingedFiniteFreeHomBaseChange identifies the invertible ordinary evaluation transpose.
2. Choose flat-term K-flat representatives P and Q and a K-injective I by
lem-pc-kflat-resolution and prop-pur-kinjective-resolutions-exist. Exact scalar
extension and its localization factorization compute all three ordinary scalar objects.
3. The scalar chain evaluation of lem-sfb-scalar-hom-chain-evaluation sends
(x tensor s)(m tensor b) to j(q(x)(m) tensor sb). Its signed Hom differential agrees
with q and j because both scalars have degree zero.
4. Uncurry by lem-sfb-hom-kflat-chain-transpose. The normalized tensor comparison
sends the generator to (x tensor m) tensor sb, so the transpose is T(evaluation).
The input-first convention introduces the same Koszul sign on both routes.
5. Conjugate by the fixed completion maps as in scalarHomCompleted and cancel the
Hom-output inverse. This proves the equality of actual morphisms. Cancel the two
input comparisons and apply the inverse closed transpose to obtain the second clause.
Canonical localized resolution comparisons give independence of all representatives. -/
theorem specifiedHomScalarEvaluation_arbitraryScheme
    (W : Scheme.{u}) (_hl : ∀ x : W, IsUnit (l : W.presheaf.stalk x))
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N)
    (hH : sfIntegralConstructible l E W
      ((integralDerivedInternalHom l E W).obj (op M, N))) :
    ((scalarCompletion l E L ι W).app
        ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
      (scalarHomCompleted l E L ι W M N hM.1 hN.1 hH.1).hom =
      scalarHomOrdinary l E L ι W M N ≫
        (integralDerivedInternalHom l L W).map (Prod.mkHom
          ((scalarCompletionIso l E L ι W M hM.1).inv.op)
          ((scalarCompletionIso l E L ι W N hN.1).hom))) ∧
    ((scalarIntegralClosed l L W).transpose _
        ((integralOrdinaryDerivedScalar l E L ι W).obj M)
        ((integralOrdinaryDerivedScalar l E L ι W).obj N)).symm
      ((scalarCompletion l E L ι W).app
          ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
        (scalarHomCompleted l E L ι W M N hM.1 hN.1 hH.1).hom ≫
        (integralDerivedInternalHom l L W).map (Prod.mkHom
          ((scalarCompletionIso l E L ι W M hM.1).hom.op)
          ((scalarCompletionIso l E L ι W N hN.1).inv))) =
      (scalarClosedTensor l E L ι W).inv.app
        ((integralDerivedInternalHom l E W).obj (op M, N), M) ≫
      (integralOrdinaryDerivedScalar l E L ι W).map
        ((scalarIntegralClosed l E W).evaluation M N) := by
  constructor
  · simp [scalarHomCompleted, scalarCompletionIso]
  · have hcancel :
        (scalarCompletion l E L ι W).app
            ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
          (scalarHomCompleted l E L ι W M N hM.1 hN.1 hH.1).hom ≫
          (integralDerivedInternalHom l L W).map (Prod.mkHom
            ((scalarCompletionIso l E L ι W M hM.1).hom.op)
            ((scalarCompletionIso l E L ι W N hN.1).inv)) =
        scalarHomOrdinary l E L ι W M N := by
      simp only [scalarHomCompleted, scalarCompletionIso, Iso.op_symm, Iso.trans_hom,
        Iso.symm_hom, asIso_inv, asIso_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.op_inv,
        op_inv, Category.assoc, ← Functor.map_comp, prod_comp, IsIso.inv_hom_id,
        IsIso.hom_inv_id, Bifunctor.map_id, IsIso.hom_inv_id_assoc]
      exact Category.comp_id (scalarHomOrdinary l E L ι W M N)
    rw [hcancel]
    exact Equiv.symm_apply_apply _ _

/-- The prescribed chain formula localizes to the actual completed operation comparison.
The fixed augmentation and actual Hom-product projections are used in every section.
Source: blueprint prop-pod-dual-tate-data-compatibility, proof Step 5; Stacks 0A8X, 08J9
(blueprint: lem-pod-specified-hom-scalar-evaluation).
Proof:
1. Use lem-sfb-scalar-hom-chain-evaluation and precompose with q tensor 1.
Its balanced section formula defines a chain map: d(h)=d_I h-(-1)^r h d_P,
and q and the fixed augmentation are chain maps. Restrictions commute with evaluation.
The sheafified pure tensors and actual Hom projections give uniqueness.
2. Uncurry with lem-sfb-hom-kflat-chain-transpose and use the generator normalization
of lem-sf-ringed-finite-free-tensor-data. The result is scalar-extended evaluation,
with the same Koszul sign if the tensor factors are exchanged.
3. Localize using the exact scalar factorization, the fixed Hom factorization and
inverse localized augmentation. This identifies the chain map with scalarHomOrdinary.
4. The first theorem identifies that map with the displayed composite through the
specified completed comparison. Its completion maps are the actual quotient maps with
zero shifted coordinates. Thus the chain construction equals that comparison;
canonical localized resolution comparisons prove independence of representatives. -/
theorem specifiedCompletedHomScalarChain
    (X : Scheme.{u}) (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (P I Q : CochainComplex (integralTowerModules l E X) ℤ)
    (_hP : integralOperationsGoodComplex l E X P)
    (_hQ : integralOperationsGoodComplex l E X Q) [I.IsKInjective]
    (hM : sfIntegralConstructible l E X (DerivedCategory.Q.obj P))
    (hN : sfIntegralConstructible l E X (DerivedCategory.Q.obj I))
    (hH : sfIntegralConstructible l E X
      ((integralDerivedInternalHom l E X).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)))
    (q : Q ⟶ homComplex (R := completedIntegralCommRingSheafUnrestricted l E X) P I)
    [QuasiIso q] :
    ∃! δ : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      homComplex (R := completedIntegralCommRingSheafUnrestricted l L X)
        (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P)
        ((coefficientHomResolution.{u, u+1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X)).obj
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)),
      (∀ (r m : ℤ) (U : X.ProEtᵒᵖ) (x : (Q.X r).val.obj U) (y : (P.X m).val.obj U)
        (s b : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U),
        coefficientHomSectionEvaluation.{u, u+1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X) _ _ _ δ r m (m+r) rfl U
          (integralOrdinaryTensorSection l E L ι X (Q.X r) U s x)
          (integralOrdinaryTensorSection l E L ι X (P.X m) U b y) =
        ((((specifiedHomResolutionUnit l L X).app
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)).f
          (m+r)).val.app U)
          (integralOrdinaryTensorSection l E L ι X (I.X (m+r)) U (s*b)
            (((((coefficientHomComponent.{u, u+1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I r m (m+r) rfl).val.app U
                ((q.f r).val.app U x)).app
                  (op (CategoryTheory.Over.mk (𝟙 U.unop)))).hom) y))) ∧
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map δ =
        (integralOrdinaryDerivedScalar l E L ι X).map
          (DerivedCategory.Q.map q ≫
            DerivedCategory.Q.map
              ((homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E X)).obj
                (op P) |>.map ((specifiedHomResolutionUnit l E X).app I)) ≫
            (coefficientHomResolutionIso.{u, u+1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I).inv) ≫
          (scalarCompletion l E L ι X).app
            ((integralDerivedInternalHom l E X).obj
              (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) ≫
          (scalarHomCompleted l E L ι X (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj I) hM.1 hN.1 hH.1).hom ≫
          (integralDerivedInternalHom l L X).map (Prod.mkHom
            ((scalarCompletionIso l E L ι X (DerivedCategory.Q.obj P) hM.1).hom.op)
            ((scalarCompletionIso l E L ι X (DerivedCategory.Q.obj I) hN.1).inv)) ≫
          (integralDerivedInternalHom l L X).map (Prod.mkHom
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.inv.app P).op
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app I)) ≫
          (coefficientHomResolutionIso.{u, u+1, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l L X) _ _).hom := by
  have hcancel := (specifiedHomScalarEvaluation_arbitraryScheme
    l E L ι X _hl (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) hM hN hH).2
  have heq := congrArg
    ((scalarIntegralClosed l L X).transpose _
      ((integralOrdinaryDerivedScalar l E L ι X).obj (DerivedCategory.Q.obj P))
      ((integralOrdinaryDerivedScalar l E L ι X).obj (DerivedCategory.Q.obj I))) hcancel
  simp only [Equiv.apply_symm_apply] at heq
  change _ = scalarHomOrdinary l E L ι X _ _ at heq
  have heq_assoc := reassoc_of% heq
  obtain ⟨δ, hδ, huniq⟩ := specifiedHomScalarChain l E L ι X P I Q _hP _hQ hM hN q
  refine ⟨δ, ⟨hδ.1, ?_⟩, ?_⟩
  · simpa only [Category.assoc, heq_assoc] using hδ.2
  · intro δ' hδ'
    apply huniq δ'
    exact ⟨hδ'.1, by simpa only [Category.assoc, heq_assoc] using hδ'.2⟩

end WeilConjectures
