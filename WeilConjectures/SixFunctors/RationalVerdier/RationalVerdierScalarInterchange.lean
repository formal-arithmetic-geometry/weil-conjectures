/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierPairingCalculus
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletedInterchangeCanonical
import WeilConjectures.SmoothPurity.Integral.IntegralBraidingScalarExtensionSquare

/-! # Scalar extension respects the normalized signed interchange

Source: blueprint thm-coef-rational-verdier, paragraph 3, second transposition.
(blueprint: lem-coef-rational-verdier-scalar-interchange). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Completed integral scalar extension preserves the signed swaps conjugated by the
normalized completion maps. No rationalization or duality comparison occurs here.
Source: blueprint thm-coef-rational-verdier, paragraph 3; integral finite extension,
evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-scalar-interchange).

Proof: choose flat-term K-flat representatives for the two integral constructible
objects. On homogeneous local tensors in degrees p,q the ordinary swap is
(-1)^(pq) times interchange. The scalar tensorator multiplies coefficient factors
of degree zero, so the two orders of applying it and the swap agree. The supplied
symmetries have precisely this representative equation. Ambient naturality transports
the identity across the representing isomorphisms, so it holds on the ordinary
presentations. The normalized completion maps respect the equation: in each positive
quotient both paths are the same quotient tensor map, while each shifted mapping-fiber
coordinate is zero. Equality of these coordinates gives the completion square, and
localization at quasi-isomorphisms gives the completed derived square. Finally conjugate
by the invertible completion comparisons on the two constructible inputs and use the
normalization of integralTensorScalarComparison. No dualizing object or evaluation
identity is used in this calculation, and zero complexes and identity scalar extensions
satisfy the same formulas. -/
theorem integral_scalar_interchange
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (hB : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (f : K ⟶ K') (g : M ⟶ M'),
      B.ordinary.tensor.map (Prod.mkHom f g) ≫ (B.symmetry.swap K' M').hom =
        (B.symmetry.swap K M).hom ≫ B.ordinary.tensor.map (Prod.mkHom g f))
    (K M : sfIntegralConstructibleCategory l E X) :
    (integralScalar l X E L i).map (completedInterchange D l hl X E wE A K M) ≫
        (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X
          (units D l hl X) M K).hom =
      (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X
          (units D l hl X) K M).hom ≫
        completedInterchange D l hl X L wL B
          ((integralScalar l X E L i).obj K) ((integralScalar l X E L i).obj M) := by
  rw [completedInterchange_eq_integralBraiding D l hl X E wE A hA K M]
  rw [completedInterchange_eq_integralBraiding D l hl X L wL B hB
    ((integralScalar l X E L i).obj K) ((integralScalar l X E L i).obj M)]
  exact @integralBraidingScalarExtensionSquare l _ E L _ _ _ _ _ _ i X
    (units D l hl X) K M

private theorem map_heq {C : Type*} [Category* C] {C' : Type*} [Category* C']
    (F : C ⥤ C') {K M K' M' : C} (hK : K = K') (hM : M = M')
    {f : K ⟶ M} {g : K' ⟶ M'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK
  cases hM
  cases h
  rfl

/-- The completed rational scalar tensorator preserves the normalized Koszul interchange.
This assertion involves no duality comparison, evaluation square, or double-dual map.
Source: blueprint thm-coef-rational-verdier, paragraph 3, transposition; integral
finite extension proof, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-scalar-interchange).

Proof: first work on K-flat representatives with flat terms. The signed chain swap
multiplies a homogeneous tensor of degrees p,q by (-1)^(pq). Ordinary coefficient
extension has degree zero, so interchanging before or after coefficient extension
has the same sign and the same coefficient product. The representative equations
of the supplied symmetries, together with ambient naturality, extend this identity
from K-flat representatives to all derived objects by conjugation with their representing
isomorphisms. The quotient-normalized completion maps commute with this identity:
each reduction coordinate is the quotient of the same pure tensor, and the shifted
mapping-fiber coordinate is zero on both paths. Conjugating by those completion maps
gives the identity for completed integral tensor. Localize it and use the defining
pure-tensor normalization of rationalTensorScalarComparison. The integral fields of
the two supplied calculi identify their swaps with exactly these localized maps.
All raw rational objects are integral representatives; the equality follows for all
pairs. The calculation includes identity embeddings, zero objects and empty X. -/
theorem scalar_interchange
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (hB : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (f : K ⟶ K') (g : M ⟶ M'),
      B.ordinary.tensor.map (Prod.mkHom f g) ≫ (B.symmetry.swap K' M').hom =
        (B.symmetry.swap K M).hom ≫ B.ordinary.tensor.map (Prod.mkHom g f))
    (sA : PairingCalculus D l hl X E wE A)
    (sB : PairingCalculus D l hl X L wL B) :
    ∀ K M : sfRationalConstructibleCategory l E X,
      sB.swap ((scalar l X E L i).obj K) ((scalar l X E L i).obj M) ≫
          (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X
            (units D l hl X)).inv.app (M, K) =
        (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X
            (units D l hl X)).inv.app (K, M) ≫
          (scalar l X E L i).map (sA.swap K M) := by
  let J := sfRationalConstructibleLocalization l E X
  let Q := sfRationalConstructibleLocalization l L X
  let T := integralScalar l X E L i
  let F := scalar l X E L i
  let TE := integralTensor D l hl X E
  let TL := integralTensor D l hl X L
  let RE := tensor D l hl X E
  let RL := tensor D l hl X L
  let mu := @rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)
  have hF (K : sfRationalConstructibleCategory l E X) : F.obj K = Q.obj (T.obj K.obj) :=
    sfRationalScalarExtension_obj l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i K
  have hRE (K M : sfRationalConstructibleCategory l E X) :
      RE.obj (K, M) = J.obj (TE.obj (K.obj, M.obj)) :=
    (@rationalDerivedTensor_existsUnique l _ E _ _ _ X (units D l hl X)).exists.choose_spec.1
      (K, M)
  have hRL (K M : sfRationalConstructibleCategory l L X) :
      RL.obj (K, M) = Q.obj (TL.obj (K.obj, M.obj)) :=
    (@rationalDerivedTensor_existsUnique l _ L _ _ _ X (units D l hl X)).exists.choose_spec.1
      (K, M)
  have hsource (K M : sfRationalConstructibleCategory l E X) :
      F.obj (RE.obj (K, M)) = Q.obj (T.obj (TE.obj (K.obj, M.obj))) := by
    rw [hRE, hF]
    rfl
  have htarget (K M : sfRationalConstructibleCategory l E X) :
      RL.obj (F.obj K, F.obj M) = Q.obj (TL.obj (T.obj K.obj, T.obj M.obj)) := by
    rw [hF K, hF M, hRL]
    rfl
  have hmu (K M : sfRationalConstructibleCategory l E X) :
      HEq (mu.hom.app (K, M))
        (Q.map (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X
          (units D l hl X) K.obj M.obj).hom) :=
    (@rationalTensorScalarComparison_existsUnique l _ E _ _ _ L _ _ _ i X
      (units D l hl X)).exists.choose_spec K M
  have hmap (K M : sfRationalConstructibleCategory l E X) :
      HEq (F.map (sA.swap K M))
        (Q.map (T.map (completedInterchange D l hl X E wE A K.obj M.obj))) := by
    have h := map_heq F (hRE K M) (hRE M K) (sA.integral K.obj M.obj)
    have ht := sfRationalScalarExtension_map_tmul l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i _ _
      (completedInterchange D l hl X E wE A K.obj M.obj) 1
    simp only [map_one] at ht
    exact h.trans ht
  have hswap (K M : sfRationalConstructibleCategory l E X) :
      HEq (sB.swap (F.obj K) (F.obj M))
        (Q.map (completedInterchange D l hl X L wL B (T.obj K.obj) (T.obj M.obj))) := by
    rw [hF K, hF M]
    exact sB.integral _ _
  intro K M
  have hhom : F.map (sA.swap K M) ≫ mu.hom.app (M, K) =
      mu.hom.app (K, M) ≫ sB.swap (F.obj K) (F.obj M) := by
    have hleft := heq_comp (hsource K M) (hsource M K) (htarget M K)
      (hmap K M) (hmu M K)
    have hright := heq_comp (hsource K M) (htarget K M) (htarget M K)
      (hmu K M) (hswap K M)
    have hi := congrArg Q.map
      (integral_scalar_interchange D l hl X E L i wE wL A B hA hB K.obj M.obj)
    simp only [Functor.map_comp] at hi
    exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))
  change sB.swap (F.obj K) (F.obj M) ≫ mu.inv.app (M, K) =
    mu.inv.app (K, M) ≫ F.map (sA.swap K M)
  apply (cancel_epi (mu.hom.app (K, M))).1
  apply (cancel_mono (mu.hom.app (M, K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc]
  exact (congrArg (fun q ↦ mu.hom.app (K, M) ≫ q)
    (Category.comp_id (sB.swap (F.obj K) (F.obj M)))).trans hhom.symm

end WeilConjectures.RationalVerdier
