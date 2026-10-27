/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.Algebra.Lie.KostantIntegralPBW
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyIntegralRootModel

/-! # Positive Kostant forms and Borel distributions

Source: Mathieu, Tilting Modules and their Applications (2000), Section 1,
pp.150--151; Milne, Algebraic Groups (2017), Section 23h, pp.509--511.
(blueprint: lem-sfb-borel-kostant-distribution-comparison)

The codomain is expressed inside the full convolution dual: the image of every
argument annihilates some power of the augmentation ideal. This is precisely a
homomorphism into the union of the finite-order duals, with its inherited product.
No multiplication or factorial division in the positive-characteristic field is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.BorelKostantDistribution

/-- The canonical divided-power generator in the positive integer subalgebra.
The latter is the recorded Kostant construction restricted to positive root vectors.
Source: Mathieu, Section 1, pp.150--151; Milne, Section 23h, equation (153).
(blueprint: lem-sfb-borel-kostant-distribution-comparison). -/
def positiveGenerator {L : Type u} [LieRing L] [LieAlgebra ℚ L]
    {I : Type v} (e : I → L) (i : I) (m : ℕ) : LieAlgebra.kostantIntegralForm e :=
  ⟨Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e i)) m,
    Algebra.subset_adjoin ⟨i, m, rfl⟩⟩

/-- A prescribed simple-root pinning extends to all positive roots and a rational
Chevalley basis, and their divided powers map to the corresponding coefficient
functionals in the geometric distribution algebra.
Source: Mathieu, Section 1, pp.150--151; Milne, Section 23h, pp.509--511.
(blueprint: lem-sfb-borel-kostant-distribution-comparison).

Proof plan:
1. Apply lem-sfb-chevalley-integral-root-model with the prescribed simple maps.
   Its ordered root chart identifies the integral unipotent coordinate ring and
   augmentation ideal with Z[t_1,...,t_N] and (t_1,...,t_N). The duals of the
   truncated rings have coefficient bases delta_a for total degree at most d.
   Their union L consists of finite sums of coefficient functionals.
2. The integral coproduct carries the augmentation ideal into I tensor A + A tensor I.
   In a product of a+b+1 such terms either the first factor lies in I^(a+1) or
   the second lies in I^(b+1). Convolution therefore preserves finite order and
   is unital and associative by the counit and coassociativity identities.
   Each root coefficient functional d_beta,m has order at most m.
3. Apply lem-sfb-characteristic-zero-distribution-enveloping to the rational model.
   In Dist(Ga_Q), q_a q_b = binomial(a+b,a) q_(a+b), hence q_1^m = m! q_m.
   Naturality sends the rational divided power e_beta^m/m! to the root coefficient
   functional. All divisions occur over Q.
4. Extend L rationally and precompose with restriction from the full group.
   This gives an injective unital ring map j into its rational distributions:
   injectivity follows from the coefficient basis and the closed immersion U into G.
   Every positive divided-power generator has image in j(L). The integer algebra
   it generates therefore maps into j(L), and unique preimages define a unital
   integer algebra map theta from the positive Kostant form into L.
5. The coefficient bases identify F tensor_Z L with Dist(U_F). Evaluating the
   coproduct of an integral monomial checks multiplicativity on basis elements;
   bilinearity gives it for all distributions. Coefficient extraction commutes
   with scalar extension and the counit gives the unit.
6. Transport through the model isomorphism to U and compose with F tensor theta.
   This gives Psi and the displayed coefficient formula for every positive root,
   m and regular function. The model supplies the rational Lie algebra and based
   root identification. Empty roots give L = Z and the scalar identity F to F.
   No step uses an identification of a reduced integral Lie algebra with Lie(S). -/
theorem exists_borel_kostant_distribution_comparison
    (F : Type u) [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S T B U : Grp (Over (Spec (.of F)))) [IsAffine U.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (jT : T ⟶ B) (iU : U ⟶ B)
    (hTB : jT ≫ iB = iT)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ U, f ≫ iU = iN)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    [ModObj T.X S.X] [ModObj T.X B.X]
    (hconjS : γ[T.X,S.X] = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : γ[T.X,B.X] = (jT.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    [P.IsReduced] (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ TorusCharacterTangent.weightSpace T S χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      TorusCharacterTangent.weightSpace T B α.val.toMul ≠ ⊥)
    (Ua : Φ → Grp (Over (Spec (.of F)))) (ia : ∀ α : Φ, Ua α ⟶ S)
    (hua : ∀ α : Φ, IsClosedSubgroupScheme (ia α).hom.hom ∧
      Smooth (Ua α).X.hom ∧ ConnectedSpace (Ua α).X.left ∧
      TorusCharacterTangent.IsStable T S (ia α) ∧
      (GrpObj.differential (ia α).hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S α.val.toMul ∧
      Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ Ua α))
    (x : ∀ α : b.support, Grp.mk (StandardGroupSchemes.additive F) ≅ Ua α) :
    ∃ (L : Type u) (_ : LieRing L) (_ : LieAlgebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : LieAlgebra.HasTrivialRadical ℚ L)
      (H : LieSubalgebra ℚ L) (_ : IsLieAbelian H)
      (Q : RootPairing Φ ℚ (Module.Dual ℚ H) H)
      (_ : Q.IsRootSystem) (_ : Q.IsCrystallographic) (_ : Q.IsReduced)
      (bQ : Q.Base) (e : Φ → L),
      (∀ K : LieSubalgebra ℚ L, H ≤ K → IsLieAbelian K → K = H) ∧
      (∀ (a : Module.Dual ℚ H) (h : H), Q.toLinearMap a h = a h) ∧
      bQ.support = b.support ∧
      (∀ α β : Φ, Q.pairing α β = (P.pairing α β : ℚ)) ∧
      (∀ α : Φ, e α ∈ LieModule.weightSpace L (Q.root α) ∧ e α ≠ 0) ∧
      (∀ α : Φ, ⁅e α, e (Q.reflectionPerm α α)⁆ = (Q.coroot α : L)) ∧
      (∀ α β κ : Φ, Q.root α + Q.root β = Q.root κ →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ⁅e α, e β⁆ = ((ε : ℚ) * (Q.chainBotCoeff α β + 1)) • e κ) ∧
      (∀ α β : Φ, Q.root α + Q.root β ∉ Set.range Q.root →
        Q.root α + Q.root β ≠ 0 → ⁅e α, e β⁆ = 0) ∧
      (∃ C : Module.Basis (bQ.support ⊕ Φ) ℚ L,
        (∀ α : bQ.support, C (Sum.inl α) = (Q.coroot α : L)) ∧
        ∀ α : Φ, C (Sum.inr α) = e α) ∧
      ∃ (xp : ∀ β : {α : Φ // b.IsPos α},
          Grp.mk (StandardGroupSchemes.additive F) ≅ Ua β.val)
        (z : ∀ β : {α : Φ // b.IsPos α},
          Grp.mk (StandardGroupSchemes.additive F) ⟶ U),
        (∀ α : b.support, xp ⟨α.val, b.isPos_of_mem_support α.property⟩ = x α) ∧
        (∀ β : {α : Φ // b.IsPos α},
          z β ≫ iU ≫ iB = (xp β).hom ≫ ia β.val) ∧
        ∃ Ψ : F ⊗[ℤ] LieAlgebra.kostantIntegralForm
            (fun β : {α : Φ // b.IsPos α} ↦ e β.val) →ₐ[F]
            WithConv (Module.Dual F (RationalHighestWeight.coordinateAlgebra U)),
          (∀ a, ∃ d : ℕ, ∀ f ∈
            RingHom.ker (Bialgebra.counitAlgHom F
              (RationalHighestWeight.coordinateAlgebra U)).toRingHom ^ (d + 1),
            (Ψ a).ofConv f = 0) ∧
          ∀ (β : {α : Φ // b.IsPos α}) (m : ℕ)
            (f : RationalHighestWeight.coordinateAlgebra U),
            (Ψ (1 ⊗ₜ[ℤ] positiveGenerator
              (fun κ : {α : Φ // b.IsPos α} ↦ e κ.val) β m)).ofConv f =
              ((Scheme.ΓSpecIso (.of (Polynomial F))).hom
                ((z β).hom.hom.left.appTop f)).coeff m := by
  sorry

end AlgebraicGeometry.BorelKostantDistribution
