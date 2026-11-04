/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Cofinal coefficient quotient maps and completed projections

Source: blueprint, sec-smooth-purity, sk-lem-sp-tower proof, final integral-constructibility
sentence; sk-def-sp-coefficient-towers, first paragraph; integral-limit clause (3).
(blueprint: lem-sp-cofinal-coefficient-projection-cocone).

The natural indices n and j denote positive exponents n+1 and j+1. Both coefficient
and scheme universes are independent. The completed ell projection is the projection
through the uniquely normalized comparison already supplied by the coefficient tower.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u w z

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The actual constant ring-sheaf map induced by the inclusion of coefficient ideals.
Its ordinary quotient homomorphism sends the class of x to the class of x.
Source: blueprint, sk-lem-sp-tower proof, final integral-constructibility sentence
(blueprint: lem-sp-cofinal-coefficient-projection-cocone). -/
def spCofinalCoefficientMap {n j : ℕ}
    (h : spEllIdeal l E ^ (n + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1)) :
    spCoefficientRing l E T n ⟶ integralCoefficientSheaf l E T j :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.factor h).comp ULift.ringEquiv.toRingHom))))

private theorem constantRing_surjective {C : Type z} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private theorem proEt_preservesSheafification :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget CommRingCat.{max u (t + 1)}) := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  let K := (equivSmallModel.{max u (t + 1)} T.ProEt).inverse.inducedTopology
    (Scheme.ProEt.topology T)
  have : K.PreservesSheafification (forget CommRingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification K _
      (FD := fun A B : CommRingCat.{max u (t + 1)} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u (t + 1)} ↦ A)
      (FE := fun A B : Type (max u (t + 1)) ↦ TypeCat.Fun A B)
      (CE := fun A : Type (max u (t + 1)) ↦ A)
  exact GrothendieckTopology.PreservesSheafification.transport
    (Scheme.ProEt.topology T) K
    (equivSmallModel.{max u (t + 1)} T.ProEt).inverse _ _

private theorem ellQuotient_surjective (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((spCoefficientConstantQuotient l E T n).hom.app U) := by
  have := proEt_preservesSheafification.{t, u} T
  apply constantRing_surjective
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
  refine ⟨ULift.up a, ?_⟩
  apply ULift.ext
  exact ha

private theorem cofinalMap_scalar {n j : ℕ}
    (h : spEllIdeal l E ^ (n + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1)) :
    spCoefficientConstantQuotient l E T n ≫ spCofinalCoefficientMap l E T h =
      integralConstantQuotientOfUniverses l E T j := by
  unfold spCoefficientConstantQuotient spCofinalCoefficientMap
    integralConstantQuotientOfUniverses
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

private def ellScalarCone : Cone (spCoefficientRings l E T) where
  pt := integralConstantRingOfUniverses l E T
  π := NatTrans.ofOpSequence (spCoefficientConstantQuotient l E T) (fun n ↦ by
    simp only [Functor.const_obj_map, spCoefficientRings,
      Functor.ofOpSequence_map_homOfLE_succ]
    unfold spCoefficientConstantQuotient spCoefficientReduction
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 2)

private theorem ellScalar_naturality (n m : ℕ) (h : m ≤ n) :
    spCoefficientConstantQuotient l E T n ≫
      (spCoefficientRings l E T).map (homOfLE h).op =
        spCoefficientConstantQuotient l E T m := by
  exact ((ellScalarCone l E T).π.naturality (homOfLE h).op).symm.trans
    (Category.id_comp _)

private theorem uniformizerScalar_naturality (j k : ℕ) (h : k ≤ j) :
    integralConstantQuotientOfUniverses l E T j ≫
      (integralCoefficientSheafSystem l E T).map (homOfLE h).op =
        integralConstantQuotientOfUniverses l E T k := by
  exact ((integralConstantConeOfUniverses l E T).π.naturality (homOfLE h).op).symm.trans
    (Category.id_comp _)

private theorem cancel_ellScalar (n : ℕ)
    {A : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}}
    (f g : spCoefficientRing l E T n ⟶ A)
    (h : spCoefficientConstantQuotient l E T n ≫ f =
      spCoefficientConstantQuotient l E T n ≫ g) : f = g := by
  ext U x
  obtain ⟨y, rfl⟩ := ellQuotient_surjective l E T n U x
  exact congrArg (fun k ↦ k.hom.app U y) h

/-- The ell-power and uniformizer-power quotients, with their completed projections,
form a single commuting diagram of actual quotient maps. Surjectivity is sectionwise.
Source: blueprint, sk-lem-sp-tower proof, final integral-constructibility sentence;
sk-def-sp-coefficient-towers; integral-limit clause (3)
(blueprint: lem-sp-cofinal-coefficient-projection-cocone).

Proof: (1) The unit factorization ell = v*pi^e gives (ell^N) = (pi^(e*N)), so
j <= e*N gives the asserted ideal inclusion. The quotient factor sends [x] to [x]
and is surjective on representatives. The finite uniformizer quotients supplied by
`def-weil-l-adic-coefficient-extension` give finiteness of both rings; ell^N belongs
to both defining ideals and hence annihilates them.
(2) Apply constant commutative-ring sheafification and then forget commutativity.
A set-theoretic section of the ordinary surjection sheafifies to a section of its
underlying set map: use `lem-pc-sites-sheafification-underlying-sets` to identify this
with the underlying map of the ring sheafification. Thus the map is surjective on
every object's sections; no ring-homomorphic section is claimed.
(3) Both composites with a quotient transition send [x] to [x] in the final quotient.
Equality on representatives and functoriality of constant sheafification give the
two squares. The same argument includes identities and all composite reductions.
(4) Clause (3) of `det-prop-sfb-qlbar-colimit-x-integral-limit` identifies the completed
ring with the uniformizer limit. Its cofinal ell-power comparison sends a compatible
family y to the family with Nth coordinate y_(e*N), transported by the quotient
identification (pi^(e*N)) = (ell^N). Conversely its jth coordinate is q_(N,j)(z_N)
for any e*N >= j; step (3) proves independence and compatibility. The composites
are identities coordinatewise. This comparison agrees with constant quotient maps,
so uniqueness in `sp_completed_coefficient_limit` identifies it with the recorded
comparison. Consequently beta_N followed by q_(N,j) is delta_j. The limit cone laws
also give compatibility of both completed projections with all reductions. No step
uses invertibility of ell on T or assumes e = 1. -/
theorem sp_cofinal_coefficient_projection_cocone
    (e : ℕ) (_he : 1 ≤ e) (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (_hv : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e) :
    ∃ H : ∀ (n j : ℕ), j + 1 ≤ e * (n + 1) →
        spEllIdeal l E ^ (n + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1),
      (∀ (n j : ℕ) (h : j + 1 ≤ e * (n + 1)),
        (∀ x : Padic.coefficientExtensionIntegers l E,
          Ideal.Quotient.factor (H n j h)
            (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)) x) =
              Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (j + 1)) x) ∧
        Function.Surjective (Ideal.Quotient.factor (H n j h)) ∧
        (∀ U : T.ProEtᵒᵖ,
          Function.Surjective ((spCofinalCoefficientMap l E T (H n j h)).hom.app U)) ∧
        ((sp_completed_coefficient_limit l E T).choose.hom ≫
          limit.π (spCoefficientRings l E T) (op n)) ≫
            spCofinalCoefficientMap l E T (H n j h) =
              limit.π (integralCoefficientSheafSystem l E T) (op j) ∧
        Finite (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) ∧
        Finite (Padic.coefficientExtensionRing l E (j + 1)) ∧
        (l ^ (n + 1) :
          Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) = 0 ∧
        (l ^ (n + 1) : Padic.coefficientExtensionRing l E (j + 1)) = 0) ∧
      (∀ (n m j : ℕ) (hnm : m ≤ n) (hmj : j + 1 ≤ e * (m + 1))
          (hnj : j + 1 ≤ e * (n + 1)),
        (spCoefficientRings l E T).map (homOfLE hnm).op ≫
          spCofinalCoefficientMap l E T (H m j hmj) =
            spCofinalCoefficientMap l E T (H n j hnj)) ∧
      (∀ (n j k : ℕ) (hjk : k ≤ j) (hnj : j + 1 ≤ e * (n + 1))
          (hnk : k + 1 ≤ e * (n + 1)),
        spCofinalCoefficientMap l E T (H n j hnj) ≫
          (integralCoefficientSheafSystem l E T).map (homOfLE hjk).op =
            spCofinalCoefficientMap l E T (H n k hnk)) ∧
      (∀ (n m : ℕ) (h : m ≤ n),
        ((sp_completed_coefficient_limit l E T).choose.hom ≫
          limit.π (spCoefficientRings l E T) (op n)) ≫
            (spCoefficientRings l E T).map (homOfLE h).op =
              (sp_completed_coefficient_limit l E T).choose.hom ≫
                limit.π (spCoefficientRings l E T) (op m)) ∧
      (∀ (j k : ℕ) (h : k ≤ j),
        limit.π (integralCoefficientSheafSystem l E T) (op j) ≫
          (integralCoefficientSheafSystem l E T).map (homOfLE h).op =
            limit.π (integralCoefficientSheafSystem l E T) (op k)) ∧
      (∀ n : ℕ,
        (spCoefficientRings l E T).map (𝟙 (op n)) = 𝟙 _ ∧
        (integralCoefficientSheafSystem l E T).map (𝟙 (op n)) = 𝟙 _) ∧
      (∀ (n m k : ℕ) (h₁ : m ≤ n) (h₂ : k ≤ m),
        (spCoefficientRings l E T).map (homOfLE h₁).op ≫
          (spCoefficientRings l E T).map (homOfLE h₂).op =
            (spCoefficientRings l E T).map (homOfLE (h₂.trans h₁)).op ∧
        (integralCoefficientSheafSystem l E T).map (homOfLE h₁).op ≫
          (integralCoefficientSheafSystem l E T).map (homOfLE h₂).op =
            (integralCoefficientSheafSystem l E T).map (homOfLE (h₂.trans h₁)).op) := by
  have hell : spEllIdeal l E =
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ e := by
    unfold spEllIdeal
    rw [_hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow]
  have hpow (n : ℕ) : spEllIdeal l E ^ (n + 1) =
      Padic.coefficientExtensionIdeal l E (e * (n + 1)) := by
    rw [hell, ← pow_mul]
    rfl
  let H (n j : ℕ) (h : j + 1 ≤ e * (n + 1)) :
      spEllIdeal l E ^ (n + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1) := by
    rw [hpow]
    exact Ideal.pow_le_pow_right h
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n j h
    refine ⟨Ideal.Quotient.factor_mk _, Ideal.Quotient.factor_surjective _, ?_, ?_,
      ?_, Padic.finite_coefficientExtensionRing l E (j + 1) (Nat.succ_pos j), ?_, ?_⟩
    · have := proEt_preservesSheafification.{t, u} T
      apply constantRing_surjective
      intro b
      obtain ⟨a, ha⟩ := Ideal.Quotient.factor_surjective (H n j h) b.down
      refine ⟨ULift.up a, ?_⟩
      apply ULift.ext
      exact ha
    · apply completedIntegralFiniteQuotientHom_ext l E T
        (Padic.coefficientExtensionIdeal l E (j + 1)) ⟨j, le_rfl⟩
      · have hn := congrArg (fun f ↦ f ≫ spCofinalCoefficientMap l E T (H n j h))
          ((sp_completed_coefficient_limit l E T).choose_spec.1 n)
        exact (Category.assoc _ _ _).symm.trans
          (hn.trans (cofinalMap_scalar l E T (H n j h)))
      · exact limit.lift_π _ _
    · rw [hpow]
      exact Padic.finite_coefficientExtensionRing l E (e * (n + 1))
        ((Nat.succ_pos n).trans_le (Nat.le_mul_of_pos_left (n + 1) _he))
    · have hmem : (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
          spEllIdeal l E ^ (n + 1) :=
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
      simpa only [map_pow, map_natCast] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    · have hmem : (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
          spEllIdeal l E ^ (n + 1) :=
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
      simpa only [map_pow, map_natCast] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr (H n j h hmem))
  · intro n m j hnm hmj hnj
    apply cancel_ellScalar l E T n
    rw [← Category.assoc, ellScalar_naturality, cofinalMap_scalar, cofinalMap_scalar]
  · intro n j k hjk hnj hnk
    apply cancel_ellScalar l E T n
    rw [← Category.assoc, cofinalMap_scalar, uniformizerScalar_naturality,
      cofinalMap_scalar]
  · intro n m h
    rw [Category.assoc, limit.w]
  · intro j k h
    exact limit.w _ _
  · intro n
    exact ⟨(spCoefficientRings l E T).map_id _,
      (integralCoefficientSheafSystem l E T).map_id _⟩
  · intro n m k h₁ h₂
    constructor
    · simpa only [← Functor.map_comp] using
        congrArg (spCoefficientRings l E T).map
          (Subsingleton.elim ((homOfLE h₁).op ≫ (homOfLE h₂).op)
            (homOfLE (h₂.trans h₁)).op)
    · simpa only [← Functor.map_comp] using
        congrArg (integralCoefficientSheafSystem l E T).map
          (Subsingleton.elim ((homOfLE h₁).op ≫ (homOfLE h₂).op)
            (homOfLE (h₂.trans h₁)).op)

end AlgebraicGeometry.ProEtale
