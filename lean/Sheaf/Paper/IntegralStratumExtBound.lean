/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.IntegralStratumHomFormula
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
import Sheaf.Paper.IntegralConstructibleReductionLimit
import Sheaf.Paper.IntegralStratumReductionExtBound
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Uniform vanishing of integral constructible Ext

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
sk-lem-int-ext-bound.md and sk-lem-int-ext.proof.md
(blueprint: det-lem-int-ext-bound).

Both clauses concern the ordinary unbounded derived category over the completed integral
coefficient sheaf. The stratum sheaf may have torsion. The cohomological dimensions use
the recorded classical, locally ell-power torsion convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem hom_shift_product_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (r : ℤ) (h : ∀ n, Subsingleton (Q ⟶ (K n) ⟦r⟧))
    (f : Q ⟶ (∏ᶜ K) ⟦r⟧) : f = 0 := by
  apply (isLimitOfPreserves (shiftFunctor (DerivedCategory C) r)
    (productIsProduct K)).hom_ext
  intro n
  exact (h n.as).elim _ _

/-- Vanishing in two adjacent degrees propagates from the levels to their Roos limit.
Source: the final paragraph of Integral targets, the derived-limit one-degree loss
(blueprint: det-uniform-constructible-ext-integral). -/
private theorem hom_roos_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q N : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (pN : N ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ N⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle step N pN δ) (q : ℤ)
    (hprev : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q - 1⟧))
    (hnext : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q⟧)) :
    Subsingleton (Q ⟶ N⟦q⟧) := by
  let T := CategoryTheory.Pretriangulated.Triangle.mk pN (towerTransitionEndomorphism step) δ
  have hT' : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles
      (C := DerivedCategory C) := hT
  let U := (shiftFunctor (CategoryTheory.Pretriangulated.Triangle (DerivedCategory C))
    (q - 1)).obj T
  have hU : U ∈ CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    CategoryTheory.Pretriangulated.Triangle.shift_distinguished T hT' (q - 1)
  let e := (shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app N
  have hz (f : Q ⟶ N⟦q⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁ U hU
      (f ≫ e.hom) (by
        apply (cancel_mono
          ((shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app (∏ᶜ K)).inv).1
        rw [zero_comp]
        exact hom_shift_product_zero Q K q hnext _)
    have hg0 : g = 0 := hom_shift_product_zero Q K (q - 1) hprev g
    apply (cancel_mono e.hom).1
    simpa only [hg0, zero_comp] using hg
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩


private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · change (CondensedRing.upperStar Λ (𝟙 X)).obj M ≅
      ((upperStarFromPoint X).mapMod Λ).obj HasZeroObject.zero.choose
    exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

private lemma constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := hA
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hS a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact hs X e hM
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private lemma constantModelConstructible_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constantModelConstructible_of_iso Λ X
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply constantModelConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn


private def UniformHomBound {C : Type*} [Category C] [HasShift C ℤ]
    (P : C → Prop) (A : C) : Prop :=
  ∃ d : ℕ, ∀ N, P N → ∀ r : ℤ, (d : ℤ) < r → Subsingleton (A ⟶ N⟦r⟧)

private theorem uniformHomBound_iso
    {C : Type*} [Category C] [HasShift C ℤ] (P : C → Prop)
    {A B : C} (e : A ≅ B) (h : UniformHomBound P A) : UniformHomBound P B := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun N hN r hr ↦ ⟨fun f g ↦ ?_⟩⟩
  apply (cancel_epi e.hom).1
  exact (hd N hN r hr).elim _ _

private theorem uniformHomBound_zero
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroMorphisms C]
    (P : C → Prop) {A : C} (h : IsZero A) : UniformHomBound P A := by
  exact ⟨0, fun _ _ _ _ ↦ ⟨fun f g ↦ h.eq_of_src f g⟩⟩

private theorem uniformHomBound_extension
    {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : C → Prop) (T : Pretriangulated.Triangle C)
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : UniformHomBound P T.obj₁) (h₃ : UniformHomBound P T.obj₃) :
    UniformHomBound P T.obj₂ := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₃, hd₃⟩ := h₃
  refine ⟨max d₁ d₃, fun N hN r hr ↦ ?_⟩
  have h₁ := hd₁ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_left d₁ d₃) hr)
  have h₃ := hd₃ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_right d₁ d₃) hr)
  have hz (f : T.obj₂ ⟶ N⟦r⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁.elim _ _)
    rw [hg, h₃.elim g 0, comp_zero]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

private theorem uniformHomBound_filtration
    {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : C → Prop) (m : ℕ) (F : Fin (m + 1) → C)
    (T : Fin m → Pretriangulated.Triangle C) (hzero : IsZero (F 0))
    (hsteps : ∀ a, T a ∈ Pretriangulated.distinguishedTriangles ∧
      (T a).obj₁ = F a.castSucc ∧ (T a).obj₂ = F a.succ ∧
      UniformHomBound P (T a).obj₃) : UniformHomBound P (F (Fin.last m)) := by
  have hF (a : Fin (m + 1)) : UniformHomBound P (F a) := by
    induction a using Fin.induction with
    | zero => exact uniformHomBound_zero P hzero
    | succ a ih =>
      obtain ⟨hT, h₁, h₂, h₃⟩ := hsteps a
      rw [← h₁] at ih
      rw [← h₂]
      exact uniformHomBound_extension P (T a) hT ih h₃
  exact hF _

/-- Ext from a stratum extension vanishes above `cd_ell(j) + cd_ell(S) + 3`;
every integral constructible sheaf has a nonnegative bound uniform in the target sheaf.
The natural number `d` names the finite displayed cohomological-dimension bound, while
Ext degrees are arbitrary integers. The qcqs instances only supply the domains of the
recorded dimensions: every locally closed subscheme and complementary open of the
Noetherian finite-type X has these properties.

Source: blueprint main-20261015, sk-lem-int-ext-bound and its twelve-step DAG proof;
Stacks Project, Tags 099M, 08JJ and 08TB (blueprint: det-lem-int-ext-bound).

Proof:
1. The algebraically closed base has ell-cohomological dimension zero by
sk-lem-base-field-cd. Finite-type finiteness in sk-def-cd gives finite nonnegative
c = cd_ell(j) and s = cd_ell(S). Write B_T = O_{E,T} and A_{n,T} = (O_E/pi^n)_T.
2. For constructible N, sk-lem-int-integral-heart puts N[0] in Dbc. By
sk-lem-integral-models, N is derived complete. Its canonical derived reductions N_n
are bounded constructible by det-prop-integral-criterion-reductions and classical by
sk-thm-pe-constructible-comparison. The quotient maps define the tower, with
N isomorphic to its derived inverse limit.
3. The length-one free quotient resolution from lem-weil-pbc-standard-quotients-perfect
and lem-weil-pbc-completed-constant-sheaf-reduction represents N_n by
[N --pi^n--> N] in degrees [-1,0]. Its cohomology is killed by pi^n and a power of ell.
4. Use the derived dual D = RHom(L,B_S), including when L has torsion.
sk-lem-int-integral-heart gives dualizability and Tor amplitude [0,1]. Evaluation and
coevaluation identify RHom(L,M) with D tensor M by their triangle identities and
def-sfb-derived-tensor-hom-adjunction-modules. The support adjunction of
sk-lem-formal-closed-support and the exact open adjunction of
sk-def-sfb-module-lower-shriek, derived using lem-pc-derived-adjoint-functors and
lem-weil-pbc-exact-functor-derived-functor, give
Ext^r(a_!L,K) = H^r RΓ(S,D tensor u^* RΓ_Z K) by lem-pur-rhom-global-sections.
5. D_n = D tensor A_n has Tor amplitude [0,1] by tensor associativity. Locally resolve
the finite O_E-module modeling L by two finite free modules: O_E is a DVR by
lem-weil-l-adic-extension-integers-dvr and the kernel is free by
lem-sc-dvr-saturation-line-smith-normal-form. Flatness of the completed coefficient
sheaf preserves that resolution. Dualize it and reduce its constant matrices modulo
pi^n. This proves bounded constructibility and classicality of D_n, using
sk-def-sfb-constructible and sk-thm-pe-constructible-comparison. The coefficient tensor
comparison is lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
6. For the open complement, lem-weil-pbc-ring-sheaf-change-adjunction identifies
restriction of scalars of Rj_{A,*} with Rj_{B,*} of restriction of scalars, including
units. Its coefficient squares commute by sk-prop-sfb-cartesian-coefficients and
naturality of pullback of O_E -> O_E/pi^n. Inverse images also commute with restriction.
7. By sk-def-cd, det-pbc-conventions-module-cohomology and
sk-thm-pe-direct-image-comparison, Rj_{A,*} has upper bound c on classical torsion
sheaves. The lower bound zero is lem-weil-pbc-derived-functor-negative-vanishing,
using lem-weil-pbc-ring-sheaves-grothendieck. Triangulatedness is
lem-pc-right-derived-functor-triangulated. Thus lem-pur-bounded-heart-amplitude sends
j^*N_n in [-1,0] to [-1,c]. The same comparison proves classicality.
8. The support fibre of N_n -> Rj_*j^*N_n lies in [-1,c+1] by
lem-sf-derived-homology-long-exact. Exact inverse images, using
sk-prop-sfb-cartesian-coefficients and lem-weil-pbc-exact-functor-complex-cohomology,
give M_n = u^* RΓ_Z N_n in that interval. Direct-image comparison identifies its
fibre with the pullback of the etale fibre, so M_n is classical.
9. Put T_n = D_n tensor_{A_n} M_n = D tensor_{B_S} M_n. Filter M_n by its finitely
many shifted cohomology sheaves using lem-weil-pbc-truncation-triangle. Tor amplitude
[0,1], exact tensor and lem-sf-derived-homology-long-exact place T_n in [-1,c+2].
Exactness follows by tensoring K-flat cones as in lem-weil-pbc-site-derived-tensor-descent.
The classical equivalence det-pe-classical-derived-equivalence, its unit from
sk-prop-sf-comparison, Tor reflection det-pe-finite-tor-comparison-noetherian and the
ringed tensor pullback comparison make this a bounded classical A_n-complex.
10. Apply derived sections to that finite cohomology filtration. The definition of s,
sk-prop-sf-comparison, det-pbc-conventions-module-cohomology and triangulatedness of
derived sections give upper bound c+s+2. The scalar-extension/restriction adjunction
lem-weil-derived-scalar-extension-restriction-adjunction and
lem-pur-rhom-global-sections identify integral and finite-coefficient sections here.
Step 4 gives Hom(a_!L,N_n[r]) = 0 for r > c+s+2, uniformly in n and N.
11. det-pe-products-derived and def-weil-derived-limit give the Roos triangle
N -> P -> P -> N[1], with P the product of the N_n. Hom into each shifted P is the
product of the Hom groups into the shifted N_n. For r > c+s+3 both Hom(a_!L,P[r-1])
and Hom(a_!L,P[r]) vanish. Exactness from lem-weil-pbc-hom-into-triangle-exact then
annihilates Hom(a_!L,N[r]). No immersion inverse image is commuted with this limit.
12. Clause (1) of det-lem-int-ext-formula filters a constructible sheaf C by finitely
many degree-zero stratum extensions. Take d_C to be the maximum of their bounds,
or zero for the empty filtration. At each triangle, the outside terms of the
contravariant Hom exact sequence lem-weil-pbc-hom-out-of-triangle-exact vanish.
Induction gives the required bound simultaneously for all constructible N. -/
theorem integral_stratum_ext_bound
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    (∀ (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range j = (Set.range i)ᶜ →
      ∀ L : pulledBackModuleObjects (integralCoefficientRing l E) S,
        IsConstantModelConstructible (integralCoefficientRing l E) S L →
        HasFiniteConstantLocalModel (integralCoefficientRing l E) S L →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j +
            cohomologicalDimension l (Fact.out : l.Prime) S + 3 ∧
          ∀ N : pulledBackModuleObjects (integralCoefficientRing l E) X,
            IsConstantModelConstructible (integralCoefficientRing l E) X N →
            ∀ r : ℤ, (d : ℤ) < r →
              Subsingleton (((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar (integralCoefficientRing l E) i).obj
                  ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟶
                ((DerivedCategory.singleFunctor _ 0).obj N) ⟦r⟧)) ∧
    (∀ C : pulledBackModuleObjects (integralCoefficientRing l E) X,
      IsConstantModelConstructible (integralCoefficientRing l E) X C →
      ∃ d : ℕ, ∀ N : pulledBackModuleObjects (integralCoefficientRing l E) X,
        IsConstantModelConstructible (integralCoefficientRing l E) X N →
        ∀ r : ℤ, (d : ℤ) < r →
          Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C) ⟶
            ((DerivedCategory.singleFunctor _ 0).obj N) ⟦r⟧)) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hbase : cohomologicalDimension l (Fact.out : l.Prime) (Spec (.of D.k)) < ⊤ := by
    rw [(cohomologicalDimension_baseField l Fact.out D.k).1 inferInstance]
    exact WithTop.coe_lt_top 0
  have hstratum : ∀ (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range j = (Set.range i)ᶜ →
      ∀ L : pulledBackModuleObjects (integralCoefficientRing l E) S,
        IsConstantModelConstructible (integralCoefficientRing l E) S L →
        HasFiniteConstantLocalModel (integralCoefficientRing l E) S L →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j +
            cohomologicalDimension l (Fact.out : l.Prime) S + 3 ∧
          ∀ N : pulledBackModuleObjects (integralCoefficientRing l E) X,
            IsConstantModelConstructible (integralCoefficientRing l E) X N →
            ∀ r : ℤ, (d : ℤ) < r →
              Subsingleton (((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar (integralCoefficientRing l E) i).obj
                  ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟶
                ((DerivedCategory.singleFunctor _ 0).obj N) ⟦r⟧) := by
    intro S Z V v i j _ _ _ _ _ _ hij L hL hmodel
    let : Z.Over (Spec (.of D.k)) := ⟨i ≫ (X ↘ Spec (.of D.k))⟩
    let : S.Over (Spec (.of D.k)) := ⟨v ≫ (Z ↘ Spec (.of D.k))⟩
    let : V.Over (Spec (.of D.k)) := ⟨j ≫ (X ↘ Spec (.of D.k))⟩
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace V :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace S :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact v := inferInstance
    have : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType (i ≫ (X ↘ Spec (.of D.k))))
    have : QuasiCompact (Z ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact (i ≫ (X ↘ Spec (.of D.k))))
    have : LocallyOfFiniteType (S ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType (v ≫ (Z ↘ Spec (.of D.k))))
    have : QuasiCompact (S ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact (v ≫ (Z ↘ Spec (.of D.k))))
    have : LocallyOfFiniteType (V ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType (j ≫ (X ↘ Spec (.of D.k))))
    have : QuasiCompact (V ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact (j ≫ (X ↘ Spec (.of D.k))))
    have : j.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
      (ne_of_lt (relativeCohomologicalDimension_lt_top_of_finiteType l Fact.out hbase j))
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
      (ne_of_lt (cohomologicalDimension_lt_top_of_finiteType l Fact.out hbase (X := S)))
    refine ⟨c + s + 3, ?_, ?_⟩
    · rw [← hc, ← hs]
      norm_cast
    · intro N hN r hr
      obtain ⟨hp, step, p, δ, hT⟩ :=
        integral_constructible_reduction_limit D l _hl E X N hN
      let := hp
      apply hom_roos_zero _ _ (fun n : ℕ ↦
        (integralReductionFunctor l E X (n + 1)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)) step p δ hT r
      · intro n
        apply integral_stratum_reduction_ext_bound D l _hl E X S Z V v i j hij L
          hL hmodel c s hc hs N hN n (r - 1)
        exact_mod_cast (by omega : (c : ℤ) + s + 2 < r - 1)
      · intro n
        apply integral_stratum_reduction_ext_bound D l _hl E X S Z V v i j hij L
          hL hmodel c s hc hs N hN n r
        exact_mod_cast (by omega : (c : ℤ) + s + 2 < r)
  refine ⟨hstratum, ?_⟩
  intro C hC
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have hc : Fintype.card D.k₀ = D.q := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  have : Fact (ringChar D.k).Prime := ⟨hchar ▸ D.prime⟩
  have : Fact (ringChar D.k ≠ l) := ⟨by rw [hchar]; exact _hl.symm⟩
  obtain ⟨R, m, F, T, hzero, ⟨e⟩, hsteps⟩ :=
    integral_stratum_filtration l E D.k X ((DerivedCategory.singleFunctor _ 0).obj C)
      (constantModelConstructible_single (integralCoefficientRing l E) X C hC)
  let P : integralDerived l E X → Prop := fun K ↦
    ∃ N, IsConstantModelConstructible (integralCoefficientRing l E) X N ∧
      K = (DerivedCategory.singleFunctor _ 0).obj N
  have hlast : UniformHomBound P (F (Fin.last m)) := by
    apply uniformHomBound_filtration P m F T hzero
    intro a
    obtain ⟨hT, h₁, h₂, b, Z, v, i, hv, hi, hvi, L, n, hL, hmodel, hn, ⟨ep⟩⟩ := hsteps a
    have := hv
    have := hi
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace (R.domain b) :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨d, _, hd⟩ := hstratum (R.domain b) Z U.toScheme v i U.ι
      (by exact U.range_ι) L hL hmodel
    have hn0 : n = 0 := hn ⟨inferInstance, inferInstance⟩
    subst n
    let ep' := ep ≪≫ (shiftFunctorZero (integralDerived l E X) ℤ).app _
    refine ⟨hT, h₁, h₂, uniformHomBound_iso P ep'.symm ?_⟩
    refine ⟨d, ?_⟩
    rintro K ⟨N, hN, rfl⟩ r hr
    exact hd N hN r hr
  obtain ⟨d, hd⟩ := uniformHomBound_iso P e hlast
  exact ⟨d, fun N hN r hr ↦ hd _ ⟨N, hN, rfl⟩ r hr⟩

end AlgebraicGeometry.ProEtale.CondensedRing
