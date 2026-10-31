/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.AdicUnliftedPerfectCharts
import WeilConjectures.AlgebraicGeometry.ConstantPerfectDvrTorsionCalculation

/-! # Torsion normal form and its consecutive-quotient obstruction

Source: the DVR elementary-divisor calculation in steps 3--5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def pullbackScalarIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let R' := (adicTowerInverseImage g).obj R
  let S' := (adicTowerInverseImage g).obj S
  let φ' := (adicTowerInverseImage g).map φ
  let adjR := (proEtaleRingDerivedOperations_adjunction g R R' (Iso.refl _)).some
  let adjS := (proEtaleRingDerivedOperations_adjunction g S S' (Iso.refl _)).some
  let δ := proEtaleRingRestrictionDerivedDirectImage g R S R' S' φ φ'
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ((pbcDerivedScalarAdjunction φ).comp adjS).leftAdjointUniq
    ((adjR.comp (pbcDerivedScalarAdjunction φ')).ofNatIsoRight δ.symm)

private def pullbackHomologyIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {K L : DerivedCategory (pbcModules X R)}
    (e : (adicTowerPullback g R).obj K ≅ (adicTowerPullback g R).obj L) (q : ℤ) :
    (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)).obj
        ((DerivedCategory.homologyFunctor _ q).obj L) := by
  let F := proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)
  exact (F.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso q).app L).symm

private def pullbackTorIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : PbcCompletedDerived X d}
    (e : (adicTowerPullback g (pbcAdicCompletion X d)).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion X d)).obj L) (q : ℤ) (n : ℕ) :
    let tor (M : PbcCompletedDerived X d) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction X d (n + 1)).obj M))))
    let R := (pbcAdicRings X d).obj (op n)
    let F := proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)
    (pbcRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
        (F.obj (tor K)) ≅
      (pbcRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
        (F.obj (tor L)) := by
  let R := (pbcAdicRings X d).obj (op (n + 1))
  let F := proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)
  let red := pbcCompletedReduction X d (n + 1)
  let c := pullbackScalarIso g (pbcAdicProjection X d (n + 1))
  let er : (adicTowerPullback g R).obj (red.obj K) ≅
      (adicTowerPullback g R).obj (red.obj L) :=
    c.app K ≪≫ (pbcDerivedExtend
      ((adicTowerInverseImage g).map (pbcAdicProjection X d (n + 1)))).mapIso e ≪≫
        (c.app L).symm
  let HK := (DerivedCategory.homologyFunctor _ q).obj (red.obj K)
  let HL := (DerivedCategory.homologyFunctor _ q).obj (red.obj L)
  let eh : F.obj HK ≅ F.obj HL := pullbackHomologyIso g R er q
  let es : (adicTowerPullback g R).obj ((DerivedCategory.singleFunctor _ 0).obj HK) ≅
      (adicTowerPullback g R).obj ((DerivedCategory.singleFunctor _ 0).obj HL) :=
    (F.mapDerivedCategorySingleFunctor 0).app HK ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eh ≪≫
        ((F.mapDerivedCategorySingleFunctor 0).app HL).symm
  let φ := pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)
  let c' := pullbackScalarIso g φ
  let et := c'.app ((DerivedCategory.singleFunctor _ 0).obj HK) ≪≫
    (pbcDerivedExtend ((adicTowerInverseImage g).map φ)).mapIso es ≪≫
      (c'.app ((DerivedCategory.singleFunctor _ 0).obj HL)).symm
  exact (pbcRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).mapIso
    (pullbackHomologyIso g _ et (-1))

/-- On a finite stratum cover, each cohomology sheaf splits as a finite free sheaf
and a nilpotent-uniformizer torsion sheaf. The cokernel of the uniformizer on that
torsion sheaf is a quotient of a consecutive-quotient Tor sheaf. This is a normal-form
statement for arbitrary bounded constructible complete complexes; no Tor vanishing
or flatness of their cohomology is assumed.

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8; Stacks Tag 0ASV;
the explicit alternating quotient resolution in step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`.
(blueprint: lem-weil-pbc-adic-cohomology-torsion-normal-form).

Proof: choose a finite stratification and pro-etale perfect models. Use the actual
valuation ring, without changing to its universe lift; coefficient-ring isomorphisms
transport the usual integral characterization. A finite projective module over this
DVR is finite free. Starting at the highest degree, Smith normal form splits the
bounded free complex into one-term free summands and two-term complexes with
nonzero differential a power of the uniformizer. Incoming differentials land in
the complementary kernel, so this construction proceeds downward. Contractible
unit-differential summands contribute nothing. In degree q, complete the free
summands to F and the cokernels of the positive-power summands to N. Constant
realization is exact on these finite modules and commutes with finite reductions,
so this gives the stated cohomology isomorphism. Multiplication by the uniformizer
on N is nilpotent, with exponent at most the largest elementary divisor.
Choose n at least that exponent. The reduction of every degree-q torsion block
contains its original cokernel as a direct summand of H^q(K_(n+1)). The alternating
free resolution for the map from quotient n+1 to quotient n has differentials
uniformizer^(n+1) and uniformizer (the indexing convention uses quotient n equal
to A/(uniformizer^(n+1))). Tensoring a torsion block makes the first differential
zero and gives Tor_1 = N/uniformizer N. Projection onto these summands is the
required epimorphism, after restriction of its quotient coefficients. Exact
inverse image commutes with cohomology and derived quotient extension, so its
source is the pullback of the displayed ambient Tor sheaf. Empty charts and the
absence of torsion are covered by N = 0 and the epimorphism to zero. -/
theorem pbc_adic_cohomology_torsion_normal_form
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) (q : ℤ) :
    let d := pbcPadicCoefficientDatum l E
    let B := pbcAdicCompletion T d
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K.obj))))
    ∃ (S : Stratification T)
      (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a)),
      ∀ (a : Fin S.n) (j : (V a).I₀),
        let g := (V a).f j ≫ S.immersion a
        let B' := (adicTowerInverseImage g).obj B
        let P := proEtaleRingModulePullback g B B' (Iso.refl _)
        ∃ (r : ℕ) (F N : pbcModules ((V a).X j) B'),
          (∀ U : ((V a).X j).ProEtᵒᵖ,
            Nonempty (Module.Basis (Fin r) (B'.obj.obj U) (F.val.obj U))) ∧
          Nonempty (P.obj ((DerivedCategory.homologyFunctor _ q).obj K.obj) ≅ F ⊞ N) ∧
          ∃ f : End N, IsNilpotent f ∧ ∃ n : ℕ,
            ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
                (pbcAdicProjection T d n))).obj
              ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
                ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
                (Iso.refl _)).obj (tor n)) ⟶ cokernel f,
              Epi t := by
  obtain ⟨S, V, hV⟩ := pbc_adic_unlifted_perfect_charts T hdim l E hl K
  refine ⟨S, V, fun a j ↦ ?_⟩
  obtain ⟨C, hC, ⟨eC⟩⟩ := hV a j
  let g := (V a).f j ≫ S.immersion a
  obtain ⟨r, F, N, hF, ⟨eH⟩, f, hf, n, t, ht⟩ :=
    pbc_constant_perfect_dvr_torsion_calculation T ((V a).X j) g l E C hC q
  refine ⟨r, F, N, hF, ⟨pullbackHomologyIso g _ eC q ≪≫ eH⟩, f, hf, n,
    (pullbackTorIso g (pbcPadicCoefficientDatum l E) eC q n).hom ≫ t, ?_⟩
  have : Epi t := ht
  infer_instance

end AlgebraicGeometry.Scheme
