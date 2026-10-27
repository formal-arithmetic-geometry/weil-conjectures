/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module
import Sheaf.CategoryTheory.ExactDegreeZero
import Mathlib.AlgebraicGeometry.Noetherian

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.VectorTraceScalarDescent
import Sheaf.Paper.VectorPurityScalarSingle
import all Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.Paper.ExceptionalCoefficientUnitCoherence

/-!
# Scalar compatibility of the normalized projective-line counit

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, retained Step 7
(blueprint: lem-sp-p1-counit-scalar).

The balanced root comparison is expressed by the existing generator-normalized
`CoefficientLineComparison` with the same annihilator on both sides. Its derived map
is constrained to the scalar counit followed by the ordinary balanced sheaf map.
The displayed composite uses the published tensorator, inverse-image comparison and
shift comparison. The adjunctions are the actual normalized projective-line data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async true


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
set_option maxRecDepth 1024


universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

section Helpers

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option backward.defeqAttrib.useBackward true

private theorem cachedModSheafify (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedModSheafify



-- Keep the chosen adjoints opaque while elaborating the canonical diagrams.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  ModuleCat.extendScalars
  projectiveLineTraceDatum projectiveLineTraceTransport
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap
  WeilConjectures.PurityFiniteSetting.purityScalarUnitMap
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.unitIso
  singleFunctorObjUnitIso derivedTensorRightUnitor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.DerivedCategory.singleFunctors

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transpose_of_counit_square
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y Z : D} (β : Y ⟶ F.obj X) [IsIso β]
    (a : X ⟶ G.obj Z) (ε : Y ⟶ Z)
    (h : β ≫ F.map a ≫ adj.counit.app Z = ε) :
    a = adj.homEquiv _ _ (inv β ≫ ε) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change F.map a ≫ adj.counit.app Z = inv β ≫ ε
  rw [← h, IsIso.inv_hom_id_assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_trace_counit_square
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶
      (T.prod T) ⋙ Functor.uncurry.obj TB)
    (K H I : C) (H' I' : D) (E : C) (E' : D)
    (π : (TA.obj K).obj H ⟶ E) [Epi (T.map π)]
    (π' : (TB.obj (T.obj K)).obj H' ⟶ E')
    (c : T.obj E ⟶ E') (ε : E ⟶ K) (ε' : E' ⟶ T.obj K)
    (t : H ⟶ I) (t' : H' ⟶ I') (b : T.obj H ⟶ H') (e : T.obj I ⟶ I')
    (ρ : (TA.obj K).obj I ⟶ K)
    (ρ' : (TB.obj (T.obj K)).obj I' ⟶ T.obj K)
    (hπ : T.map π ≫ c = m.app (K, H) ≫ (TB.obj (T.obj K)).map b ≫ π')
    (hε : π ≫ ε = (TA.obj K).map t ≫ ρ)
    (hε' : π' ≫ ε' = (TB.obj (T.obj K)).map t' ≫ ρ')
    (ht : b ≫ t' = T.map t ≫ e)
    (hρ : m.app (K, I) ≫ (TB.obj (T.obj K)).map e ≫ ρ' = T.map ρ) :
    c ≫ ε' = T.map ε := by
  apply (cancel_epi (T.map π)).1
  rw [← Category.assoc, hπ]
  simp only [Category.assoc]
  rw [hε', ← Functor.map_comp_assoc, ht, Functor.map_comp, Category.assoc]
  have hn := m.naturality (show (K, H) ⟶ (K, I) from (𝟙 K, t))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hn
  rw [← reassoc_of% hn, hρ, ← T.map_comp, ← hε, T.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coefficient_line_sheaf_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤)))
    (e : FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T)
    (c : (ProEtale.etaleSheafExtendScalars φ T).obj
        (Scheme.finiteEtaleTateLine T N A hA) ≅ Scheme.finiteEtaleTateLine T N B hB)
    (hc : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ c.hom).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z) :
    e.sheafIso.hom = c.hom := by
  have hroot : e.roots = 𝟙 _ := by
    apply (cancel_mono (kernel.ι (N • 𝟙 T.gmSheaf))).1
    exact e.roots_power.trans (by
      rw [Nat.div_self hN, one_smul]
      exact (Category.id_comp _).symm)
  apply ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).injective
  apply (Scheme.lineHomEquiv T N A hA _).injective
  ext W z
  simp only [Scheme.lineHomEquiv_generator]
  rw [e.generators, hc, hroot]
  rfl


open WeilConjectures.PurityFiniteSetting MonoidalCategory in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparison_balancing_sheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (e : FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T) :
    e.sheafIso.hom = (VectorTraceScalar.balancing φ N hN hA hB T hT 1).hom := by
  have hstalk (x : T) : IsUnit (N : T.presheaf.stalk x) := by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom
  have norm := finite_tate_scalar_source_normalization φ N hN hA hB T hstalk
  have hb := (Classical.choose_spec norm.2.exists).1.1 1
  have hc : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
        (VectorTraceScalar.balancing φ N hN hA hB T hT 1).hom).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
    intro W a z
    have hg := hb W a 1 (fun _ ↦ z)
    simp only [one_smul, mul_one,
      Scheme.finiteTateEtalePowerGenerator] at hg
    rw [Adjunction.homEquiv_unit]
    unfold VectorTraceScalar.balancing
    exact hg
  exact coefficient_line_sheaf_eq φ N hN hA hB T hT e
    (VectorTraceScalar.balancing φ N hN hA hB T hT 1) hc


attribute [local irreducible] derivedTensorSingleUnitIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transported_right_unit
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶ T.prod T ⋙ Functor.uncurry.obj TB)
    (K I U : C) (I' U' : D) (e : I ≅ U) (f : I' ≅ U') (mu : T.obj U ⟶ U')
    (ρ : (TA.obj K).obj U ⟶ K) (ρ' : (TB.obj (T.obj K)).obj U' ⟶ T.obj K)
    (hu : m.app (K, U) ≫ (TB.obj (T.obj K)).map mu ≫ ρ' = T.map ρ) :
    m.app (K, I) ≫ (TB.obj (T.obj K)).map (T.map e.hom ≫ mu ≫ f.inv) ≫
      ((TB.obj (T.obj K)).map f.hom ≫ ρ') =
    T.map ((TA.obj K).map e.hom ≫ ρ) := by
  have hn := m.naturality (show (K, I) ⟶ (K, U) from (𝟙 K, e.hom))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ f.inv f.hom, f.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% hn, hu, ← T.map_comp]

private theorem transported_right_unit_named
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶ T.prod T ⋙ Functor.uncurry.obj TB)
    (K I U : C) (I' U' : D) (e : I ≅ U) (f : I' ≅ U') (mu : T.obj U ⟶ U')
    (ρ : (TA.obj K).obj U ⟶ K) (ρ' : (TB.obj (T.obj K)).obj U' ⟶ T.obj K)
    (v : T.obj I ⟶ I') (r : (TA.obj K).obj I ⟶ K)
    (r' : (TB.obj (T.obj K)).obj I' ⟶ T.obj K)
    (hv : v = T.map e.hom ≫ mu ≫ f.inv)
    (hr : r = (TA.obj K).map e.hom ≫ ρ)
    (hr' : r' = (TB.obj (T.obj K)).map f.hom ≫ ρ')
    (hu : m.app (K, U) ≫ (TB.obj (T.obj K)).map mu ≫ ρ' = T.map ρ) :
    m.app (K, I) ≫ (TB.obj (T.obj K)).map v ≫ r' = T.map r := by
  rw [hv, hr, hr']
  exact transported_right_unit T TA TB m K I U I' U' e f mu ρ ρ' hu

end Helpers

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

set_option synthInstance.maxSize 4096

/-- The actual normalized projective-line counit commutes with arbitrary finite
coefficient extension, and the canonical right comparison is the transpose of the
inverse proper coefficient map. Source: main-20261015 blueprint, Charts paragraph
of sk-lem-sp-reduction-exceptional.proof.md, retained Step 7
(blueprint: lem-sp-p1-counit-scalar).

Proof: (1) Put L_R=R_P(1)[2] and H_R=Rq_*L_R. The normalized adjunction of
lem-asd-ordinary-finite-p1-adjunction expresses its actual counit as inverse ordered
projection, tensor with the normalized trace t_R, then the right unitor. The twist
is flat of rank one by lem-asd-finite-etale-twist-line, so derived coefficient change
is ordinary balancing on this factor, and its exact derived functor commutes with shift.
(2) The geometric adjunctions q_A^* ⊣ Rq_{*,A} and q_B^* ⊣ Rq_{*,B} give beta as the
mate of scalarPullbackIso, exactly the specified proper coefficient map of
lem-sp-et-proet-coefficient-compatibility. The monoidal composition comparisons of
lem-sfb-ringed-derived-monoidal-comparisons identify the composite pullbacks and
respect tensor, units and symmetry, without flatness of the coefficient map.
(3) Apply lem-sp-categorical-projection-mate-square to these geometric adjunctions.
Conjugate its ordered projection by the two symmetries, as in
lem-amb-proper-coproducts-projection, and follow by the balanced twist comparison.
This gives F_B(a_K) beta(G_A K) T_S(pi_A)=pi_B(1 tensor b)m, where
b=F_B(lambda) beta(L_A) and m is the scalar tensorator.
(4) The specified two-summand splitting of lem-sp-p1-splitting-scalar gives
t_B b=e_unit T_S(t_A), with the same Kummer-normalized trace and balanced lambda.
(5) Cancel the projection isomorphisms supplied by
lem-amb-proper-coproducts-projection. Substitute the actual counit formulas, then
use tensorator naturality at (1_K,t_A) and its right-unit equation. The result is
beta(G_A K) F_B(a_K) epsilon_B=T_S(epsilon_A), the first displayed equation.
(6) S is Noetherian because it is finite type over a field. By
lem-sp-finite-coefficient-input-models, K has a bounded flat constructible model and
its coefficient extension remains in Dctf. Exact inverse image preserves this model's
bounds and flat terms. Pull back a constructible stratification: base-changed locally
closed strata are constructible by lem-pur-scheme-constructible-preimage, and the
trivializing etale covers pull back. Tensor with the locally rank-one twist and shift;
this gives a bounded flat constructible model of G_A K. Its finite degree interval
bounds Tor against every degree-zero module. Thus beta is invertible there by
lem-sp-et-proet-coefficient-compatibility. Precompose the first equation with its
inverse. The exceptional B-adjunction Hom bijection identifies a_K with the unique
transpose of beta(G_A K) inverse followed by T_S(epsilon_A), equivalently the mate
of beta inverse on the finite-Tor subcategories. N=ell^n is invertible on S because
ell differs from the positive characteristic; the same-annihilator root comparison
exists by ordinary balancing and flatness of the Tate line. Its generators and scalar
counit normalization fix the isomorphism used in both displayed clauses. -/
theorem p1_counit_scalar
    (ell p n : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    ∃ hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)),
    ∃ e : FiniteSmoothPurity.CoefficientLineComparison φ (ell ^ n) (ell ^ n) hA hB
        (ProjectiveLine S),
    ∀ (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
      (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
      (dA : OrdinaryFiniteP1Datum A (ell ^ n) hA tA S hS)
      (dB : OrdinaryFiniteP1Datum B (ell ^ n) hB tB S hS)
      (K : DerivedCategoryModule A S)
      (_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K),
      ((scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteP1Right A (ell ^ n) hA S).obj K) ≫
        (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          ((ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).app
              ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
                (ordinaryFiniteLine A (ell ^ n) hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
            (Functor.uncurry.obj (ordinaryFiniteTensor B (ProjectiveLine S))).mapIso
              (Iso.prod ((scalarPullbackIso φ (ProjectiveLine S ↘ S)).app K).symm
                ((FiniteSmoothPurity.scalarShiftIso φ (ProjectiveLine S) (2 : ℤ)).app _ ≪≫
                  (shiftFunctor _ (2 : ℤ)).mapIso e.derivedIso))).hom ≫
        dB.adjunction.counit.app ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map (dA.adjunction.counit.app K)) ∧
      ∃ hβ : IsIso ((scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteP1Right A (ell ^ n) hA S).obj K)),
        ((ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).app
              ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
                (ordinaryFiniteLine A (ell ^ n) hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
            (Functor.uncurry.obj (ordinaryFiniteTensor B (ProjectiveLine S))).mapIso
              (Iso.prod ((scalarPullbackIso φ (ProjectiveLine S ↘ S)).app K).symm
                ((FiniteSmoothPurity.scalarShiftIso φ (ProjectiveLine S) (2 : ℤ)).app _ ≪≫
                  (shiftFunctor _ (2 : ℤ)).mapIso e.derivedIso))).hom =
          dB.adjunction.homEquiv _ _
            (@inv _ _ _ _ ((scalarMate φ (ProjectiveLine S ↘ S)).app
                ((ordinaryFiniteP1Right A (ell ^ n) hA S).obj K)) hβ ≫
              (scalarExtension φ S).map (dA.adjunction.counit.app K)) := by
  sorry

end AlgebraicGeometry.Etale
