/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Algebra.Homology.AdicShortComplexCohomologyML
public import Sheaf.CategoryTheory.FiniteTripleMittagLeffler
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # A finite-projective algebraic model for individually constant reductions

Source: Stacks Project, Tag 09C5, the first two paragraphs of the proof.
(blueprint: lem-sfb-constant-reductions-finite-projective-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Exact constant realization of a standard algebraic derived object on a small site.
This is the existing representative construction, stated before specializing the site.
Source: Stacks Project, Tags 093J and 09C5.
(blueprint: lem-sfb-constant-reductions-finite-projective-model). -/
@[irreducible] def constantReductionsRealization {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) (R : Type w) [CommRing R]
    (E : @DerivedCategory (ModuleCat.{w} R) _ _ (HasDerivedCategory.standard _)) :
    ConstantCompletion.D (ConstantCompletion.constant T R) := by
  letI : (siteConstantModulePresheafGeneral (C := C) R).PreservesZeroMorphisms :=
    ⟨by intros; ext U x; rfl⟩
  letI : (constantModuleHomFunctor T R).PreservesZeroMorphisms := by
    unfold constantModuleHomFunctor siteConstantModuleFunctorGeneral
    infer_instance
  exact (ConstantCompletion.Q _).obj
    (((constantModuleHomFunctor T R).mapHomologicalComplex (.up ℤ)).obj
      ((@DerivedCategory.Q (ModuleCat.{w} R) _ _ (HasDerivedCategory.standard _)).objPreimage E))


section RealizationComparison

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]

private theorem realizationCoefficientIso_eq :
    realizationRingIso J R = (constantModuleHomRingIso J R).symm := by
  have hc : (Functor.compConstIso Cᵒᵖ (forget₂ CommRingCat.{w}
      RingCat.{w})).inv.app (CommRingCat.of R) = 𝟙 _ := by
    ext
    rfl
  ext U x
  simp [realizationRingIso, constantCommuteCompose, constantModuleHomRingIso, hc]
private theorem realizationFunctorComparison :
    Nonempty (constantModuleHomFunctor J R ≅ commutativeSiteConstantModuleFunctor J R) := by
  let e := constantModuleHomRingIso J R
  obtain ⟨t⟩ := commutativeSiteConstantModuleFunctor_transport J R
  rw [realizationCoefficientIso_eq J R] at t
  change commutativeSiteConstantModuleFunctor J R ⋙
    SheafOfModules.pushforward (F := 𝟭 C) e.hom ≅ siteConstantModuleFunctorGeneral J R at t
  have he : e.inv ≫ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).map e.hom = 𝟙 _ :=
    e.inv_hom_id
  let R₁ := (constantSheaf J RingCat.{w}).obj (RingCat.of R)
  let R₂ := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
    ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of R))
  let c := SheafOfModules.pushforwardComp (S := R₂) (R := R₁) (R' := R₂)
    (J := J) (K := J) (K' := J) (F := 𝟭 C) (G := 𝟭 C) e.inv e.hom
  let d := SheafOfModules.pushforwardCongr (S := R₂) (R := R₂) (J := J) (K := J) (F := 𝟭 C) he
  let k : SheafOfModules.pushforward (F := 𝟭 C) e.hom ⋙
      SheafOfModules.pushforward (F := 𝟭 C) e.inv ≅ 𝟭 _ :=
    c ≪≫ d ≪≫ SheafOfModules.pushforwardId _
  exact ⟨Functor.isoWhiskerRight t.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ k ≪≫ Functor.rightUnitor _⟩


/-- The representative construction is the existing exact derived constant functor,
up to its canonical representative and coefficient-presentation comparisons.

Source: Stacks Project, Tags 093J, 05RU and 09C5.
(blueprint: lem-sfb-constant-reductions-finite-projective-model).

Proof: identify the two ring-sheafification isomorphisms on constant sections. The
existing comparison for commutative constant module sheafification, composed with
inverse coefficient transport, identifies its functor with constantModuleHomFunctor.
Apply this isomorphism degreewise to the chosen representative, localize, and compose
with the exact-derived-functor comparison and the representative marking. -/
theorem constantReductionsRealization_iso
    (E : @DerivedCategory (ModuleCat.{w} R) _ _ (HasDerivedCategory.standard _)) :
    let := HasDerivedCategory.standard (ModuleCat.{w} R)
    let := HasDerivedCategory.standard (realizationModules J R)
    Nonempty (constantReductionsRealization J R E ≅
      (commutativeSiteDerivedConstantModuleFunctor J R).obj E) := by
  let := HasDerivedCategory.standard (ModuleCat.{w} R)
  let := HasDerivedCategory.standard (realizationModules J R)
  have : (siteConstantModulePresheafGeneral (C := C) R).PreservesZeroMorphisms :=
    ⟨by intros; ext U x; rfl⟩
  have : (constantModuleHomFunctor J R).PreservesZeroMorphisms := by
    unfold constantModuleHomFunctor siteConstantModuleFunctorGeneral
    infer_instance
  unfold constantReductionsRealization
  obtain ⟨k⟩ := realizationFunctorComparison J R
  let P := DerivedCategory.Q.objPreimage E
  exact ⟨DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex k (.up ℤ)).app P) ≪≫
    ((commutativeSiteConstantModuleFunctor J R).mapDerivedCategoryFactors.app P).symm ≪≫
    (commutativeSiteDerivedConstantModuleFunctor J R).mapIso
      (DerivedCategory.Q.objObjPreimageIso E)⟩

end RealizationComparison

/-- Cohomology of strict coefficient-sheaf towers in the standard localization.
Source: Stacks Project, Tags 05RU and 0940.
(blueprint: lem-sfb-constant-reductions-finite-projective-model). -/
@[irreducible] def constantReductionsTowerCohomology {C : Type w} [SmallCategory C]
    {T : GrothendieckTopology C} (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.TD R ⥤ (ℕᵒᵖ ⥤ ConstantCompletion.Mod R) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

/-- The nth completion evaluation has exactly the nth power of the extended ideal
as its kernel, for every n including zero.
Source: Stacks Project, Tag 09C5 and Mathlib's completion kernel calculation.
(blueprint: lem-sfb-constant-reductions-finite-projective-model).
Proof: the evaluation to A/I^n is the linear evaluation followed by the canonical
quotient equality isomorphism. Its kernel is I^n times the completion. Restriction
of scalars identifies this submodule with the extension of I^n, equal to (IB)^n. -/
theorem constantReductionsCompletionKer {A : Type w} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  ext x
  change (AdicCompletion.evalₐ I n) x = 0 ↔ _
  change (Ideal.quotientEquivAlgOfEq A (by ext; simp))
    (AdicCompletion.eval I A n x) = 0 ↔ _
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  change x ∈ (AdicCompletion.eval I A n).ker ↔ _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map, Ideal.map_pow]
  rfl

/-- The actual completion-quotient isomorphism, induced by the evaluation map.
Source: Stacks Project, Tag 09C5, first proof paragraph.
(blueprint: lem-sfb-constant-reductions-finite-projective-model). -/
def constantReductionsCompletionIso {A : Type w} [CommRing A] (I : Ideal A) (hI : I.FG) (n : ℕ) :
    AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ n ≃+*
      A ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq (AdicCompletion I A)
    (constantReductionsCompletionKer I hI n).symm).toRingEquiv.trans
      ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.surjective_evalₐ I n))

/-- The completion-quotient comparison sends each representative to its evaluation.
Source: Stacks Project, Tag 09C5.
(blueprint: lem-sfb-constant-reductions-finite-projective-model).
Proof: both quotient equivalences are induced by their displayed ring maps, so their
formulas on quotient representatives compose to the evaluation formula. -/
theorem constantReductionsCompletionIso_mk {A : Type w} [CommRing A]
    (I : Ideal A) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I A) :
    constantReductionsCompletionIso I hI n (Ideal.Quotient.mk _ x) =
      AdicCompletion.evalₐ I n x := by
  simp [constantReductionsCompletionIso]

/-- Individually constant reductions with perfect residue admit one bounded finite-projective
complex over the coefficient completion. Its quotient cohomology, realized as actual constant
module sections, compares with any finite triple of the given reduction tower.

Source: Stacks Project, Tag 09C5, first two paragraphs; Tags 09BE, 09AR and 09AW.
(blueprint: lem-sfb-constant-reductions-finite-projective-model).

Proof: if W is empty, its section modules vanish and the zero complex is a model. Otherwise,
constant realization on any nonempty pro-etale object is conservative: its exactness reduces
this to injectivity of the constant sheafification unit. For each algebraic marking E_n,
reduce to A/J and use local algebraicity of maps from a perfect constant complex to obtain
an algebraic isomorphism with the residue model on a nonempty covering member. Lift the
bounded finite-projective residue complex across the nilpotent kernel. Nilpotent Nakayama
shows its lifted projective terms are finite and vanish outside the same bounded range.
Thus each E_n is perfect. Local algebraicity now gives consecutive algebraic maps whose
derived reductions are isomorphisms, detected on a nonempty covering member. Choose one
at each level. Complete A at J: its compatible finite quotients are the original A/J^(n+1).
Perfect inverse-limit reconstruction gives a perfect complex over this completion and
compatible isomorphisms from its reductions to E_n. The universal equivalence
between small Grothendieck derived localization and the standard localization preserves
the quotient functors and transports the finite-projective representatives. Choose a
bounded finite-projective representative P. For a triple t >= m >= n, reduce a single
level-t constant marking of P
to m and n. Scalar-extension transitivity, normalized on pure tensors, identifies the two
arrows with the actual quotient transitions, including repeated indices. Exact constant
realization commutes with cohomology, so sections give the displayed bijections and both
comparison equations, for every q. No compatibility of the original markings is needed.
This statement supplies the geometric model only; it asserts no stabilization of images. -/
theorem constant_reductions_finite_projective_model
    (W : Scheme.{u}) [IsAffine W]
    (_hW : ∀ (F G : Sheaf (ProEt.topology W) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (⊤_ W.ProEt))))
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (H : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A))
    (_hcomplete : ConstantCompletion.IsComplete
      (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J 0) H)
    (_hconstant : ∀ n : ℕ, ∃ E :
        @DerivedCategory (ModuleCat.{max v (u + 1)} (A ⧸ J ^ (n + 1))) _ _
          (HasDerivedCategory.standard _),
      (n = 0 → @DerivedCategory.IsPerfectRingComplex _ _
        (HasDerivedCategory.standard _) E) ∧
      Nonempty
        ((ConstantCompletion.extend
            (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J n)).obj H ≅
          constantReductionsRealization (coefficientProEtaleModelTopology.{u, v} W)
            (A ⧸ J ^ (n + 1)) E)) :
    ∃ (P : CochainComplex (ModuleCat.{max v (u + 1)} (AdicCompletion J A)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective (AdicCompletion J A) (P.X i) ∧
        Module.Finite (AdicCompletion J A) (P.X i)) ∧
      ∀ q : ℤ, CategoryTheory.Functor.FiniteTripleRangeComparison
        ((constantReductionsTowerCohomology
            (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A) q).obj
            ((ConstantCompletion.quotientPresentation
              (coefficientProEtaleModelTopology.{u, v} W) A J false).tower.obj H) ⋙
          SheafOfModules.evaluation.{max v (u + 1)}
            (siteModuleRings
              (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A))
            (op (AsSmall.up.obj (⊤_ W.ProEt))) ⋙
          CategoryTheory.forget (ModuleCat _))
        (AdicCohomology.tower (J.map (algebraMap A (AdicCompletion J A))) (P.sc q) ⋙
          AdicCohomology.sections.{max v (u + 1)} (R := AdicCompletion J A)
            (coefficientProEtaleModelTopology.{u, v} W)
            (AsSmall.up.obj (⊤_ W.ProEt)) ⋙ CategoryTheory.forget (ModuleCat _)) := by
  sorry

end AlgebraicGeometry.Scheme
