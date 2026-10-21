/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Hom-complex composition and the normalized derived adjunction

Source: Stacks Project, sites-cohomology.tex, Tags 0A91 and 0A98, with 08J9
(blueprint: lem-sfb-ringed-hom-composition-model).

The local formula uses the actual Hom-product projections and sheafified tensor
summand generators. The derived comparison uses the fixed augmentation, not an
arbitrary isomorphism between representatives.

## Main declarations

- `ringedHomComposition_existsUnique`: unique sign-free chain composition.
- `ringedHomComposition`: the map determined by that unique characterization.
- `ringedHomRepresentativeMap`: comparison through the fixed augmentation.
- `ringedHomComposition_naturality`: outer naturality and middle dinaturality.
- `ringedHomComposition_model`: agreement with the normalized closed adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- The sign-free local homogeneous composition formula, as equality of maps on
all slices. Source: Stacks 0A91, following More on Algebra 0A8I
(blueprint: lem-sfb-ringed-hom-composition-model). -/
def RingedHomCompositionFormula
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (m : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G) :
    Prop :=
  ∀ (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b)
    (hfb : (a + q) + p = b) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) F G).X p).val.obj U)
    (g : ((homComplex (R := R) E F).X q).val.obj U),
    (coefficientHomComponent.{u, c, v} J R E G k a b hab).val.app U
        ((m.f k).val.app U
          (coefficientTensorGenerator.{u, c, v} J R
            (homComplex (R := R) F G) (homComplex (R := R) E F) p q k hpq U f g)) =
      (coefficientHomComponent.{u, c, v} J R E F q a (a + q) rfl).val.app U g ≫
        (coefficientHomComponent.{u, c, v} J R F G p (a + q) b hfb).val.app U f

/-- There is exactly one chain map with the specified homogeneous composition formula.
Source: Stacks 0A91 and More on Algebra 0A8I
(blueprint: lem-sfb-ringed-hom-composition-model).
Proof: on bidegrees (p,q), compose the a-component of g with the (a+q)-component
of f. Bilinearity and restriction compatibility descend this map through the
sheafification unit, then the tensor coproduct and Hom product universal properties
assemble its components. These same universal properties give uniqueness. Expanding
the differential gives d(fg) = (df)g + (-1)^p f(dg): the two terms containing the
middle differential cancel. Thus the graded map is a chain map. No infinite sum
of product coordinates is taken; each total-tensor section is locally a finite sum. -/
theorem ringedHomComposition_existsUnique
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃! m : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G,
      RingedHomCompositionFormula.{c, v, u} J R E F G m := by
  sorry

/-- The actual Hom-complex composition, determined uniquely by its local formula.
Source: Stacks 0A91 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomComposition
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G :=
  (ringedHomComposition_existsUnique.{c, v, u} J R E F G).exists.choose

/-- The fixed augmentation used by the recorded derived Hom construction.
Source: Stacks 079P, 0A95 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomAugmentation
    (F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    F ⟶ (coefficientHomResolution.{u, c, v} J R).obj F :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  (CochainComplex.toKInjectiveResolution.{max c v u} _).app F

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- Canonical comparison from a Hom representative to the fixed derived internal Hom.
It is an isomorphism for a K-injective target: postcompose by its fixed augmentation,
then invert the recorded localization-factorization comparison.
Source: Stacks 0A95, 0A98 (blueprint: lem-sfb-ringed-hom-composition-model). -/
def ringedHomRepresentativeMap
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map
      (((homComplexFunctor (R := R)).obj (op E)).map
        (ringedHomAugmentation.{c, v, u} J R F)) ≫
    (coefficientHomResolutionIso.{u, c, v, w} J R E F).inv

/-- Naturality in the outer variables and dinaturality in the middle variable of
composition defined as the transpose of the two counit evaluations.
Source: Stacks 08J9 and 0A98
(blueprint: lem-sfb-ringed-hom-composition-model).
Proof: apply inverse transposition against K to each desired equality. Naturality
of the adjunction in its target proves naturality in M. Parameter naturality of
its counit proves contravariant naturality in K. For u : L → L', use
H(K,u) followed by evaluation = evaluation followed by u, and H(u,M) followed by
evaluation = (1 tensor u) followed by evaluation. Both dinaturality composites
uncurry to the same double evaluation with u between them. Associator naturality
identifies bracketings, and injectivity of transposition gives each equality. -/
theorem ringedHomComposition_naturality
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R)) :
    (∀ (K K' L M : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (a : K' ⟶ K),
      S.composition K L M ≫
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).map (a.op, 𝟙 M) =
        S.tensor.map
          (𝟙 ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op L, M)),
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).map (a.op, 𝟙 L)) ≫
          S.composition K' L M) ∧
    (∀ (K L M M' : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (b : M ⟶ M'),
      S.composition K L M ≫
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).map (𝟙 (op K), b) =
        S.tensor.map
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map (𝟙 (op L), b),
            𝟙 ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))) ≫
          S.composition K L M') ∧
    (∀ (K L L' M : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (f : L ⟶ L'),
      S.tensor.map
          (𝟙 ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op L', M)),
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).map (𝟙 (op K), f)) ≫
          S.composition K L' M =
        S.tensor.map
          (X := ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op L', M),
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L)))
          (Y := ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op L, M),
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L)))
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map (f.op, 𝟙 M),
            𝟙 ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))) ≫
          S.composition K L M) := by
  sorry

/-- Localization of sign-free Hom-complex composition computes the fixed closed
composition, using any K-flat resolution of the second Hom factor.
Source: Stacks 0A98, 08J9 and 0A95
(blueprint: lem-sfb-ringed-hom-composition-model).
Proof (the node's representative-comparison steps 5--8):
1. Put A = Hom(F,G), B = Hom(E,F), C = Hom(E,G). Choose K-flat resolutions
s : P → E and r : U → A (06YS). Invariance of Hom into K-injectives (0A95)
identifies QA,QB,QC with the three fixed derived Hom objects through the fixed
augmentations. The given t : T → B and r,s become invertible after Q.
2. Set V = Tot(T tensor P), with h(z tensor x) = t(z)(s(x)). The normalized
uncurrying model for the K-flat pair T,P identifies Qh with the counit evaluation
against QE after Qt tensor Qs. Total tensor of K-flat complexes is K-flat.
3. Apply normalized uncurrying to the K-flat pair U,V and the map
u ↦ ((z tensor x) ↦ r(u)(t(z)(s(x)))). Counit parameter naturality identifies
its derived map with the double evaluation defining closed composition.
4. Apply the same normalization to W = Tot(U tensor T) and P. The uncurrying
of composition precomposed by r tensor t is the identical triple evaluation.
The representative associator comparison identifies its bracketing with step 3.
Cancel Qr,Qs,Qt and use injectivity of transposition. The one-K-flat tensor
comparison applies to A tensor T although A is arbitrary. No boundedness,
perfectness or flat-term hypothesis on the given T is used. -/
theorem ringedHomComposition_model
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (N : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (D : RingedDerivedTensorCoherence.{c, v, u, w} J R S N β)
    (E F G T : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    [F.IsKInjective] [G.IsKInjective]
    (t : T ⟶ homComplex (R := R) E F)
    (ht : CochainComplex.IsKFlatResolutionIndependentCoefficients (J := J) (R := R) t) :
    (D.tensorIso (homComplex (R := R) F G) T (Or.inr ht.2)).hom ≫
        S.tensor.map
          (ringedHomRepresentativeMap.{c, v, u, w} J R F G,
            DerivedCategory.Q.map t ≫ ringedHomRepresentativeMap.{c, v, u, w} J R E F) ≫
        S.composition (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj G) =
      DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, c, v} J R).map
          (𝟙 (homComplex (R := R) F G), t) ≫ ringedHomComposition.{c, v, u} J R E F G) ≫
        ringedHomRepresentativeMap.{c, v, u, w} J R E G := by
  sorry

end CategoryTheory
