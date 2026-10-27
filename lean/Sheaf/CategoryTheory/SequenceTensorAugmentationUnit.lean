/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
public import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.DerivedTowerCounitProjections
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.SequenceTensorAugmentationNormalization
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Sheaf.CategoryTheory.SystemGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # The strict tensor augmentation is the sequence adjunction unit

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6E and 0941;
Derived Categories, Tags 09T5 and 0FND.
(blueprint: lem-sf-sequence-tensor-augmentation-unit)

The existential presentation retains the normalized data of
`SequenceProjection.pushforwardLimitProjections` verbatim. The additional clauses
identify the entire augmentation and its total limit. They impose no conditions
on the coefficients, transition surjectivity, boundedness or countable products.
Index `n` denotes the paper's positive level `n+1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w d

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Append a conclusion to a right-associated conjunction without expanding its members. -/
private theorem appendConjunction
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ Q : Prop}
    (h : P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇ ∧ P₈ ∧ P₉ ∧ P₁₀ ∧ P₁₁) (q : Q) :
    P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇ ∧ P₈ ∧ P₉ ∧ P₁₀ ∧ P₁₁ ∧ Q := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, q⟩

/-- Retain six existing clauses while replacing their final conclusion. -/
private theorem mapConjunctionSix
    {P₁ P₂ P₃ P₄ P₅ P₆ Q R : Prop}
    (h : P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ Q) (f : Q → R) :
    P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ R :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, f h.2.2.2.2.2.2⟩

/-- Retain seven existing clauses while replacing their final conclusion. -/
private theorem mapConjunctionSeven
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ Q R : Prop}
    (h : P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇ ∧ Q) (f : Q → R) :
    P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇ ∧ R :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, f h.2.2.2.2.2.2.2⟩

/-- Append a conclusion to the normalized derived-limit presentation. The body is
exactly its original conjunction, in order, followed by `Extra`.
Source: Stacks 0D6E, 0941 and 07A6.
(blueprint: lem-sf-sequence-tensor-augmentation-unit). -/
def augmentedDerivedLimitProperties
    {D E T : Type*} {K : ℕ → Type*}
    [Category D] [Category E] [Category T] [∀ n, Category (K n)]
    [Abelian D] [Abelian E] [Abelian T] [∀ n, Abelian (K n)]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    [∀ n : ℕ, HasDerivedCategory.{d} (K n)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive]
    (U0 : E ⥤ T) (H : T ⥤ D) [U0.Additive] [H.PreservesZeroMorphisms]
    [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
    (W : ℕ → (T ⥤ D)) (V : ∀ n, E ⥤ K n) (S : ∀ n, K n ⥤ D)
    [∀ n, (W n).Additive] [∀ n, (V n).Additive] [∀ n, (S n).Additive]
    [∀ n, PreservesFiniteLimits (W n)] [∀ n, PreservesFiniteColimits (W n)]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
    (uEval : ∀ n, U0 ⋙ W n ≅ V n ⋙ S n)
    (πOrd : ∀ n, F ⟶ V n ⋙ S n) (fLim : F ≅ U0 ⋙ H) (pOrd : ∀ n, H ⟶ W n)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (RL : DerivedCategory.{d} T ⥤ DerivedCategory.{d} D)
    (etaLim : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (LevelProperty : (∀ n, G ⋙ V n ⊣ S n) → Prop)
    (piLim : ∀ n, RL ⟶ (W n).mapDerivedCategory)
      (xi : ∀ n, U0.mapDerivedCategory ⋙ (W n).mapDerivedCategory ≅
        (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory)
      (c : R ≅ U0.mapDerivedCategory ⋙ RL)
      (levelAdj : ∀ n, G ⋙ V n ⊣ S n)
      (derivedLevelAdj : ∀ n,
        L ⋙ (V n).mapDerivedCategory ⊣ (S n).mapDerivedCategory)
    (Extra : Prop) : Prop :=
    (∀ (T : CochainComplex T ℤ) (n : ℕ),
      etaLim.app T ≫ (piLim n).app (DerivedCategory.Q.obj T) ≫
          (W n).mapDerivedCategoryFactors.hom.app T =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pOrd n) (.up ℤ)).app T)) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        (W n).mapDerivedCategory.map
            (U0.mapDerivedCategoryFactors.hom.app I) ≫
          (W n).mapDerivedCategoryFactors.hom.app
            ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (uEval n) (.up ℤ)).hom.app I)) ∧
    (∀ (I : CochainComplex E ℤ), I.IsKInjective →
      ∀ (T : CochainComplex T ℤ), T.IsKInjective →
      ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      QuasiIso ((H.mapHomologicalComplex
        (.up ℤ)).map j) ∧
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RL.map (U0.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex fLim (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map
            ((H.mapHomologicalComplex
              (.up ℤ)).map j) ≫
          etaLim.app T ≫ RL.map (inv (DerivedCategory.Q.map j))) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)) ∧
    LevelProperty levelAdj ∧
    (∀ (n : ℕ) (Q : CochainComplex D ℤ)
      (K : CochainComplex (K n) ℤ)
      (f : ((G ⋙ V n).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
      (derivedLevelAdj n).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
          ((V n).mapDerivedCategory.map (ε.app Q) ≫
            (V n).mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            (((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
          (S n).mapDerivedCategoryFactors.inv.app K) ∧
    (∀ (P : DerivedCategory.{d} D) (n : ℕ),
      (dAdj.ofNatIsoRight c).unit.app P ≫
          (piLim n).app (U0.mapDerivedCategory.obj (L.obj P)) ≫
          (xi n).hom.app (L.obj P) = (derivedLevelAdj n).unit.app P) ∧
    (∀ (N : DerivedCategory.{d} E) (n : ℕ),
      (V n).mapDerivedCategory.map
          ((dAdj.ofNatIsoRight c).counit.app N) =
        ((derivedLevelAdj n).homEquiv
          ((U0.mapDerivedCategory ⋙ RL).obj N)
          ((V n).mapDerivedCategory.obj N)).symm
            ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N)) ∧
    (∀ (P : DerivedCategory.{d} D)
      (N : DerivedCategory.{d} E)
      (h : P ⟶ (U0.mapDerivedCategory ⋙ RL).obj N) (n : ℕ),
      (V n).mapDerivedCategory.map
          (((dAdj.ofNatIsoRight c).homEquiv P N).symm h) =
        (L ⋙ (V n).mapDerivedCategory).map h ≫
          (V n).mapDerivedCategory.map
            ((dAdj.ofNatIsoRight c).counit.app N)) ∧
    (∀ (P : DerivedCategory.{d} D),
      L.map ((dAdj.ofNatIsoRight c).unit.app P) ≫
        (dAdj.ofNatIsoRight c).counit.app (L.obj P) = 𝟙 (L.obj P)) ∧
    (∀ (N : DerivedCategory.{d} E),
      (dAdj.ofNatIsoRight c).unit.app ((U0.mapDerivedCategory ⋙ RL).obj N) ≫
        (U0.mapDerivedCategory ⋙ RL).map ((dAdj.ofNatIsoRight c).counit.app N) =
          𝟙 ((U0.mapDerivedCategory ⋙ RL).obj N)) ∧ Extra

private theorem appendDerivedLimitProperties
    {D E T : Type*} {K : ℕ → Type*}
    [Category D] [Category E] [Category T] [∀ n, Category (K n)]
    [Abelian D] [Abelian E] [Abelian T] [∀ n, Abelian (K n)]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    [∀ n : ℕ, HasDerivedCategory.{d} (K n)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive]
    (U0 : E ⥤ T) (H : T ⥤ D) [U0.Additive] [H.PreservesZeroMorphisms]
    [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
    (W : ℕ → (T ⥤ D)) (V : ∀ n, E ⥤ K n) (S : ∀ n, K n ⥤ D)
    [∀ n, (W n).Additive] [∀ n, (V n).Additive] [∀ n, (S n).Additive]
    [∀ n, PreservesFiniteLimits (W n)] [∀ n, PreservesFiniteColimits (W n)]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
    (uEval : ∀ n, U0 ⋙ W n ≅ V n ⋙ S n)
    (πOrd : ∀ n, F ⟶ V n ⋙ S n) (fLim : F ≅ U0 ⋙ H) (pOrd : ∀ n, H ⟶ W n)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (RL : DerivedCategory.{d} T ⥤ DerivedCategory.{d} D)
    (etaLim : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (LevelProperty : (∀ n, G ⋙ V n ⊣ S n) → Prop)
    (piLim : ∀ n, RL ⟶ (W n).mapDerivedCategory)
      (xi : ∀ n, U0.mapDerivedCategory ⋙ (W n).mapDerivedCategory ≅
        (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory)
      (c : R ≅ U0.mapDerivedCategory ⋙ RL)
      (levelAdj : ∀ n, G ⋙ V n ⊣ S n)
      (derivedLevelAdj : ∀ n,
        L ⋙ (V n).mapDerivedCategory ⊣ (S n).mapDerivedCategory)
    (Extra : Prop)
    (h : derivedLimitProperties G F U0 H W V S uEval πOrd fLim pOrd L R ε η dAdj RL etaLim
      LevelProperty piLim xi c levelAdj derivedLevelAdj) (e : Extra) :
    augmentedDerivedLimitProperties G F U0 H W V S uEval πOrd fLim pOrd L R ε η dAdj RL etaLim
      LevelProperty piLim xi c levelAdj derivedLevelAdj Extra :=
  appendConjunction h e

/-- The standard K-injective resolution class gives the resolution data used below. -/
private theorem kInjectiveResolutions
    {D : Type*} [Category D] [Abelian D] [Abelian.HasKInjectiveResolutions D]
    (X : CochainComplex D ℤ) :
    ∃ (I : CochainComplex D ℤ) (a : X ⟶ I), I.IsKInjective ∧ QuasiIso a := by
  obtain ⟨I, hi, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  exact ⟨I, a, hi, ha⟩

attribute [local instance 10000] CategoryTheory.HasSheafify.isRightAdjoint

attribute [local irreducible] _root_.instCategoryDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sequence-projection unit is the total derived strict tensor augmentation.
Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6E and 0941;
Derived Categories, Tags 09T5 and 0FND
(blueprint: lem-sf-sequence-tensor-augmentation-unit)

Here `beta` is the ordinary strict augmentation, specified on every local section
by `x ↦ 1 ⊗ x`, the scalar-first notation for `x ⊗ 1`. Its termwise map on
complexes is the single strict chain augmentation. `augmentation` is its natural
localization under the K-flat computation of L and exact restriction U0.
`towerAdj` has the ordinary constant/limit unit normalization. The last equality
is written after the canonical target comparison, with no inverse of a
noninvertible comparison. Its right side is exactly localization of the ordinary
compatible-family map h_Q followed by the universal derived-limit comparison.
The quantification over all flat-term K-flat Q and the natural transformation
`augmentation` express independence of the representative, including transport
along any quasi-isomorphism Q → P in the preceding K-flat computation clause.

Proof plan:
1. Take the normalized ordinary and derived presentation from
   lem-coef-sequence-projection-derived-adjunction and
   lem-coef-sequence-pushforward-limit-projections. The sheafified tensor
   universal property (def-pur-sheaf-tensor-product) gives beta, with local
   sections x mapped to x tensor 1. Transition maps preserve 1, so this is one
   strict tower map. Its ordinary constant/limit adjunct is h_Q.
2. Use lem-pur-system-ringed-sequence-site and
   prop-pur-kinjective-resolutions-exist to resolve the tensor system M by I,
   then U0(I) by a K-injective tower J. By
   lem-coef-restricted-tower-resolution-acyclicity, lim(U0(I) → J) is a
   quasi-isomorphism. The specified comparison is the composition comparison
   of lem-weil-pbc-ringed-topoi-derived-pushforward-composition for the sequence
   factorization. Its normalized value on I is the localization of lim(j)
   Thus the universal comparison on U0(M) is localization of lim(j U0(a))
3. By lem-coef-sequence-adjunction-cochain-transposes the actual unit is the
   compatible family x mapped to a_n(x tensor 1). The ordinary limit universal
   property makes it lim(U0(a)) h_Q. After the specified comparison it is
   localization of h_Q followed by the universal derived-limit comparison.
4. Apply lem-coef-derived-tower-counit-projections,
   lem-weil-pbc-termwise-adjunction-homotopy and
   lem-sfb-resolving-derived-adjunction-normalization to the exact constant
   functor. Its transpose of the strict augmentation resolved into J is
   lim(j U0(a)) h_Q, hence equals Rlim(augmentation) after the constant unit.
   This calculation takes place in the whole derived limit; projections are
   never used to detect equality of maps into a derived limit.
5. Steps 3 and 4 give the same map. The natural K-flat comparison and
   resolution-independent transpose formulas transport the identity through
   every representative. Naturality of the units gives the identity for all
   P in D(A). No flatness of B over A, surjective transition maps, boundedness,
   or exact countable products enters any step. -/
theorem sequenceTensorAugmentationUnit
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A)]
    [∀ n : ℕ, HasDerivedCategory.{d} (systemLevel B n)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) ∧
        ∃ (U0 : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A))
          (_ : U0.Additive) (_ : PreservesFiniteLimits U0)
          (_ : PreservesFiniteColimits U0)
          (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
            (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n))
          (uEval : ∀ n : ℕ,
            U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
              systemEvaluation B n ⋙ restriction A B α n)
          (πOrd : ∀ n : ℕ, F ⟶ systemEvaluation B n ⋙ restriction A B α n)
          (fLim : F ≅ U0 ⋙ (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A))
          (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A) ⥤ DerivedCategory.{d} (Modules A))
          (etaLim : (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
          (piLim : ∀ n : ℕ, RL ⟶
            ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory)
          (xi : ∀ n : ℕ,
            U0.mapDerivedCategory ⋙
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory ≅
              (systemEvaluation B n).mapDerivedCategory ⋙
                (restriction A B α n).mapDerivedCategory)
          (c : R ≅ U0.mapDerivedCategory ⋙ RL)
          (levelAdj : ∀ n : ℕ, G ⋙ systemEvaluation B n ⊣ restriction A B α n)
          (derivedLevelAdj : ∀ n : ℕ,
            L ⋙ (systemEvaluation B n).mapDerivedCategory ⊣
              (restriction A B α n).mapDerivedCategory),
          (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
            (U0.map f).app (op n) ≫ eqToHom (uObj N' n) =
              eqToHom (uObj N n) ≫ (restriction A B α n).map (f.app n)) ∧
          (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
            (V : Cᵒᵖ) (x : (N.level n).val.obj V),
            ((U0.obj N).map (homOfLE h).op).val.app V
                ((eqToHom (uObj N n).symm).val.app V x) =
              (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            (uEval n).hom.app N = eqToHom (uObj N n)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ), (πOrd n).app N = π N n) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            fLim.hom.app N ≫ limit.π (U0.obj N) (op n) ≫ (uEval n).hom.app N = π N n) ∧
          RL.IsRightDerivedFunctor etaLim
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules A) (.up ℤ)) ∧
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            IsIso (etaLim.app T)) ∧
          augmentedDerivedLimitProperties G F U0 (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)
            (fun n ↦ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))
            (systemEvaluation B) (restriction A B α) uEval πOrd fLim
            (fun n ↦ lim.π (op n)) L R ε η derivedAdj RL etaLim
            (fun levelAdj ↦ ∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V)
                (by
                  set_option backward.isDefEq.respectTransparency.types false in
                    exact inferInstance) b
                (h.val.app V x))
            piLim xi c levelAdj derivedLevelAdj
          (∃ (beta : (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⟶ G ⋙ U0)
            (towerAdj :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⊣ RL)
            (augmentation :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⟶
                L ⋙ U0.mapDerivedCategory),
            (∀ (M : Modules A) (n : ℕ) (V : Cᵒᵖ) (x : M.val.obj V),
              (eqToHom (uObj (G.obj M) n)).val.app V
                  (((beta.app M).app (op n)).val.app V x) =
                (e M n).inv.val.app V (tensorSection (α.app (op n)) M V 1 x)) ∧
            (∀ Q : CochainComplex (Modules A) ℤ,
              towerAdj.unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map ((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
                  etaLim.app (((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
            (∀ (P : DerivedCategory.{d} (Modules A)),
              (derivedAdj.ofNatIsoRight c).unit.app P =
                towerAdj.unit.app P ≫ RL.map (augmentation.app P)) ∧
            (∀ (Q : CochainComplex (Modules A) ℤ),
              Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
              (augmentation.app (DerivedCategory.Q.obj Q) ≫
                  U0.mapDerivedCategory.map (ε.app Q) ≫
                  U0.mapDerivedCategoryFactors.hom.app
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
                (Functor.const ℕᵒᵖ :
                  Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q ≫
                  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ∧
              ((derivedAdj.ofNatIsoRight c).unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map (U0.mapDerivedCategory.map (ε.app Q) ≫
                    U0.mapDerivedCategoryFactors.hom.app
                      ((G.mapHomologicalComplex (.up ℤ)).obj Q)) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).homEquiv Q
                      ((U0.mapHomologicalComplex (.up ℤ)).obj
                        ((G.mapHomologicalComplex (.up ℤ)).obj Q))
                      ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ≫
                  etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q))))) :=
    set_option backward.isDefEq.respectTransparency.types true in by
  classical
  let : HasWeakSheafify J AddCommGrpCat.{w} := HasSheafify.isRightAdjoint
  refine Exists.imp ?_ (pushforwardLimitProjections.{u, v, w, d} A B α)
  intro G hg
  refine Exists.imp ?_ hg
  intro F hf
  refine Exists.imp ?_ hf
  intro hG hg
  let := hG
  refine Exists.imp ?_ hg
  intro hF hf
  let := hF
  refine Exists.imp ?_ hf
  intro e he
  refine Exists.imp ?_ he
  intro π hπ
  refine Exists.imp ?_ hπ
  intro adj hord
  have hsection := hord.2.2.2.2.2.1
  refine mapConjunctionSix hord ?_
  intro hderived
  refine Exists.imp ?_ hderived
  intro L hL
  refine Exists.imp ?_ hL
  intro R hR
  refine Exists.imp ?_ hR
  intro ε hε
  refine Exists.imp ?_ hε
  intro η hη
  refine Exists.imp ?_ hη
  intro dAdj hd
  have hnorm := hd.2.2.2.2.2.1
  refine mapConjunctionSix hd ?_
  intro hlimits
  refine Exists.imp ?_ hlimits
  intro U0 hU
  refine Exists.imp ?_ hU
  intro hUadd hU
  let := hUadd
  refine Exists.imp ?_ hU
  intro hUlim hU
  let := hUlim
  refine Exists.imp ?_ hU
  intro hUcolim hU
  let := hUcolim
  refine Exists.imp ?_ hU
  intro uObj hU
  refine Exists.imp ?_ hU
  intro uEval hU
  refine Exists.imp ?_ hU
  intro πOrd hU
  refine Exists.imp ?_ hU
  intro fLim hU
  refine Exists.imp ?_ hU
  intro RL hU
  refine Exists.imp ?_ hU
  intro etaLim hU
  refine Exists.imp ?_ hU
  intro piLim hU
  refine Exists.imp ?_ hU
  intro xi hU
  refine Exists.imp ?_ hU
  intro c hU
  refine Exists.imp ?_ hU
  intro levelAdj hU
  refine Exists.imp ?_ hU
  intro derivedLevelAdj hlimits
  have huEval := hlimits.2.2.1
  have hfLim := hlimits.2.2.2.2.1
  have hRL := hlimits.2.2.2.2.2.1
  have hηLim := hlimits.2.2.2.2.2.2.1
  refine mapConjunctionSeven hlimits ?_
  intro hdata
  refine appendDerivedLimitProperties G F U0
    (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)
    (fun n ↦ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))
    (systemEvaluation B) (restriction A B α) uEval πOrd fLim
    (fun n ↦ lim.π (op n)) L R ε η dAdj RL etaLim
    _ piLim xi c levelAdj derivedLevelAdj _ hdata ?_
  have hcomparison := hdata.2.2.1
  let : IsGrothendieckAbelian.{w} (Modules A) :=
    isGrothendieckAbelian_coefficientUniverse _
  let : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ Modules A) :=
    CategoryTheory.tower_grothendieck _
  let : IsGrothendieckAbelian.{w} (StrictRingSystem B) :=
    strictRingSystem_isGrothendieckAbelian B
  let : Abelian.HasKInjectiveResolutions (StrictRingSystem B) := inferInstance
  let : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Modules A) := inferInstance
  have hresSystem := kInjectiveResolutions (D := StrictRingSystem B)
  have hresTower := kInjectiveResolutions (D := ℕᵒᵖ ⥤ Modules A)
  refine normalizedTensorAugmentation G F adj U0 fLim L R ε η dAdj hnorm RL etaLim c
    hresSystem hresTower hRL hηLim
    (fun I hI T hT j hj ↦ (hcomparison I hI T hT j).2) _ ?_ _ _
  intro beta hbeta M n V x
  have hh := hsection M (G.obj M) (adj.unit.app M) n V 1 x
  rw [adj.homEquiv_symm_unit] at hh
  have hu : (π (G.obj M) n).val.app V ((adj.unit.app M).val.app V x) =
      (e M n).inv.val.app V (tensorSection (α.app (op n)) M V 1 x) := by
    set_option backward.isDefEq.respectTransparency.types false in
    have hone (y : ((G.obj M).level n).val.obj V) :
        @SMul.smul ((B.obj (op n)).obj.obj V) (((G.obj M).level n).val.obj V)
          inferInstance 1 y = y := one_smul _ y
    rw [hone] at hh
    change (e M n).inv.val.app V (tensorSection (α.app (op n)) M V 1 x) = _ at hh
    exact hh.symm
  have hb : (beta.app M).app (op n) ≫ eqToHom (uObj (G.obj M) n) =
      adj.unit.app M ≫ π (G.obj M) n := by
    rw [hbeta]
    erw [← huEval, Category.assoc, Category.assoc, hfLim]
  have hb' := congrArg (fun f ↦ f.val.app V x) hb
  exact hb'.trans hu

end SheafOfModules.SequenceProjection
