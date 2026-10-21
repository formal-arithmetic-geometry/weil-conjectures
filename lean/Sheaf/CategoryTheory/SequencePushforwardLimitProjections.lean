/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Total-limit projections and the sequence-projection adjunction

Source: Stacks Project, Cohomology on Sites, Tags 0D6E, 0941 and 07A6;
Derived Categories, Tag 09T5.
(blueprint: lem-coef-sequence-pushforward-limit-projections).

All functors act on the existing strict-system and module derived categories.
The initial existential data are exactly the normalized presentation provided by
`derivedAdjunction`. Index `n` denotes positive level `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The canonical comparison with restricted total inverse limit preserves its actual
projections and transports the sequence-projection adjunction with the stated level formulas.
Source: Stacks 0D6E, 0941, 07A6 and derived.tex 09T5
(blueprint: lem-coef-sequence-pushforward-limit-projections).

Proof plan:
1. Take the normalized ordinary and derived data of
lem-coef-sequence-projection-derived-adjunction (`derivedAdjunction`), using
lem-pur-system-ringed-sequence-site (`strictSystemSequenceEquivalence`). Factor the
ringed projection through the constant ring sequence. Termwise scalar restriction U0
is exact: kernels and sheafified cokernels are unchanged on underlying abelian sheaves
(def-pc-sheaf-restrict-scalars). Its level identifications have the prescribed section maps.
2. Use prop-pur-kinjective-resolutions-exist on both sequence ringed sites. Apply
lem-weil-pbc-ringed-topoi-derived-pushforward-composition to the factorization, and
lem-weil-pbc-ringed-strict-tower-homotopy-limit to the projection with constant coefficients.
For K-injective I and a K-injective resolution j:U0(I) to T, the comparison is the class
of lim(j), under the displayed universal-unit identifications; lim(j) is a quasi-isomorphism.
3. The equality pr_n(lim(j)) = j_n(pr_n) proves that this comparison preserves the actual
limit projections. The equations with etaLim specify those projections by the ordinary
termwise projections, including on arbitrary complex representatives.
4. Apply lem-weil-pbc-ringed-topoi-module-adjunction at each level. Its scalar transpose
sends a map h to b tensor x mapped to b times h(x). Restriction is exact. Use
lem-pc-kflat-resolution, lem-pur-derived-change-of-rings and
lem-pur-resolving-class-derived-adjunction to derive this adjunction. Its displayed
chain-map equation fixes the canonical transpose for arbitrary targets; K-flat
resolutions extend it to fractions. The level of L is derived scalar extension by the
simultaneous K-flat description in the sequence-projection dependency.
5. Transport derivedAdj along c by Adjunction.ofNatIsoRight. Its unit is the old unit
followed by c, and its counit is L(c inverse) followed by the old counit. Naturality and
the old triangles give both triangle identities as equalities of actual derived maps.
6. On a flat-term K-flat Q, the old unit sends x to (a_n(x tensor 1))_n for a system
resolution a. Step 3 cancels a_n after projection; step 4 identifies the resulting map
with the reduction unit at level n.
7. For a K-injective system I and a K-flat resolution q:Q to lim(U0(I)), the old counit
has components b tensor x mapped to b times pr_n(q(x)). Step 4 gives adjunct pr_n,
and step 3 identifies it with pi_n composed with c. Precomposing with L(c inverse)
gives exactly pi_n. Neither U0(I) nor its levels are assumed K-injective.
8. The inverse transported Hom bijection sends h to L(h) followed by the counit.
Evaluation is functorial and L evaluated at n is scalar extension. This gives the final
component formula, naturally in both arguments, and the two actual triangle equations. -/
theorem pushforwardLimitProjections
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
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ) (n : ℕ),
            etaLim.app T ≫ (piLim n).app (DerivedCategory.Q.obj T) ≫
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj
                  (op n)).mapDerivedCategoryFactors.hom.app T =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T)) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
            (xi n).hom.app (DerivedCategory.Q.obj I) ≫
                (restriction A B α n).mapDerivedCategory.map
                  ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app I) ≫
                (restriction A B α n).mapDerivedCategoryFactors.hom.app
                  (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj I) =
              ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory.map
                  (U0.mapDerivedCategoryFactors.hom.app I) ≫
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj
                  (op n)).mapDerivedCategoryFactors.hom.app
                  ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
                DerivedCategory.Q.map
                  ((NatIso.mapHomologicalComplex (uEval n) (.up ℤ)).hom.app I)) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
            ∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
            QuasiIso (((lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex
              (.up ℤ)).map j) ∧
            η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
                RL.map (U0.mapDerivedCategoryFactors.hom.app I) =
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex fLim (.up ℤ)).hom.app I) ≫
                DerivedCategory.Q.map
                  (((lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex
                    (.up ℤ)).map j) ≫
                etaLim.app T ≫ RL.map (inv (DerivedCategory.Q.map j))) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
            η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
                (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
                (xi n).hom.app (DerivedCategory.Q.obj I) ≫
                (restriction A B α n).mapDerivedCategory.map
                  ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app I) ≫
                (restriction A B α n).mapDerivedCategoryFactors.hom.app
                  (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj I) =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)) ∧
          (∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V) inferInstance b
                (h.val.app V x)) ∧
          (∀ (n : ℕ) (Q : CochainComplex (Modules A) ℤ)
            (K : CochainComplex (systemLevel B n) ℤ)
            (f : ((G ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
            (derivedLevelAdj n).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
                ((systemEvaluation B n).mapDerivedCategory.map (ε.app Q) ≫
                  (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫ DerivedCategory.Q.map f) =
              DerivedCategory.Q.map
                  (((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
                (restriction A B α n).mapDerivedCategoryFactors.inv.app K) ∧
          (∀ (P : DerivedCategory.{d} (Modules A)) (n : ℕ),
            (derivedAdj.ofNatIsoRight c).unit.app P ≫
                (piLim n).app (U0.mapDerivedCategory.obj (L.obj P)) ≫
                (xi n).hom.app (L.obj P) = (derivedLevelAdj n).unit.app P) ∧
          (∀ (N : DerivedCategory.{d} (StrictRingSystem B)) (n : ℕ),
            (systemEvaluation B n).mapDerivedCategory.map
                ((derivedAdj.ofNatIsoRight c).counit.app N) =
              ((derivedLevelAdj n).homEquiv
                ((U0.mapDerivedCategory ⋙ RL).obj N)
                ((systemEvaluation B n).mapDerivedCategory.obj N)).symm
                  ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N)) ∧
          (∀ (P : DerivedCategory.{d} (Modules A))
            (N : DerivedCategory.{d} (StrictRingSystem B))
            (h : P ⟶ (U0.mapDerivedCategory ⋙ RL).obj N) (n : ℕ),
            (systemEvaluation B n).mapDerivedCategory.map
                (((derivedAdj.ofNatIsoRight c).homEquiv P N).symm h) =
              (L ⋙ (systemEvaluation B n).mapDerivedCategory).map h ≫
                (systemEvaluation B n).mapDerivedCategory.map
                  ((derivedAdj.ofNatIsoRight c).counit.app N)) ∧
          (∀ (P : DerivedCategory.{d} (Modules A)),
            L.map ((derivedAdj.ofNatIsoRight c).unit.app P) ≫
              (derivedAdj.ofNatIsoRight c).counit.app (L.obj P) = 𝟙 (L.obj P)) ∧
          (∀ (N : DerivedCategory.{d} (StrictRingSystem B)),
            (derivedAdj.ofNatIsoRight c).unit.app ((U0.mapDerivedCategory ⋙ RL).obj N) ≫
              (U0.mapDerivedCategory ⋙ RL).map ((derivedAdj.ofNatIsoRight c).counit.app N) =
                𝟙 ((U0.mapDerivedCategory ⋙ RL).obj N)) := by
  sorry

end SheafOfModules.SequenceProjection
