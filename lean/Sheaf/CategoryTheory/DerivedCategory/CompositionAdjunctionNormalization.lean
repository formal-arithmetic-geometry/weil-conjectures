/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Normalization of derived composition by the specified adjunctions

Source: Stacks Project, Derived Categories, Tags 09T5, 0DVC and 0FND;
Cohomology on Sites, Tag 0D6E (blueprint: lem-sfb-derived-composition-adjunction-normalization).

The derived left comparison is the canonical descent of the ordinary comparison.
The theorem specifies the right comparison, its K-injective representative, and both
adjunction normalization equations.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uC vA vB vC wA wB wC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The descent of a comparison of exact functors, including the canonical composition
identification. Source: Stacks Project, Tag 09T5 and the left-composition comparison used
in Tag 0D6E (blueprint: lem-sfb-derived-composition-adjunction-normalization). -/
noncomputable def derivedCompositionLeftIso
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
    (La : A ⥤ B) (Lb : B ⥤ C) (Lc : A ⥤ C)
    [La.Additive] [Lb.Additive] [Lc.Additive]
    [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
    [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
    (eL : La ⋙ Lb ≅ Lc) :
    La.mapDerivedCategory ⋙ Lb.mapDerivedCategory ≅ Lc.mapDerivedCategory :=
  letI := comp_preservesFiniteLimits La Lb
  letI := comp_preservesFiniteColimits La Lb
  (Functor.mapDerivedCategoryCompIso La Lb).symm ≪≫ Functor.mapDerivedCategoryNatIso eL

/-- Derived composition has the normalization determined by the specified adjunctions.
Source: Stacks Project, Tags 09T5, 0DVC, 0FND, 070I, 070Y and 08BJ; the composition
and adjoint-uniqueness argument of Tag 0D6E
(blueprint: lem-sfb-derived-composition-adjunction-normalization).

Proof:
1. Grothendieck abelian categories have K-injective resolutions
(sk-def-sfb-derived-categories). Each Ri preserves K-injectives because its specified
left adjoint Li is exact (lem-weil-pbc-right-adjoint-preserves-kinjective).
The right-derived units beta_i are therefore invertible on the complexes in question
(def-sfb-right-derived-functor).
2. The canonical derived hom bijection sends Q(f) to Q(a_i(f));beta_i on a
K-injective target. This follows from the representative formula in
lem-pc-pre-derived-adjoint-functors-general and the K-injective Hom bijection
lem-weil-pbc-kinjective-hom-derived. These are the induced adjunctions of
lem-pc-derived-adjoint-functors, with the termwise adjunctions of
lem-weil-pbc-termwise-adjunction-homotopy.
3. Define kappaD as the conjugate of the descended lambda under the c-adjunction
and the composite of the a,b-adjunctions (def-weil-pbc-adjunction-conjugate and
def-weil-pbc-composite-adjunction). Conjugation of an isomorphism is an isomorphism.
4. Apply the normalized hom bijection first for b and then for a. Naturality
makes the composite resolution comparison beta_a at C(Rb)I followed by
R(Ra)(beta_b at I), with the termwise composition identification inserted.
5. Transpose the localized ordinary c-counit precomposed with lambda. Its ordinary
transpose is C(kappa), while its derived transpose is beta_c;kappaD. The preceding
calculation gives exactly the representative equation below. Both comparison factors
are invertible, so this is the required formula under resolution identifications.
6. Naturality extends this equation along every K-injective resolution and makes it
independent of the resolution. Conjugation intertwines the two hom bijections;
evaluating at identities gives the displayed unit and counit equations, with exactly
the composite unit and counit of def-weil-pbc-composite-adjunction. -/
theorem derivedCompositionAdjunctionNormalization
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Abelian A] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
    (La : A ⥤ B) (Lb : B ⥤ C) (Lc : A ⥤ C)
    (Ra : B ⥤ A) (Rb : C ⥤ B) (Rc : C ⥤ A)
    [La.Additive] [Lb.Additive] [Lc.Additive]
    [Ra.Additive] [Rb.Additive] [Rc.Additive]
    [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
    [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
    (adja : La ⊣ Ra) (adjb : Lb ⊣ Rb) (adjc : Lc ⊣ Rc) (eL : La ⋙ Lb ≅ Lc) :
    ∃ κD : Rc.rightDerivedFunctor ≅ Rb.rightDerivedFunctor ⋙ Ra.rightDerivedFunctor,
      κD = conjugateIsoEquiv adjc.mapDerivedCategoryRightDerivedAdjunction
        (adja.mapDerivedCategoryRightDerivedAdjunction.comp
          adjb.mapDerivedCategoryRightDerivedAdjunction)
        (derivedCompositionLeftIso La Lb Lc eL) ∧
      (∀ (I : CochainComplex C ℤ) [I.IsKInjective],
        CochainComplex.IsKInjective ((Rb.mapHomologicalComplex (.up ℤ)).obj I) ∧
        Rc.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≫
            κD.hom.app
              (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I)) =
          DerivedCategory.Qh.map
              ((NatTrans.mapHomotopyCategory
                (conjugateIsoEquiv adjc (adja.comp adjb) eL).hom (.up ℤ)).app
                  ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (Rb ⋙ Ra)) (.up ℤ)).inv.app
                ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≫
            Ra.rightDerivedFunctorUnit.app
              ((Rb.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≫
            Ra.rightDerivedFunctor.map
              (Rb.rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient C (.up ℤ)).obj I))) ∧
      (∀ X : DerivedCategory A,
        (adja.mapDerivedCategoryRightDerivedAdjunction.comp
            adjb.mapDerivedCategoryRightDerivedAdjunction).unit.app X ≫
            (Rb.rightDerivedFunctor ⋙ Ra.rightDerivedFunctor).map
              ((derivedCompositionLeftIso La Lb Lc eL).hom.app X) =
          adjc.mapDerivedCategoryRightDerivedAdjunction.unit.app X ≫
            κD.hom.app (Lc.mapDerivedCategory.obj X)) ∧
      (∀ Y : DerivedCategory C,
        (La.mapDerivedCategory ⋙ Lb.mapDerivedCategory).map (κD.hom.app Y) ≫
            (adja.mapDerivedCategoryRightDerivedAdjunction.comp
              adjb.mapDerivedCategoryRightDerivedAdjunction).counit.app Y =
          (derivedCompositionLeftIso La Lb Lc eL).hom.app (Rc.rightDerivedFunctor.obj Y) ≫
            adjc.mapDerivedCategoryRightDerivedAdjunction.counit.app Y) := by
  sorry

end CategoryTheory.Adjunction
