/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Scalar linearity of total right derived functors computed by K-injectives

Source: Stacks Project, Derived Categories, Tag 070I (lemma-K-injective), (1) and (3),
with the naturality argument using Tags 070K and 070Y; Differential Graded Algebra,
Tags 09MJ and 09MK (blueprint: lem-weil-kinjective-total-derived-linear).

## Main definitions and statements

* `CategoryTheory.Functor.kInjectiveDerivedRepresentativeIso` is the specified comparison
  for an arbitrary derived object and an arbitrary K-injective representative.
* `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_linear` states additivity,
  scalar linearity, and the unique homotopy-class computation for those representatives.
-/

@[expose] public section

set_option autoImplicit false

universe r wA wB vA vB uA uB

open CategoryTheory

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  (U : A ⥤ B) [U.Additive]
  (enough : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The canonical comparison c_M = eta_I inverse after RU(q_M), for any chosen
K-injective representative of a derived object. This uses the unit of the recorded
universal right-derived pair, not a new choice of resolutions.
Source: Stacks Tags 070I, 070K and 070Y, and the representative formula in
(blueprint: lem-weil-kinjective-total-derived-linear). -/
noncomputable def kInjectiveDerivedRepresentativeIso
    {M : DerivedCategory A} (I : CochainComplex A ℤ) [I.IsKInjective]
    (q : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I)) :
    (U.rightDerivedFunctorOfQuasiIsoResolutions enough).obj M ≅
      DerivedCategory.Qh.obj ((U.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj I)) :=
  letI := U.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
  (U.rightDerivedFunctorOfQuasiIsoResolutions enough).mapIso q ≪≫
    (asIso ((U.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I))).symm

/-- The total right derived functor of an additive scalar-linear functor is additive
and scalar-linear, and its action on any derived morphism is computed by the unique
homotopy class between any specified K-injective representatives.

Source: the scalar-linearity extraction from Stacks Tag 070I, (1) iff (3), together
with the unit of Tags 070K and 070Y and the definitions of Tags 09MJ and 09MK
(blueprint: lem-weil-kinjective-total-derived-linear).

Proof plan:
1. Addition and scalar multiplication of cochain maps preserve the chain-map equation.
   They preserve chain homotopies by the identities for d s + s d, so descend to the
   homotopy category. Additivity and linearity of U make its termwise functor linear.
2. The localization functors are linear by lem-weil-linear-abelian-derived-category.
   Represent homotopy classes by cochain maps to see that Qh and Qh after U_K are linear.
3. Resolve a complex representing each derived object using enough. For any fixed I, J
   and qM, qN, apply lem-weil-pbc-kinjective-hom-derived to obtain a bijective linear Hom
   map. Its inverse sends qM inverse followed by f followed by qN to the unique lift g.
   Injectivity proves that the lifts of f + f' and a f are g + g' and a g.
4. The unit is invertible at I and J by def-sfb-right-derived-functor. Naturality at g,
   followed by the lift equation and functoriality, gives the displayed conjugation
   formula for the comparison isomorphisms c_M and c_N.
5. Keep the representatives fixed for two parallel maps. Apply steps 2--4 to their sum
   and scalar multiples. Bilinearity of composition in D(B) and cancellation of c_M
   and c_N give additivity and scalar linearity of RU. No exactness of U, nor additive
   or linear choice of resolutions, enters this argument. -/
theorem rightDerivedFunctorOfQuasiIsoResolutions_linear
    (R : Type r) [CommRing R] [CategoryTheory.Linear R A] [CategoryTheory.Linear R B]
    [U.Linear R] :
    (U.rightDerivedFunctorOfQuasiIsoResolutions enough).Additive ∧
    Functor.Linear R (U.rightDerivedFunctorOfQuasiIsoResolutions enough) ∧
    (∀ (M N : DerivedCategory A) (I J : CochainComplex A ℤ)
      [I.IsKInjective] [J.IsKInjective]
      (qM : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I))
      (qN : N ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj J))
      (f : M ⟶ N),
      (∃! g : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶
          (HomotopyCategory.quotient A (.up ℤ)).obj J,
        DerivedCategory.Qh.map g = qM.inv ≫ f ≫ qN.hom) ∧
      (∀ g : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶
          (HomotopyCategory.quotient A (.up ℤ)).obj J,
        DerivedCategory.Qh.map g = qM.inv ≫ f ≫ qN.hom →
        (U.kInjectiveDerivedRepresentativeIso enough I qM).inv ≫
            (U.rightDerivedFunctorOfQuasiIsoResolutions enough).map f ≫
            (U.kInjectiveDerivedRepresentativeIso enough J qN).hom =
          DerivedCategory.Qh.map ((U.mapHomotopyCategory (.up ℤ)).map g))) := by
  classical
  let RF := U.rightDerivedFunctorOfQuasiIsoResolutions enough
  let η := U.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough
  let π := HomotopyCategory.quotient A (.up ℤ)
  let T := U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have compute (M N : DerivedCategory A) (I J : CochainComplex A ℤ)
      [I.IsKInjective] [J.IsKInjective]
      (qM : M ≅ DerivedCategory.Qh.obj (π.obj I))
      (qN : N ≅ DerivedCategory.Qh.obj (π.obj J))
      (f : M ⟶ N) (g : π.obj I ⟶ π.obj J)
      (hg : DerivedCategory.Qh.map g = qM.inv ≫ f ≫ qN.hom) :
      (U.kInjectiveDerivedRepresentativeIso enough I qM).inv ≫ RF.map f ≫
          (U.kInjectiveDerivedRepresentativeIso enough J qN).hom = T.map g := by
    have := U.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
    have := U.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough J
    change (η.app (π.obj I) ≫ RF.map qM.inv) ≫ RF.map f ≫
      RF.map qN.hom ≫ CategoryTheory.inv (η.app (π.obj J)) = _
    calc
      _ = η.app (π.obj I) ≫ RF.map (DerivedCategory.Qh.map g) ≫
          CategoryTheory.inv (η.app (π.obj J)) := by
        rw [hg]
        simp only [RF.map_comp, Category.assoc]
      _ = T.map g := by
        have hn : T.map g ≫ η.app (π.obj J) =
            η.app (π.obj I) ≫ RF.map (DerivedCategory.Qh.map g) := η.naturality g
        rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have reps (M : DerivedCategory A) :
      ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective),
        Nonempty (M ≅ DerivedCategory.Qh.obj (π.obj I)) := by
    obtain ⟨I, s, hI, hs⟩ := enough (DerivedCategory.Q.objPreimage M)
    have := hs
    exact ⟨I, hI, ⟨(DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      asIso (DerivedCategory.Q.map s) ≪≫
      (DerivedCategory.quotientCompQhIso A).symm.app I⟩⟩
  have additive : RF.Additive := by
    constructor
    intro M N f f'
    obtain ⟨I, hI, ⟨qM⟩⟩ := reps M
    obtain ⟨J, hJ, ⟨qN⟩⟩ := reps N
    obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).surjective
      (qM.inv ≫ f ≫ qN.hom)
    obtain ⟨g', hg'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).surjective
      (qM.inv ≫ f' ≫ qN.hom)
    have hsum : DerivedCategory.Qh.map (g + g') = qM.inv ≫ (f + f') ≫ qN.hom := by
      simp only [Functor.map_add, hg, hg', Preadditive.add_comp, Preadditive.comp_add]
    apply (cancel_mono (U.kInjectiveDerivedRepresentativeIso enough J qN).hom).1
    apply (cancel_epi (U.kInjectiveDerivedRepresentativeIso enough I qM).inv).1
    rw [compute M N I J qM qN (f + f') (g + g') hsum,
      Preadditive.add_comp, Preadditive.comp_add,
      compute M N I J qM qN f g hg, compute M N I J qM qN f' g' hg', T.map_add]
  have linear : RF.Linear R := by
    constructor
    intro M N f r
    obtain ⟨I, hI, ⟨qM⟩⟩ := reps M
    obtain ⟨J, hJ, ⟨qN⟩⟩ := reps N
    obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).surjective
      (qM.inv ≫ f ≫ qN.hom)
    have hsmul : DerivedCategory.Qh.map (r • g) = qM.inv ≫ (r • f) ≫ qN.hom := by
      simp only [Functor.map_smul, hg, Linear.smul_comp, Linear.comp_smul]
    apply (cancel_mono (U.kInjectiveDerivedRepresentativeIso enough J qN).hom).1
    apply (cancel_epi (U.kInjectiveDerivedRepresentativeIso enough I qM).inv).1
    rw [compute M N I J qM qN (r • f) (r • g) hsmul,
      Linear.smul_comp, Linear.comp_smul, compute M N I J qM qN f g hg, T.map_smul]
  refine ⟨additive, linear, ?_⟩
  intro M N I J hI hJ qM qN f
  constructor
  · exact (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).existsUnique _
  · exact compute M N I J qM qN f

end CategoryTheory.Functor
