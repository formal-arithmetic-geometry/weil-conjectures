/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The normalized injective finite-total derived comparison

Source: Stacks Project, derived.tex, Tags 015J, 070J and 05TH, with the finite-total
and three-index extensions in the accepted ten-step proof
(blueprint: lem-sfb-injective-finite-total-derived-comparison).

Natural-indexed complexes are extended by zero before unbounded localization.
The finite total is the alternating-coface complex followed by the finite-diagonal total of
def-sp-double-complex-total; its differential is delta + (-1)^n d. It and the localization by
extension by zero are written out through local notation, not imported from the parent
NonnegativeDerivedTotalization module, whose node cites this one as a proof dependency.
The auxiliary parameter h identifies the arbitrary-quasi-isomorphism derived pair of
def-sfb-right-derived-functor. The theorem supplies h from the existing Grothendieck
K-injective resolution construction, rather than assuming an additional hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory

/-- The alternating-coface finite total of a strict nonnegative cosimplicial complex. -/
local notation "nonnegativeCosimplicialTotal" C':max =>
  (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex C' ℕ) ⋙
    HomologicalComplex₂.totalFunctor C' (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ))

/-- Localization of a nonnegative complex after extension by zero. -/
local notation "nonnegativeComplexLocalization" C':max =>
  (ComplexShape.embeddingUpNat.extendFunctor C' ⋙ DerivedCategory.Q)

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

/-- The two parenthesizations of the finite triple total: first total q,s, then n.
Source: Stacks Tag 015J, finite-total extension, proof step 10
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
noncomputable def finiteTripleTotalRight
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    CochainComplex C ℕ :=
  (nonnegativeCosimplicialTotal C).obj
    (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ))

/-- First total n,q in the category of s-complexes, then total with s.
Source: Stacks Tag 015J, finite-total extension, proof step 10
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
noncomputable def finiteTripleTotalLeft
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    CochainComplex C ℕ :=
  HomologicalComplex₂.total
    ((nonnegativeCosimplicialTotal (CochainComplex C ℕ)).obj X) (.up ℕ)

/-- Inclusion of a triple summand into the n,(q,s) grouping.
Source: Stacks Tag 015J, finite-total extension, proof step 10
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
noncomputable def finiteTripleInclusionRight
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (h : n + (q + s) = r) :
    ((X.obj ⦋n⦌).X q).X s ⟶ (finiteTripleTotalRight X).X r :=
  HomologicalComplex₂.ιTotal (X.obj ⦋n⦌) (.up ℕ) q s (q + s) rfl ≫
    HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
      (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ)))
        (.up ℕ) n (q + s) r h

/-- Inclusion of a triple summand into the (n,q),s grouping.
Source: Stacks Tag 015J, finite-total extension, proof step 10
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
noncomputable def finiteTripleInclusionLeft
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (h : (n + q) + s = r) :
    ((X.obj ⦋n⦌).X q).X s ⟶ (finiteTripleTotalLeft X).X r :=
  (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj X)
      (.up ℕ) n q (n + q) rfl).f s ≫
    HomologicalComplex₂.ιTotal ((nonnegativeCosimplicialTotal (CochainComplex C ℕ)).obj X)
      (.up ℕ) (n + q) s r h

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The recorded right-derived unit at a nonnegative complex, including both canonical
localization identifications and the map/extension comparison.
Source: Stacks Tags 070K, 070Y and 015J; proof steps 7--9
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
noncomputable def injectiveFiniteTotalUnit (E : CochainComplex C ℕ) :
    (nonnegativeComplexLocalization D).obj ((F.mapHomologicalComplex (.up ℕ)).obj E) ⟶
      (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj
        ((nonnegativeComplexLocalization C).obj E) :=
  DerivedCategory.Q.map (E.mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
    (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj (E.extend ComplexShape.embeddingUpNat)) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj (E.extend ComplexShape.embeddingUpNat)) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso C).hom.app (E.extend ComplexShape.embeddingUpNat))

/-- All clauses of the normalized finite-total comparison, with real strict diagrams.
The normalization equations are the inverse-unit formulas after cancellation; they uniquely
specify the entire derived isomorphisms. The final field includes the actual canonical
reassociation, normalized on every triple summand, and the comparison commuting square.
Source: Stacks Tags 015J, 070J, 05TH; accepted proof steps 1--10
(blueprint: lem-sfb-injective-finite-total-derived-comparison). -/
structure InjectiveFiniteTotalDerivedComparison where
  beta : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (F.mapHomologicalComplex (.up ℕ)).obj ((nonnegativeCosimplicialTotal C).obj J) ≅
      (nonnegativeCosimplicialTotal D).obj (J ⋙ F.mapHomologicalComplex (.up ℕ))
  beta_summand : ∀ (J : CosimplicialObject (CochainComplex C ℕ))
      (n q r : ℕ) (hnq : n + q = r),
    F.map (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)
        (.up ℕ) n q r hnq) ≫ (beta J).hom.f r =
      HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (J ⋙ F.mapHomologicalComplex (.up ℕ))) (.up ℕ) n q r hnq
  beta_natural : ∀ (J J' : CosimplicialObject (CochainComplex C ℕ)) (g : J ⟶ J'),
    (F.mapHomologicalComplex (.up ℕ)).map ((nonnegativeCosimplicialTotal C).map g) ≫
        (beta J').hom =
      (beta J).hom ≫ (nonnegativeCosimplicialTotal D).map
        (Functor.whiskerRight g (F.mapHomologicalComplex (.up ℕ)))
  beta_unique : ∀ (J : CosimplicialObject (CochainComplex C ℕ))
      (e : (F.mapHomologicalComplex (.up ℕ)).obj
          ((nonnegativeCosimplicialTotal C).obj J) ≅
        (nonnegativeCosimplicialTotal D).obj (J ⋙ F.mapHomologicalComplex (.up ℕ))),
    (∀ (n q r : ℕ) (hnq : n + q = r),
      F.map (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)
          (.up ℕ) n q r hnq) ≫ e.hom.f r =
        HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
          (J ⋙ F.mapHomologicalComplex (.up ℕ))) (.up ℕ) n q r hnq) →
      e = beta J
  total_quasiIso : ∀ (K J : CosimplicialObject (CochainComplex C ℕ)) (u : K ⟶ J),
    (∀ n : SimplexCategory, QuasiIso (u.app n)) →
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
      QuasiIso ((nonnegativeCosimplicialTotal C).map u)
  total_injective : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
      ∀ r : ℤ, Injective
        (((nonnegativeCosimplicialTotal C).obj J).extend ComplexShape.embeddingUpNat |>.X r)
  total_kInjective : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
      CochainComplex.IsKInjective (((nonnegativeCosimplicialTotal C).obj J).extend
        ComplexShape.embeddingUpNat)
  column_kInjective : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
      ∀ n : SimplexCategory,
        CochainComplex.IsKInjective ((J.obj n).extend ComplexShape.embeddingUpNat)
  unit_isIso : ∀ E : CochainComplex C ℕ,
    (∀ q : ℕ, Injective (E.X q)) → IsIso (injectiveFiniteTotalUnit F h E)
  derived : ∀ (K J : CosimplicialObject (CochainComplex C ℕ)) (u : K ⟶ J),
    (∀ n : SimplexCategory, QuasiIso (u.app n)) →
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
    ∃ chi : (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj
          ((nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj K)) ≅
        (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
          (J ⋙ F.mapHomologicalComplex (.up ℕ))),
      (chi.hom ≫ (nonnegativeComplexLocalization D).map (beta J).inv ≫
          injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J) =
        (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
          ((nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map u))) ∧
      (∀ e : (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj
            ((nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj K)) ≅
          (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
            (J ⋙ F.mapHomologicalComplex (.up ℕ))),
        e.hom ≫ (nonnegativeComplexLocalization D).map (beta J).inv ≫
            injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J) =
          (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
            ((nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map u)) →
        e = chi) ∧
      ∃ c : K ⋙ nonnegativeComplexLocalization C ⋙
            F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
          J ⋙ F.mapHomologicalComplex (.up ℕ) ⋙ nonnegativeComplexLocalization D,
        ∀ n : SimplexCategory,
          c.hom.app n ≫ injectiveFiniteTotalUnit F h (J.obj n) =
            (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
              ((nonnegativeComplexLocalization C).map (u.app n))
  reassociation : ∀ X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)),
    ∃ (aC : finiteTripleTotalRight X ≅ finiteTripleTotalLeft X)
      (aD : finiteTripleTotalRight
          (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)) ≅
        finiteTripleTotalLeft
          (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)))
      (b : X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ) ⋙
            F.mapHomologicalComplex (.up ℕ) ≅
          X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ) ⋙
            HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ))
      (bL : (F.mapHomologicalComplex (.up ℕ)).obj (finiteTripleTotalLeft X) ≅
        finiteTripleTotalLeft
          (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))),
      (∀ (n q s r : ℕ) (hr : n + (q + s) = r) (hl : (n + q) + s = r),
        finiteTripleInclusionRight X n q s r hr ≫ aC.hom.f r =
          finiteTripleInclusionLeft X n q s r hl) ∧
      (∀ (n q s r : ℕ) (hr : n + (q + s) = r) (hl : (n + q) + s = r),
        finiteTripleInclusionRight
            (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
            n q s r hr ≫ aD.hom.f r =
          finiteTripleInclusionLeft
            (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
            n q s r hl) ∧
      (∀ (n : SimplexCategory) (q s t : ℕ) (hqs : q + s = t),
        F.map (HomologicalComplex₂.ιTotal (X.obj n) (.up ℕ) q s t hqs) ≫ (b.hom.app n).f t =
          HomologicalComplex₂.ιTotal
            (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj (X.obj n))
            (.up ℕ) q s t hqs) ∧
      (∀ (n q s r : ℕ) (hl : (n + q) + s = r),
        F.map (finiteTripleInclusionLeft X n q s r hl) ≫ bL.hom.f r =
          finiteTripleInclusionLeft
            (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
            n q s r hl) ∧
      (F.mapHomologicalComplex (.up ℕ)).map aC.hom ≫ bL.hom =
        (beta (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ))).hom ≫
          (nonnegativeCosimplicialTotal D).map b.hom ≫ aD.hom

section FiniteTotals

omit [HasDerivedCategory C] [HasDerivedCategory D]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_finite (r : ℕ) :
    Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {r}) := by
  refine Set.Finite.to_subtype ((Set.finite_Iic (r, r)).subset ?_)
  rintro ⟨n, q⟩ (h : n + q = r)
  simp only [Set.mem_Iic, Prod.mk_le_mk]
  omega

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def totalMapInverse
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (HomologicalComplex₂.total
      (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K) (.up ℕ)) ⟶
      (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) where
  f r := HomologicalComplex₂.totalDesc _
    (fun n q hnq ↦ F.map (K.ιTotal (.up ℕ) n q r hnq))
  comm' r r' h := by
    obtain rfl : r + 1 = r' := h
    apply HomologicalComplex₂.total.hom_ext
    intro n q hnq
    erw [HomologicalComplex₂.ι_totalDesc_assoc]
    change F.map (K.ιTotal (.up ℕ) n q r hnq) ≫ F.map ((K.total (.up ℕ)).d r (r + 1)) = _
    erw [← F.map_comp, HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ (show n + 1 = n + 1 from rfl) q _ (by
        change (n + 1) + q = r + 1; change n + q = r at hnq; omega),
      HomologicalComplex₂.d₂_eq _ _ n (show q + 1 = q + 1 from rfl) _ (by
        change n + (q + 1) = r + 1; change n + q = r at hnq; omega)]
    erw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
      HomologicalComplex₂.d₁_eq _ _ (show n + 1 = n + 1 from rfl) q _ (by
        change (n + 1) + q = r + 1; change n + q = r at hnq; omega),
      HomologicalComplex₂.d₂_eq _ _ n (show q + 1 = q + 1 from rfl) _ (by
        change n + (q + 1) = r + 1; change n + q = r at hnq; omega)]
    simp only [Functor.map_add, Functor.map_units_smul, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_totalDesc]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem totalMapInverse_isIso
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : IsIso (totalMapInverse F K) := by
  have hr (r : ℕ) : IsIso ((totalMapInverse F K).f r) := by
    have := diagonal_finite r
    change IsIso (sigmaComparison F (K.toGradedObject.mapObjFun
      (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) r))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def totalMapIso
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) ≅
      (HomologicalComplex₂.total
        (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K) (.up ℕ)) := by
  have := totalMapInverse_isIso F K
  exact (asIso (totalMapInverse F K)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma totalMapIso_summand
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
    (n q r : ℕ) (hnq : n + q = r) :
    F.map (K.ιTotal (.up ℕ) n q r hnq) ≫ (totalMapIso F K).hom.f r =
      HomologicalComplex₂.ιTotal
        (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K)
        (.up ℕ) n q r hnq := by
  apply (cancel_mono ((totalMapIso F K).inv.f r)).mp
  erw [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  erw [Category.comp_id]
  simp [totalMapIso, totalMapInverse]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cofaceMapIso
    (J : CosimplicialObject (CochainComplex C ℕ)) :
    (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)) ≅
    AlgebraicTopology.AlternatingCofaceMapComplex.obj (J ⋙ F.mapHomologicalComplex (.up ℕ)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro n m hnm
    obtain rfl : n + 1 = m := hnm
    ext q
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteTotalBeta
    (J : CosimplicialObject (CochainComplex C ℕ)) :
    (F.mapHomologicalComplex (.up ℕ)).obj ((nonnegativeCosimplicialTotal C).obj J) ≅
      (nonnegativeCosimplicialTotal D).obj (J ⋙ F.mapHomologicalComplex (.up ℕ)) :=
  totalMapIso F (AlgebraicTopology.AlternatingCofaceMapComplex.obj J) ≪≫
    HomologicalComplex₂.total.mapIso (cofaceMapIso F J) (.up ℕ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteTotalBeta_summand
    (J : CosimplicialObject (CochainComplex C ℕ)) (n q r : ℕ) (hnq : n + q = r) :
    F.map (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)
        (.up ℕ) n q r hnq) ≫ (finiteTotalBeta F J).hom.f r =
      HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (J ⋙ F.mapHomologicalComplex (.up ℕ))) (.up ℕ) n q r hnq := by
  simp only [finiteTotalBeta, Iso.trans_hom, HomologicalComplex.comp_f, ← Category.assoc,
    totalMapIso_summand, HomologicalComplex₂.total.mapIso_hom,
    HomologicalComplex₂.ιTotal_map]
  simp [cofaceMapIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma mappedTotal_ext
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) (r : ℕ) {Z : D}
    (a b : F.obj ((K.total (.up ℕ)).X r) ⟶ Z)
    (hab : ∀ n q (hnq : n + q = r),
      F.map (K.ιTotal (.up ℕ) n q r hnq) ≫ a =
        F.map (K.ιTotal (.up ℕ) n q r hnq) ≫ b) : a = b := by
  have := diagonal_finite r
  apply (isColimitOfHasCoproductOfPreservesColimit F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) r)).hom_ext
  rintro ⟨⟨n, q⟩, hnq⟩
  exact hab n q hnq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteTotalBeta_natural
    (J J' : CosimplicialObject (CochainComplex C ℕ)) (g : J ⟶ J') :
    (F.mapHomologicalComplex (.up ℕ)).map ((nonnegativeCosimplicialTotal C).map g) ≫
        (finiteTotalBeta F J').hom =
      (finiteTotalBeta F J).hom ≫ (nonnegativeCosimplicialTotal D).map
        (Functor.whiskerRight g (F.mapHomologicalComplex (.up ℕ))) := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply mappedTotal_ext F _ r
  intro n q hnq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.comp_map, HomologicalComplex₂.totalFunctor_map]
  erw [← F.map_comp_assoc, HomologicalComplex₂.ιTotal_map,
    F.map_comp, Category.assoc, finiteTotalBeta_summand,
    ← Category.assoc, finiteTotalBeta_summand, HomologicalComplex₂.ιTotal_map]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteTotalBeta_unique
    (J : CosimplicialObject (CochainComplex C ℕ))
    (e : (F.mapHomologicalComplex (.up ℕ)).obj ((nonnegativeCosimplicialTotal C).obj J) ≅
      (nonnegativeCosimplicialTotal D).obj (J ⋙ F.mapHomologicalComplex (.up ℕ)))
    (he : ∀ n q r (hnq : n + q = r),
      F.map (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)
          (.up ℕ) n q r hnq) ≫ e.hom.f r =
        HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
          (J ⋙ F.mapHomologicalComplex (.up ℕ))) (.up ℕ) n q r hnq) :
    e = finiteTotalBeta F J := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext r
  apply mappedTotal_ext F _ r
  intro n q hnq
  exact (he n q r hnq).trans (finiteTotalBeta_summand F J n q r hnq).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteTotal_injective
    (J : CosimplicialObject (CochainComplex C ℕ))
    (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q))
    (r : ℕ) : Injective (((nonnegativeCosimplicialTotal C).obj J).X r) := by
  have := diagonal_finite r
  let := Fintype.ofFinite
    ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {r})
  let A := (HomologicalComplex₂.toGradedObject
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj J)).mapObjFun
    (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) r
  have (i : (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {r}) : Injective (A i) :=
    hJ ⦋i.val.1⦌ i.val.2
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  exact Injective.of_iso (biproduct.isoCoproduct A) inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem nonnegative_injective_kInjective (E : CochainComplex C ℕ)
    (hE : ∀ q : ℕ, Injective (E.X q)) :
    CochainComplex.IsKInjective (E.extend ComplexShape.embeddingUpNat) := by
  have := hE
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteTotal_quasiIso
    (K J : CosimplicialObject (CochainComplex C ℕ)) (u : K ⟶ J)
    (hu : ∀ n : SimplexCategory, QuasiIso (u.app n)) :
    QuasiIso ((nonnegativeCosimplicialTotal C).map u) := by
  let g := (AlgebraicTopology.alternatingCofaceMapComplex _).map u
  let G := HomologicalComplex₂.flipFunctor C (.up ℕ) (.up ℕ)
  have hg : QuasiIso (HomologicalComplex₂.total.map (G.map g) (.up ℕ)) := by
    apply HomologicalComplex₂.quasiIso_totalMap_of_columns
    intro n
    exact hu ⦋n⦌
  have hn : HomologicalComplex₂.total.map (G.map g) (.up ℕ) ≫
      (HomologicalComplex₂.totalFlipIso
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj J) (.up ℕ)).hom =
    (HomologicalComplex₂.totalFlipIso
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj K) (.up ℕ)).hom ≫
      HomologicalComplex₂.total.map g (.up ℕ) := by
    ext r q n hnq
    simp only [HomologicalComplex.comp_f]
    erw [HomologicalComplex₂.ιTotal_map_assoc]
    change (u.app ⦋n⦌).f q ≫ _ = _
    erw [HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
      HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc, Linear.units_smul_comp,
      HomologicalComplex₂.ιTotal_map, Linear.comp_units_smul]
    rfl
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (HomologicalComplex₂.totalFlipIso
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj K) (.up ℕ))
      (HomologicalComplex₂.totalFlipIso
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj J) (.up ℕ)) hn.symm)).mp hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma total_d_summand
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
    (n q r : ℕ) (hnq : n + q = r) :
    K.ιTotal (.up ℕ) n q r hnq ≫ (K.total (.up ℕ)).d r (r + 1) =
      (K.d n (n + 1)).f q ≫ K.ιTotal (.up ℕ) (n + 1) q (r + 1) (by
        change (n + 1) + q = r + 1; omega) +
      (-1 : ℤˣ) ^ n • ((K.X n).d q (q + 1) ≫
        K.ιTotal (.up ℕ) n (q + 1) (r + 1) (by
          change n + (q + 1) = r + 1; omega)) := by
  erw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq _ _ (show n + 1 = n + 1 from rfl) q _ (by
      change (n + 1) + q = r + 1; omega),
    HomologicalComplex₂.d₂_eq _ _ n (show q + 1 = q + 1 from rfl) _ (by
      change n + (q + 1) = r + 1; omega)]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleRight_ext
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (r : ℕ) {Z : C} (a b : (finiteTripleTotalRight X).X r ⟶ Z)
    (hab : ∀ n q s (h : n + (q + s) = r),
      finiteTripleInclusionRight X n q s r h ≫ a =
        finiteTripleInclusionRight X n q s r h ≫ b) : a = b := by
  apply HomologicalComplex₂.total.hom_ext
  intro n t hnt
  apply HomologicalComplex₂.total.hom_ext
  intro q s hqs
  change q + s = t at hqs
  subst t
  simpa [finiteTripleInclusionRight, Category.assoc,
    AlgebraicTopology.alternatingCofaceMapComplex] using hab n q s hnt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleLeft_ext
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (r : ℕ) {Z : C} (a b : (finiteTripleTotalLeft X).X r ⟶ Z)
    (hab : ∀ n q s (h : (n + q) + s = r),
      finiteTripleInclusionLeft X n q s r h ≫ a =
        finiteTripleInclusionLeft X n q s r h ≫ b) : a = b := by
  apply HomologicalComplex₂.total.hom_ext
  intro t s hts
  apply mappedTotal_ext (HomologicalComplex.eval C (.up ℕ) s) _ t
  intro n q hnq
  change n + q = t at hnq
  subst t
  simpa [finiteTripleInclusionLeft, Category.assoc,
    AlgebraicTopology.alternatingCofaceMapComplex] using hab n q s hts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def tripleRightToLeftX
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) (r : ℕ) :
    (finiteTripleTotalRight X).X r ⟶ (finiteTripleTotalLeft X).X r :=
  HomologicalComplex₂.totalDesc _ (fun n t hnt ↦
    HomologicalComplex₂.totalDesc (X.obj ⦋n⦌) (fun q s hqs ↦
      finiteTripleInclusionLeft X n q s r (by
        change n + t = r at hnt; change q + s = t at hqs; omega)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def tripleLeftToRightX
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) (r : ℕ) :
    (finiteTripleTotalLeft X).X r ⟶ (finiteTripleTotalRight X).X r :=
  HomologicalComplex₂.totalDesc _ (fun t s hts ↦
    (totalMapIso (HomologicalComplex.eval C (.up ℕ) s)
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj X)).hom.f t ≫
    HomologicalComplex₂.totalDesc _ (fun n q hnq ↦
      finiteTripleInclusionRight X n q s r (by
        change t + s = r at hts; change n + q = t at hnq; omega)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleRightToLeftX_summand
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) (hl : (n + q) + s = r) :
    finiteTripleInclusionRight X n q s r hr ≫ tripleRightToLeftX X r =
      finiteTripleInclusionLeft X n q s r hl := by
  simp only [finiteTripleInclusionRight, tripleRightToLeftX, Category.assoc]
  erw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalDesc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma tripleRightToLeftX_summand_normalized
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) :
    finiteTripleInclusionRight X n q s r hr ≫ tripleRightToLeftX X r =
      finiteTripleInclusionLeft X n q s r ((Nat.add_assoc n q s).trans hr) :=
  tripleRightToLeftX_summand X n q s r hr _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleLeftToRightX_summand
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) (hl : (n + q) + s = r) :
    finiteTripleInclusionLeft X n q s r hl ≫ tripleLeftToRightX X r =
      finiteTripleInclusionRight X n q s r hr := by
  simp only [finiteTripleInclusionLeft, tripleLeftToRightX, Category.assoc,
    HomologicalComplex₂.ι_totalDesc]
  erw [← Category.assoc, totalMapIso_summand
    (HomologicalComplex.eval C (.up ℕ) s) _ n q (n + q) rfl]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleRight_ι
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s t r : ℕ) (ht : q + s = t) (hr : n + t = r) :
    (X.obj ⦋n⦌).ιTotal (.up ℕ) q s t ht ≫
      HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ)))
        (.up ℕ) n t r hr =
      finiteTripleInclusionRight X n q s r (by omega) := by
  subst t
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleLeft_ι
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s t r : ℕ) (ht : n + q = t) (hr : t + s = r) :
    (HomologicalComplex₂.ιTotal (AlgebraicTopology.AlternatingCofaceMapComplex.obj X)
      (.up ℕ) n q t ht).f s ≫
      HomologicalComplex₂.ιTotal ((nonnegativeCosimplicialTotal (CochainComplex C ℕ)).obj X)
        (.up ℕ) t s r hr =
      finiteTripleInclusionLeft X n q s r (by omega) := by
  subst t
  rfl

private lemma sum_f {A B : CochainComplex C ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → (A ⟶ B)) (q : ℕ) :
    (∑ i ∈ t, f i).f q = ∑ i ∈ t, (f i).f q := by
  exact map_sum (HomologicalComplex.Hom.fAddMonoidHom q) f t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleRight_d
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) :
    finiteTripleInclusionRight X n q s r hr ≫ (finiteTripleTotalRight X).d r (r + 1) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (((X.δ i).f q).f s ≫ finiteTripleInclusionRight X (n + 1) q s (r + 1)
          (by omega))) +
      (-1 : ℤˣ) ^ n • (((X.obj ⦋n⦌).d q (q + 1)).f s ≫
        finiteTripleInclusionRight X n (q + 1) s (r + 1) (by omega)) +
      (-1 : ℤˣ) ^ (n + q) • (((X.obj ⦋n⦌).X q).d s (s + 1) ≫
        finiteTripleInclusionRight X n q (s + 1) (r + 1) (by omega)) := by
  unfold finiteTripleTotalRight
  erw [finiteTripleInclusionRight, Category.assoc, total_d_summand]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_f,
    HomologicalComplex.zsmul_f_apply, Preadditive.comp_add, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp]
  simp only [CosimplicialObject.δ, Functor.comp_map, HomologicalComplex₂.totalFunctor_map,
    HomologicalComplex₂.ιTotal_map_assoc]
  erw [Linear.comp_units_smul, ← Category.assoc, total_d_summand]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, smul_add, smul_smul,
    ← pow_add, Category.assoc]
  refine (add_assoc _ _ _).symm.trans ?_
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      apply congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
      exact congrArg (fun f ↦ ((X.δ i).f q).f s ≫ f)
        (tripleRight_ι X (n + 1) q s (q + s) (r + 1) rfl (by omega))
    · apply congrArg ((-1 : ℤˣ) ^ n • ·)
      exact congrArg (fun f ↦ ((X.obj ⦋n⦌).d q (q + 1)).f s ≫ f)
        (tripleRight_ι X n (q + 1) s (q + s + 1) (r + 1) (by omega) (by omega))
  · apply congrArg ((-1 : ℤˣ) ^ (n + q) • ·)
    exact congrArg (fun f ↦ ((X.obj ⦋n⦌).X q).d s (s + 1) ≫ f)
      (tripleRight_ι X n q (s + 1) (q + s + 1) (r + 1) (by omega) (by omega))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleLeft_d
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hl : (n + q) + s = r) :
    finiteTripleInclusionLeft X n q s r hl ≫ (finiteTripleTotalLeft X).d r (r + 1) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (((X.δ i).f q).f s ≫ finiteTripleInclusionLeft X (n + 1) q s (r + 1)
          (by omega))) +
      (-1 : ℤˣ) ^ n • (((X.obj ⦋n⦌).d q (q + 1)).f s ≫
        finiteTripleInclusionLeft X n (q + 1) s (r + 1) (by omega)) +
      (-1 : ℤˣ) ^ (n + q) • (((X.obj ⦋n⦌).X q).d s (s + 1) ≫
        finiteTripleInclusionLeft X n q (s + 1) (r + 1) (by omega)) := by
  unfold finiteTripleTotalLeft
  erw [finiteTripleInclusionLeft, Category.assoc, total_d_summand]
  erw [Preadditive.comp_add, Linear.comp_units_smul]
  have hd := congrArg (fun g ↦ g.f s)
    (total_d_summand (AlgebraicTopology.AlternatingCofaceMapComplex.obj X)
      n q (n + q) rfl)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
    HomologicalComplex.units_smul_f_apply] at hd
  erw [← Category.assoc, hd, Preadditive.add_comp, Linear.units_smul_comp]
  have hv := (HomologicalComplex₂.ιTotal
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj X) (.up ℕ)
    n q (n + q) rfl).comm s (s + 1)
  erw [reassoc_of% hv]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_f,
    HomologicalComplex.zsmul_f_apply, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Category.assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      apply congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
      exact congrArg (fun f ↦ ((X.δ i).f q).f s ≫ f)
        (tripleLeft_ι X (n + 1) q s (n + q + 1) (r + 1) (by omega) (by omega))
    · apply congrArg ((-1 : ℤˣ) ^ n • ·)
      exact congrArg (fun f ↦ ((X.obj ⦋n⦌).d q (q + 1)).f s ≫ f)
        (tripleLeft_ι X n (q + 1) s (n + q + 1) (r + 1) (by omega) (by omega))
  · apply congrArg ((-1 : ℤˣ) ^ (n + q) • ·)
    exact congrArg (fun f ↦ ((X.obj ⦋n⦌).X q).d s (s + 1) ≫ f)
      (tripleLeft_ι X n q (s + 1) (n + q) (r + 1) rfl (by omega))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def tripleReassociation
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    finiteTripleTotalRight X ≅ finiteTripleTotalLeft X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ {
      hom := tripleRightToLeftX X r
      inv := tripleLeftToRightX X r
      hom_inv_id := by
        apply tripleRight_ext
        intro n q s hr
        erw [← Category.assoc, tripleRightToLeftX_summand X n q s r hr
          (by omega), tripleLeftToRightX_summand]
        · simp
        · exact hr
      inv_hom_id := by
        apply tripleLeft_ext
        intro n q s hl
        erw [← Category.assoc, tripleLeftToRightX_summand X n q s r (by omega) hl,
          tripleRightToLeftX_summand]
        · simp
        · exact hl })
    (by
      intro r r' hrr'
      obtain rfl : r + 1 = r' := hrr'
      apply tripleRight_ext
      intro n q s hr
      erw [← Category.assoc, tripleRightToLeftX_summand X n q s r hr (by omega)]
      dsimp only
      erw [tripleLeft_d]
      erw [← Category.assoc (finiteTripleInclusionRight X n q s r hr)
        ((finiteTripleTotalRight X).d r (r + 1)) (tripleRightToLeftX X (r + 1)),
        tripleRight_d X n q s r hr]
      simp only [Preadditive.add_comp, Preadditive.sum_comp, Preadditive.zsmul_comp,
        Linear.units_smul_comp, Category.assoc, tripleRightToLeftX_summand_normalized])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma totalMapIso_natural
    {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (g : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℕ)).map (HomologicalComplex₂.total.map g (.up ℕ)) ≫
        (totalMapIso F L).hom =
      (totalMapIso F K).hom ≫ HomologicalComplex₂.total.map
        (((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).map g) (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply mappedTotal_ext F K r
  intro n q hnq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [← F.map_comp_assoc, HomologicalComplex₂.ιTotal_map, F.map_comp, Category.assoc,
    totalMapIso_summand, ← Category.assoc, totalMapIso_summand,
    HomologicalComplex₂.ιTotal_map]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def innerTotalBeta
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ) ⋙
        F.mapHomologicalComplex (.up ℕ) ≅
      X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ) :=
  NatIso.ofComponents (fun n ↦ totalMapIso F (X.obj n))
    (fun g ↦ totalMapIso_natural F (X.map g))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def leftTotalBeta
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    (F.mapHomologicalComplex (.up ℕ)).obj (finiteTripleTotalLeft X) ≅
      finiteTripleTotalLeft
        (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)) :=
  (F.mapHomologicalComplex (.up ℕ)).mapIso (tripleReassociation X).symm ≪≫
    finiteTotalBeta F (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ)) ≪≫
    (nonnegativeCosimplicialTotal D).mapIso (innerTotalBeta F X) ≪≫
    tripleReassociation
      (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma tripleReassociation_inv_summand
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) (hl : (n + q) + s = r) :
    finiteTripleInclusionLeft X n q s r hl ≫ (tripleReassociation X).inv.f r =
      finiteTripleInclusionRight X n q s r hr :=
  tripleLeftToRightX_summand X n q s r hr hl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma rightTotalBeta_summand
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hr : n + (q + s) = r) :
    F.map (finiteTripleInclusionRight X n q s r hr) ≫
      (finiteTotalBeta F (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ)
        (.up ℕ))).hom.f r ≫
      ((nonnegativeCosimplicialTotal D).map (innerTotalBeta F X).hom).f r =
    finiteTripleInclusionRight
      (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
        n q s r hr := by
  erw [finiteTripleInclusionRight, F.map_comp, Category.assoc,
    ← Category.assoc _ ((finiteTotalBeta F _).hom.f r), finiteTotalBeta_summand]
  dsimp only [Functor.comp_map, HomologicalComplex₂.totalFunctor_map]
  erw [HomologicalComplex₂.ιTotal_map]
  erw [← Category.assoc, totalMapIso_summand]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma leftTotalBeta_summand
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ)))
    (n q s r : ℕ) (hl : (n + q) + s = r) :
    F.map (finiteTripleInclusionLeft X n q s r hl) ≫ (leftTotalBeta F X).hom.f r =
      finiteTripleInclusionLeft
        (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
        n q s r hl := by
  let a := (F.mapHomologicalComplex (.up ℕ)).map (tripleReassociation X).inv
  let b := (finiteTotalBeta F
    (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ))).hom
  let c := (nonnegativeCosimplicialTotal D).map (innerTotalBeta F X).hom
  let d := (tripleReassociation
    (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))).hom
  change F.map (finiteTripleInclusionLeft X n q s r hl) ≫
    (a.f r ≫ b.f r ≫ c.f r ≫ d.f r) = _
  have ha : F.map (finiteTripleInclusionLeft X n q s r hl) ≫ a.f r =
      F.map (finiteTripleInclusionRight X n q s r (by omega)) := by
    change F.map _ ≫ F.map _ = _
    erw [← F.map_comp, tripleReassociation_inv_summand]
  have hb : F.map (finiteTripleInclusionRight X n q s r (by omega)) ≫
      b.f r ≫ c.f r = finiteTripleInclusionRight
        (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
        n q s r (by omega) := rightTotalBeta_summand F X n q s r _
  rw [← Category.assoc, ha]
  have hb' := congrArg (fun f ↦ f ≫ d.f r) hb
  have hc := tripleRightToLeftX_summand
    (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))
    n q s r (by omega) hl
  simpa only [Category.assoc] using hb'.trans hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma leftTotalBeta_square
    (X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))) :
    (F.mapHomologicalComplex (.up ℕ)).map (tripleReassociation X).hom ≫
      (leftTotalBeta F X).hom =
    (finiteTotalBeta F
      (X ⋙ HomologicalComplex₂.totalFunctor C (.up ℕ) (.up ℕ) (.up ℕ))).hom ≫
      (nonnegativeCosimplicialTotal D).map (innerTotalBeta F X).hom ≫
      (tripleReassociation
        (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ))).hom := by
  simp [leftTotalBeta, ← Functor.map_comp_assoc]

end FiniteTotals

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteTotalUnitNat :
    F.mapHomologicalComplex (.up ℕ) ⋙ nonnegativeComplexLocalization D ⟶
      nonnegativeComplexLocalization C ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h :=
  (Functor.isoWhiskerRight (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F).symm
      DerivedCategory.Q).hom ≫
    Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
      ((Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso D).symm).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
          (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ≫
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
          (F.rightDerivedFunctorOfQuasiIsoResolutions h)).hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteTotalUnitNat_app (E : CochainComplex C ℕ) :
    (finiteTotalUnitNat F h).app E = injectiveFiniteTotalUnit F h E := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteTotalUnit_isIso (E : CochainComplex C ℕ)
    (hE : ∀ q : ℕ, Injective (E.X q)) : IsIso (injectiveFiniteTotalUnit F h E) := by
  have := nonnegative_injective_kInjective E hE
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h
    (E.extend ComplexShape.embeddingUpNat)
  unfold injectiveFiniteTotalUnit
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteTotal_derived
    (K J : CosimplicialObject (CochainComplex C ℕ)) (u : K ⟶ J)
    (hu : ∀ n : SimplexCategory, QuasiIso (u.app n))
    (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) :
    ∃ chi : (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj
          ((nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj K)) ≅
        (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
          (J ⋙ F.mapHomologicalComplex (.up ℕ))),
      (chi.hom ≫ (nonnegativeComplexLocalization D).map (finiteTotalBeta F J).inv ≫
          injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J) =
        (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
          ((nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map u))) ∧
      (∀ e : (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj
            ((nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj K)) ≅
          (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
            (J ⋙ F.mapHomologicalComplex (.up ℕ))),
        e.hom ≫ (nonnegativeComplexLocalization D).map (finiteTotalBeta F J).inv ≫
            injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J) =
          (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
            ((nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map u)) →
        e = chi) ∧
      ∃ c : K ⋙ nonnegativeComplexLocalization C ⋙
            F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
          J ⋙ F.mapHomologicalComplex (.up ℕ) ⋙ nonnegativeComplexLocalization D,
        ∀ n : SimplexCategory,
          c.hom.app n ≫ injectiveFiniteTotalUnit F h (J.obj n) =
            (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
              ((nonnegativeComplexLocalization C).map (u.app n)) := by
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions h
  have := finiteTotal_quasiIso K J u hu
  have : QuasiIso (HomologicalComplex.extendMap ((nonnegativeCosimplicialTotal C).map u)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  have := finiteTotalUnit_isIso F h ((nonnegativeCosimplicialTotal C).obj J)
    (finiteTotal_injective J hJ)
  let a := RF.map ((nonnegativeComplexLocalization C).map
    ((nonnegativeCosimplicialTotal C).map u))
  have : IsIso a := by
    change IsIso (RF.map (DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((nonnegativeCosimplicialTotal C).map u) ComplexShape.embeddingUpNat)))
    infer_instance
  let chi := asIso a ≪≫
    (asIso (injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J))).symm ≪≫
    (nonnegativeComplexLocalization D).mapIso (finiteTotalBeta F J)
  have hchi : chi.hom ≫
      (nonnegativeComplexLocalization D).map (finiteTotalBeta F J).inv ≫
        injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J) = a := by
    simp only [chi, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Functor.mapIso_hom, Category.assoc]
    erw [← Functor.map_comp_assoc]
    simp only [Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    erw [IsIso.inv_hom_id, Category.comp_id]
  refine ⟨chi, hchi, ?_, ?_⟩
  · intro e he
    apply Iso.ext
    apply (cancel_mono ((nonnegativeComplexLocalization D).map (finiteTotalBeta F J).inv ≫
      injectiveFiniteTotalUnit F h ((nonnegativeCosimplicialTotal C).obj J))).mp
    exact he.trans hchi.symm
  · have ha (n : SimplexCategory) :
        IsIso ((Functor.whiskerRight u
          (nonnegativeComplexLocalization C ⋙ RF)).app n) := by
      have := hu n
      have : QuasiIso (HomologicalComplex.extendMap (u.app n)
          ComplexShape.embeddingUpNat) :=
        (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
      change IsIso (RF.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (u.app n) ComplexShape.embeddingUpNat)))
      infer_instance
    have hb (n : SimplexCategory) :
        IsIso ((Functor.whiskerLeft J (finiteTotalUnitNat F h)).app n) := by
      erw [Functor.whiskerLeft_app, finiteTotalUnitNat_app]
      exact finiteTotalUnit_isIso F h (J.obj n) (hJ n)
    have : IsIso (Functor.whiskerRight u (nonnegativeComplexLocalization C ⋙ RF)) :=
      NatIso.isIso_of_isIso_app _
    have : IsIso (Functor.whiskerLeft J (finiteTotalUnitNat F h)) :=
      NatIso.isIso_of_isIso_app _
    refine ⟨asIso (Functor.whiskerRight u (nonnegativeComplexLocalization C ⋙ RF)) ≪≫
      (asIso (Functor.whiskerLeft J (finiteTotalUnitNat F h))).symm, ?_⟩
    intro n
    have := finiteTotalUnit_isIso F h (J.obj n) (hJ n)
    simp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom, Iso.symm_hom, asIso_inv]
    rw [NatIso.isIso_inv_app, Category.assoc]
    change _ ≫ inv (injectiveFiniteTotalUnit F h (J.obj n)) ≫
      injectiveFiniteTotalUnit F h (J.obj n) = _
    simp
    rfl

/-- A natural finite-total chain comparison and its uniquely normalized entire-derived-object
comparison, including all cosimplicial operators and finite three-index reassociation.
Source: Stacks Tags 015J (proof remark (3)), 070J and 05TH, normalized extension
(blueprint: lem-sfb-injective-finite-total-derived-comparison).

Proof:
1. Alternating cofaces square to zero by pairing the cosimplicial identities with opposite
   signs. They commute with the internal differential. This gives the bicomplex of
   def-sp-double-complex-total, and strict maps give its summandwise total maps.
2. In degree r use the finite biproduct indexed by n+q=r. Additivity preserves its
   identities. The map beta sending every F(inclusion) to the new inclusion has inverse
   the sum of F(inclusion) composed with the target projections. Negative degrees are zero.
3. Test the chain equation on these inclusions: both sides are the sum of the mapped
   cofaces plus (-1)^n times the mapped internal differential. The same test proves
   beta natural for every strict map, using def-sp-left-exact-additive.
4. Apply lem-sc-first-quadrant-total-column-comparison after transposing the indices.
   Multiplication on the (n,q) summand by (-1)^(n*q) intertwines d+(-1)^q delta with
   delta+(-1)^n d, and commutes with the map induced by u. Thus T(u) is a quasi-isomorphism.
5. To extend a map into a finite sum of injectives along a mono, extend each projected
   component by def-sp-injective-resolutions and sum their inclusions. This proves every
   total term injective, including the zero terms in negative degrees.
6. The total and each column are bounded below injective complexes, hence K-injective
   by the bounded-below Mathlib instance (lem-weil-pbc-dplus-injective-representative).
7. Grothendieck categories have K-injective resolutions
   (sk-def-sfb-derived-categories). The unit of def-sfb-right-derived-functor
   is invertible on K-injectives. Invert this unit and compose
   RF(QT(u)), its inverse, and Q(beta). All factors are invertible.
8. Invert unit naturality at each column and combine it with strictness of u. This gives
   the normalized column natural isomorphism, for every coface and codegeneracy.
9. Cancel the invertible total unit and Q(beta) to obtain the displayed normalization
   equation; conversely that equation forces chi = RF(QT(u)) followed by rho and Q(beta).
10. Both groupings have the finite triples n+q+s=r as summands. Match each by its identity.
    Both differentials are delta+(-1)^n d_q+(-1)^(n+q) d_s. The identity matching and its
    reverse are chain maps. Each path around the comparison square sends F of every
    original triple inclusion to that same inclusion. Finite-biproduct uniqueness proves
    equality. No step assumes that F is exact, preserves injectives, or preserves u. -/
theorem injective_finite_total_derived_comparison
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [PreservesFiniteLimits F] :
    Nonempty (InjectiveFiniteTotalDerivedComparison F
      (fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{v} C).obj K,
        (CochainComplex.toKInjectiveResolution.{v} C).app K, inferInstance,
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{v} C K).2⟩)) := by
  classical
  let h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s :=
    fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{v} C).obj K,
      (CochainComplex.toKInjectiveResolution.{v} C).app K, inferInstance,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{v} C K).2⟩
  refine ⟨{
    beta := finiteTotalBeta F
    beta_summand := finiteTotalBeta_summand F
    beta_natural := finiteTotalBeta_natural F
    beta_unique := finiteTotalBeta_unique F
    total_quasiIso := fun K J u hu _ ↦ finiteTotal_quasiIso K J u hu
    total_injective := ?_
    total_kInjective := fun J hJ ↦
      nonnegative_injective_kInjective _ (finiteTotal_injective J hJ)
    column_kInjective := fun J hJ n ↦ nonnegative_injective_kInjective _ (hJ n)
    unit_isIso := finiteTotalUnit_isIso F h
    derived := finiteTotal_derived F h
    reassociation := ?_ }⟩
  · intro J hJ r
    have := finiteTotal_injective J hJ
    infer_instance
  · intro X
    refine ⟨tripleReassociation X,
      tripleReassociation
        (X ⋙ (F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)),
      innerTotalBeta F X, leftTotalBeta F X, ?_, ?_, ?_, ?_, leftTotalBeta_square F X⟩
    · intro n q s r hr hl
      exact tripleRightToLeftX_summand X n q s r hr hl
    · intro n q s r hr hl
      exact tripleRightToLeftX_summand _ n q s r hr hl
    · intro n q s t hqs
      exact totalMapIso_summand F (X.obj n) q s t hqs
    · exact leftTotalBeta_summand F X

end CategoryTheory
