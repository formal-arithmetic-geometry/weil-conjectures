/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.ProjectionMateExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.SixFunctors.FieldTensor
import Sheaf.SixFunctors.ProperImageLocalizingProper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Proper projection formula on rational localizing categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field,
sk-thm-sf-pf-field-localizing.md and its proof
(blueprint: det-thm-sf-pf-field-localizing).

Membership of both endpoints and invertibility in the ambient category express
invertibility in the full localizing subcategory. The generators are exactly Dbc,
with finite constant scalar models; no derived completeness condition is imposed.
The five helpers below define the actual projection map on internal module objects,
including the unique representative-normalized tensor comparison. They belong to this
projection formula; the general ringed projection-mate dependency remains unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

section ProjectionMap

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The generator formula for the ordinary pullback tensor comparison. The maps into
extension of scalars are the actual extension units; `tensorObjπ` is the relative
balanced coequalizer projection. Thus this is the map sending a pulled-back pure tensor
to the tensor of the pulled-back factors, not an arbitrary tensor isomorphism.
Source: Stacks Tag 0B56, canonical tensor comparison
(blueprint: det-thm-sf-pf-field-localizing). -/
def ModuleObjectTensorGeneratorFormula
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (b : (upperStar Λ f).obj (M ⊗ N) ⟶
      (upperStar Λ f).obj M ⊗ (upperStar Λ f).obj N) : Prop :=
  (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫
      Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj (M ⊗ N)) ≫ b.hom =
    Functor.OplaxMonoidal.δ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
      (Mod.extendUnitHom (condensedPullbackHom Λ f)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj M) ⊗ₘ
        Mod.extendUnitHom (condensedPullbackHom Λ f)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj N)) ≫
      Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)

/-- Characterization of the derived tensor comparison by its signed direct-sum total
map and the derived-functor counits. Each component of the total map is specified on every
summand by the ordinary balanced tensor formula. The condition is imposed on all complexes,
so it retains the unbounded comparison, with no boundedness or completeness condition.
Source: Stacks Tags 06YU, 07A4 and 0B56
(blueprint: det-thm-sf-pf-field-localizing). -/
def ModuleObjectDerivedTensorFormula
    (μ : Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f)) : Prop :=
  letI : HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    Mod.hasColimitsOfSize
  letI : HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
    Mod.hasColimitsOfSize
  letI : ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ,
      HomologicalComplex.HasTensor K P :=
    fun _K _P _n ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (HasColimitsOfSize.has_colimits_of_shape _) _
  letI : ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ,
      HomologicalComplex.HasTensor K P :=
    fun _K _P _n ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (HasColimitsOfSize.has_colimits_of_shape _) _
  ∀ K P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ,
    ∃ q : ((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj K P) ⟶
        HomologicalComplex.tensorObj
          (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj K)
          (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (i j n : ℤ) (h : i + j = n),
        ∃ b : (upperStar Λ f).obj (K.X i ⊗ P.X j) ⟶
            (upperStar Λ f).obj (K.X i) ⊗ (upperStar Λ f).obj (P.X j),
          ModuleObjectTensorGeneratorFormula Λ f (K.X i) (P.X j) b ∧
          (upperStar Λ f).map (HomologicalComplex.ιTensorObj K P i j n h) ≫ q.f n =
            b ≫ HomologicalComplex.ιTensorObj
              (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj K)
              (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) i j n h) ∧
      (μ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj P) ≫
          ((Functor.derivedTensorLeftDerivedCounit (upperStar Λ f)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ((Functor.leftDerivedDerivedTensorCounit (upperStar Λ f)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Q.map q

/-- The canonical tensor comparison exists uniquely with its representative normalization.
Source: Stacks Tags 06YU, 07A4, 07A6 and 0B56
(blueprint: det-thm-sf-pf-field-localizing).

Proof: identify internal modules with module sheaves of their section ring, preserving
relative tensor and the module pullback adjunction. The balanced coequalizer universal
property gives the ordinary comparison with the displayed extension-unit formula; its
inverse multiplies scalars. Since the coefficient comparison is an isomorphism, pullback
is exact and preserves colimits. On total complexes the comparison is specified on each
(i,j) summand by this ordinary map. Additivity makes it commute with the differential,
including the Koszul sign. Descend by the two-variable K-flat universal property as in
lem-weil-pbc-ringed-projection-mate-exact. The counit equation characterizes this descent
uniquely. The inverse ordinary comparison descends in the same way, so the result is an
isomorphism. These constructions transport back to the existing internal-module category.
-/
theorem existsUnique_moduleObjectDerivedTensorComparison :
    ∃! μ : Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
        Functor.derivedTensorLeftDerived (upperStar Λ f),
      ModuleObjectDerivedTensorFormula Λ f μ ∧ IsIso μ := sorry

/-- The unique representative-normalized tensor comparison. Its data are determined by
`ModuleObjectDerivedTensorFormula`, not by a mere existence of an isomorphism.
Source: Stacks Tag 0B56 (blueprint: det-thm-sf-pf-field-localizing). -/
noncomputable def moduleObjectDerivedTensorComparison :
    Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f) :=
  (existsUnique_moduleObjectDerivedTensorComparison Λ f).exists.choose

/-- The actual counit mate `(Rf_* A) ⊗ B ⟶ Rf_*(A ⊗ Lf^* B)` on internal module objects.
The existing derived adjunction and the normalized comparison determine this map.
Source: Stacks Tag 0B56 (blueprint: det-thm-sf-pf-field-localizing). -/
noncomputable def moduleObjectProjectionMate
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ f).rightDerivedFunctor.obj A ⊗ B ⟶
      (lowerStar Λ f).rightDerivedFunctor.obj
        (A ⊗ (upperStar Λ f).leftDerivedFunctor.obj B) :=
  (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (moduleObjectDerivedTensorComparison Λ f)).app A).app B

end ProjectionMap

/-- Proper projection formula on Loc(Dbc) for a finite extension E of the ell-adic field.
Source: blueprint main-20261015, sk-thm-sf-pf-field-localizing, both paragraphs
(blueprint: det-thm-sf-pf-field-localizing).

Proof:
1. The standing separated finite-type schemes are qcqs. By
   det-def-localizing-closure-ctf-equals-bc the rational Dctf and Dbc categories and their
   localizing closures coincide.
2. Apply det-proper-base-change-unbounded-pullback and det-proper-image-localizing-proper.
   Both restricted functors are exact and preserve sums. Tensor closure from
   det-thm-sf-pf-field-tensor puts both endpoints in the target localizing category.
3. The closed tensor structure of sk-def-sfb-derived-tensor-hom makes tensor preserve sums;
   its exactness follows from lem-weil-pbc-ringed-projection-mate-exact.
4. By def-sfb-module-upper-star and sk-prop-sfb-cartesian-coefficients, module pullback is
   the exact inverse image, hence its total left derived functor is p*.
5. The projection map is the counit mate of the canonical tensor comparison. Use
   lem-weil-pbc-ringed-projection-mate-exact for its naturality and tensor shift compatibility.
6. The canonical adjoint shifts of lem-weil-pbc-adjunction-shift-compatibility-unique make
   the counit commute with shifts. Apply lem-sf-triangulated-right-adjoint for exactness of R.
7. These counit and comparison shift equations make the canonical mate commute with shifts
   in each variable and give the connecting square on distinguished triangles.
8. det-thm-sfb-proper-base-change-rational gives invertibility for bounded constructible A,B.
9. Fix bounded B and apply sk-lem-sf-determination to the two exact sum-preserving functors
   of A, giving invertibility for arbitrary A in Loc(Dbc).
10. Fix this arbitrary A and apply the same determination lemma in B. Since the localizing
    category is full and both endpoints belong to it, this is invertibility there.
-/
theorem isIso_projectionMate_localizing_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj
          (A ⊗ (upperStar (Profinite.continuousCoefficientRingObj E) p).leftDerivedFunctor.obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.continuousCoefficientRingObj E) p A B) := sorry

/-- Proper projection formula on Loc(Dbc) for finite-subextension-valued condensed Qlbar.
Source: blueprint main-20261015, sk-thm-sf-pf-field-localizing, both paragraphs
(blueprint: det-thm-sf-pf-field-localizing).

Proof:
1. Use the standing qcqs hypotheses and det-def-localizing-closure-ctf-equals-bc to identify
   Dctf, Dbc and their localizing closures for Qlbar.
2. det-proper-base-change-unbounded-pullback and det-proper-image-localizing-proper restrict
   p* and Rp* to exact sum-preserving functors; det-thm-sf-pf-field-tensor gives membership
   of both endpoints in the target localizing category.
3. The closed structure sk-def-sfb-derived-tensor-hom gives tensor preservation of sums;
   lem-weil-pbc-ringed-projection-mate-exact gives exactness in both variables.
4. def-sfb-module-upper-star and sk-prop-sfb-cartesian-coefficients identify Lp* with p*.
5. Use the normalized canonical tensor comparison and its counit mate as supplied by
   lem-weil-pbc-ringed-projection-mate-exact, natural in both variables.
6. lem-weil-pbc-adjunction-shift-compatibility-unique gives the counit-compatible adjoint
   shifts, and lem-sf-triangulated-right-adjoint supplies exactness of Rp* for these shifts.
7. The comparison and counit shift identities make the mate compatible with shifts in both
   variables and give its connecting square on distinguished triangles.
8. det-thm-sfb-proper-base-change-rational gives invertibility on bounded constructible A,B.
9. For bounded B, apply sk-lem-sf-determination in A to obtain all A in Loc(Dbc).
10. Fix arbitrary A and apply determination in B, giving all B in Loc(Dbc). Fullness and
    the membership of both endpoints give the asserted isomorphism in Loc(Dbc).
-/
theorem isIso_projectionMate_localizing_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (A ⊗ (upperStar (Profinite.padicAlgClRingObj ℓ) p).leftDerivedFunctor.obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.padicAlgClRingObj ℓ) p A B) := sorry

end AlgebraicGeometry.ProEtale.CondensedRing
