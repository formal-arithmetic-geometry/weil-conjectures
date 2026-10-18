-- Q80 stage-2 revalidation of the landed C3 repair.
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Sheaf.Algebra.Homology.FilteredHomComplexInvariance
import Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel
import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Exact-adjunction comparison for filtered derived global Hom

Source: Varshavsky, §§5.1.1–5.1.2 and §5.1.5
(blueprint: lem-trf-filtered-global-hom-exact-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CochainComplex.FiniteFiltered

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable (L : A ⥤ B) [L.Additive]
variable [hLlim : PreservesFiniteLimits L] [hLcolim : PreservesFiniteColimits L]

/-- Images of the termwise images of filtration steps decrease.
Source: Varshavsky, §5.1.1, exact functors on filtered objects.
Proof: map the inclusion of two successive steps and its factorization, then use
monotonicity of image subobjects.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_antitone (K : FilteredObject (CochainComplex A ℤ)) :
    Antitone (fun p : ℤ ↦ imageSubobject
      ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)) := by
  sorry

/-- Termwise L with the filtration by the images of L of the step inclusions.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredObject (K : FilteredObject (CochainComplex A ℤ)) :
    FilteredObject (CochainComplex B ℤ) where
  obj := (L.mapHomologicalComplex (.up ℤ)).obj K.obj
  filtration :=
    { F := fun p ↦ imageSubobject
        ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)
      F_succ_le := fun p ↦ exactFiltered_antitone L K (by omega) }

/-- Termwise exact application preserves finite filtration and cochain bounds.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: L sends the whole step to the whole image and the zero step to zero.
Additivity preserves zero terms, hence the same cochain degree bounds.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_bounds (bounded : Bool) (K : Complex A bounded) :
    (exactFilteredObject L K.obj).filtration.IsFinite ∧
      DegreeBound B bounded (exactFilteredObject L K.obj).obj := by
  sorry

/-- Applying L to a filtered map preserves the image filtration.
Source: Varshavsky, §5.1.1.
Proof: map the restriction square of the original filtered map and descend through
its image factorizations. The resulting factorization is unique by monicity.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_preserves (bounded : Bool) {K M : Complex A bounded} (f : K ⟶ M) :
    ∀ p : ℤ, ∃ l : ((exactFilteredObject L K.obj).filtration.step p : CochainComplex B ℤ) ⟶
      ((exactFilteredObject L M.obj).filtration.step p : CochainComplex B ℤ),
      l ≫ ((exactFilteredObject L M.obj).filtration.step p).arrow =
        ((exactFilteredObject L K.obj).filtration.step p).arrow ≫
          (L.mapHomologicalComplex (.up ℤ)).map f.hom.hom := by
  sorry

/-- The actual termwise functor on uniformly finite filtered complexes.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredComplex (bounded : Bool) :
    Complex A bounded ⥤ Complex B bounded where
  obj K := ⟨exactFilteredObject L K.obj, exactFiltered_bounds L bounded K⟩
  map f := ⟨⟨(L.mapHomologicalComplex (.up ℤ)).map f.hom.hom,
    exactFiltered_preserves L bounded f⟩⟩
  map_id K := by
    apply ObjectProperty.hom_ext
    change FilteredObject.HomPreservingSteps.mk _ _ =
      FilteredObject.HomPreservingSteps.mk _ _
    congr 1
    exact (L.mapHomologicalComplex (.up ℤ)).map_id K.obj.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change FilteredObject.HomPreservingSteps.mk _ _ =
      FilteredObject.HomPreservingSteps.mk _ _
    congr 1
    exact (L.mapHomologicalComplex (.up ℤ)).map_comp f.hom.hom g.hom.hom

include hLlim hLcolim in
/-- Exact termwise application preserves graded quasi-isomorphisms and therefore
inverts them after the target localization.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: exactness identifies each cokernel of consecutive mapped steps with L of
the original graded complex. Exact L preserves quasi-isomorphisms; target Q inverts
these maps by its localization property.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_inverts (bounded : Bool) :
    (∀ (K M : Complex A bounded) (f : K ⟶ M), quasiIso bounded f →
      quasiIso bounded ((exactFilteredComplex L bounded).map f)) ∧
    (quasiIso (A := A) bounded).IsInvertedBy
      (exactFilteredComplex L bounded ⋙ Q bounded) := by
  sorry

/-- L^F is the localization lift of the actual termwise filtered functor.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredDerived (bounded : Bool) :
    Derived (A := A) bounded ⥤ Derived (A := B) bounded :=
  Localization.lift (exactFilteredComplex L bounded ⋙ Q bounded)
    (exactFiltered_inverts L bounded).2 (Q bounded)

/-- The localization comparison fixes L^F on all filtered representatives.
Source: Varshavsky, §5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredDerivedQ (bounded : Bool) :
    Q bounded ⋙ exactFilteredDerived L bounded ≅ exactFilteredComplex L bounded ⋙ Q bounded :=
  Localization.fac (exactFilteredComplex L bounded ⋙ Q bounded)
    (exactFiltered_inverts L bounded).2 (Q bounded)

include hLlim hLcolim in
/-- Exactness gives the canonical graded quotient comparison, uniquely characterized
by the quotient projection square.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: L preserves the monic inclusions and their cokernels. Identify their sources
with their image subobjects and descend the mapped quotient projection. The descended
map is invertible by preservation of cokernels; the epimorphic projection gives uniqueness.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_graded_iso (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    ∃! e : (exactFilteredObject L K).filtration.gradedPiece p ≅
        (L.mapHomologicalComplex (.up ℤ)).obj (K.filtration.gradedPiece p),
      (L.mapHomologicalComplex (.up ℤ)).map
          (K.filtration.complexQuotientπ p (p + 1) (by omega)) ≫ e.inv =
        factorThruImageSubobject
            ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow) ≫
          (exactFilteredObject L K).filtration.complexQuotientπ p (p + 1) (by omega) := by
  sorry

/-- The quotient comparison selected from its unique universal-property characterization.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredGrIso (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (exactFilteredObject L K).filtration.gradedPiece p ≅
      (L.mapHomologicalComplex (.up ℤ)).obj (K.filtration.gradedPiece p) :=
  (exactFiltered_graded_iso L K p).exists.choose

variable [HasDerivedCategory.{max u₁ v₁} A] [HasDerivedCategory.{max u₂ v₂} B]
variable [HasDerivedCategory.{(max (max u₁ v₁) (max u₂ v₂)) + 1}
  AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)}]
variable [TriangulatedLocalization A true] [TriangulatedLocalization B true]
variable [TriangulatedLocalization AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} false]
variable (TA : TruncationCalculus A true) (TB : TruncationCalculus B true)
variable (C : TruncationCalculus AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} false)
variable
  (GA : GlobalHomCalculusIn.{max (max u₁ v₁) (max u₂ v₂), v₁, u₁} A TA C)
  (GB : GlobalHomCalculusIn.{max (max u₁ v₁) (max u₂ v₂), v₂, u₂} B TB C)

/-- Comparison data for the constructed L^F, with representative-normalized omega/gr
comparisons and ordinary and graded maps pinned on all cohomology groups to L.mapDerivedCategory.
Source: Varshavsky, §§5.1.2 and 5.1.5
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
structure FilteredGlobalHomExactAdjunctionData where
  omega : exactFilteredDerived L true ⋙ TB.omega ≅ TA.omega ⋙ L.mapDerivedCategory
  omega_normalization : ∀ K : Complex A true,
    omega.hom.app ((Q true).obj K) =
      TB.omega.map ((exactFilteredDerivedQ L true).hom.app K) ≫
        TB.omegaComparison.hom.app ((exactFilteredComplex L true).obj K) ≫
          L.mapDerivedCategoryFactors.inv.app K.obj.obj ≫
            L.mapDerivedCategory.map (TA.omegaComparison.inv.app K)
  gr : ∀ p : ℤ, exactFilteredDerived L true ⋙ TB.gr p ≅ TA.gr p ⋙ L.mapDerivedCategory
  gr_normalization : ∀ (p : ℤ) (K : Complex A true),
    (gr p).hom.app ((Q true).obj K) =
      (TB.gr p).map ((exactFilteredDerivedQ L true).hom.app K) ≫
        (TB.grComparison p).hom.app ((exactFilteredComplex L true).obj K) ≫
          DerivedCategory.Q.map (exactFilteredGrIso L K.obj p).hom ≫
            L.mapDerivedCategoryFactors.inv.app (K.obj.filtration.gradedPiece p) ≫
              L.mapDerivedCategory.map ((TA.grComparison p).inv.app K)
  c : ∀ P Q : Derived (A := A) true,
    (GA.filteredHom.obj (op P)).obj Q ≅
      (GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj ((exactFilteredDerived L
        true).obj Q)
  natural_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    (GA.filteredHom.map f.op).app Q ≫ (c P' Q).hom =
      (c P Q).hom ≫ (GB.filteredHom.map ((exactFilteredDerived L true).map f).op).app
        ((exactFilteredDerived L true).obj Q)
  natural_target : ∀ (P Q Q' : Derived (A := A) true) (g : Q ⟶ Q'),
    (GA.filteredHom.obj (op P)).map g ≫ (c P Q').hom =
      (c P Q).hom ≫ (GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).map
        ((exactFilteredDerived L true).map g)
  ordinary : ∀ (P Q : Derived (A := A) true),
    (GA.ordinaryHom.obj (op (GA.omegaBounded.obj P))).obj (GA.omegaBounded.obj Q) ⟶
      (GB.ordinaryHom.obj (op (GB.omegaBounded.obj ((exactFilteredDerived L true).obj P)))).obj
        (GB.omegaBounded.obj ((exactFilteredDerived L true).obj Q))
  ordinary_cohomology : ∀ (P Q : Derived (A := A) true) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor
      AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).obj
        ((GA.ordinaryHom.obj (op (GA.omegaBounded.obj P))).obj (GA.omegaBounded.obj Q))),
    GB.cohomology (GB.omegaBounded.obj ((exactFilteredDerived L true).obj P))
      (GB.omegaBounded.obj ((exactFilteredDerived L true).obj Q)) n
      ((DerivedCategory.homologyFunctor
        AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).map (ordinary P Q) x) =
      (GB.omegaBoundedComparison.hom.app ((exactFilteredDerived L true).obj P) ≫
        omega.hom.app P ≫ L.mapDerivedCategory.map (GA.omegaBoundedComparison.inv.app P)) ≫
      L.mapDerivedCategory.map (GA.cohomology (GA.omegaBounded.obj P)
        (GA.omegaBounded.obj Q) n x) ≫
      (L.mapDerivedCategory.commShiftIso n).hom.app (GA.omegaBounded.obj Q).obj ≫
      (L.mapDerivedCategory.map (GA.omegaBoundedComparison.hom.app Q) ≫
        omega.inv.app Q ≫
        GB.omegaBoundedComparison.inv.app ((exactFilteredDerived L true).obj Q))⟦n⟧'
  underlying : ∀ (P Q : Derived (A := A) true),
    C.omega.map ((c P Q).hom) ≫
        (GB.underlyingComparison ((exactFilteredDerived L true).obj P)).hom.app
          ((exactFilteredDerived L true).obj Q) =
      (GA.underlyingComparison P).hom.app Q ≫ ordinary P Q
  gradedTerm : ∀ (r a : ℤ) (P Q : Derived (A := A) true),
    (GA.ordinaryHom.obj (op ((GA.grBounded a).obj P))).obj
          ((GA.grBounded (a + r)).obj Q) ⟶
      (GB.ordinaryHom.obj (op ((GB.grBounded a).obj ((exactFilteredDerived L true).obj P)))).obj
          ((GB.grBounded (a + r)).obj ((exactFilteredDerived L true).obj Q))
  gradedTerm_cohomology : ∀ (r a : ℤ) (P Q : Derived (A := A) true) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor
      AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).obj
        ((GA.ordinaryHom.obj (op ((GA.grBounded a).obj P))).obj
          ((GA.grBounded (a + r)).obj Q))),
    GB.cohomology ((GB.grBounded a).obj ((exactFilteredDerived L true).obj P))
      ((GB.grBounded (a + r)).obj ((exactFilteredDerived L true).obj Q)) n
      ((DerivedCategory.homologyFunctor
        AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).map (gradedTerm r a P Q) x) =
      ((GB.grBoundedComparison a).hom.app ((exactFilteredDerived L true).obj P) ≫
        (gr a).hom.app P ≫
        L.mapDerivedCategory.map ((GA.grBoundedComparison a).inv.app P)) ≫
      L.mapDerivedCategory.map (GA.cohomology ((GA.grBounded a).obj P)
        ((GA.grBounded (a + r)).obj Q) n x) ≫
      (L.mapDerivedCategory.commShiftIso n).hom.app ((GA.grBounded (a + r)).obj Q).obj ≫
      (L.mapDerivedCategory.map ((GA.grBoundedComparison (a + r)).hom.app Q) ≫
        (gr (a + r)).inv.app Q ≫
        (GB.grBoundedComparison (a + r)).inv.app ((exactFilteredDerived L true).obj Q))⟦n⟧'
  gradedSum : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    ∃ m : (GA.gradedSum r P Q).pt ⟶
        (GB.gradedSum r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L true).obj
          Q)).pt,
      ∀ a : ℤ, m ≫ (GB.gradedSum r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L
        true).obj Q)).π a =
        (GA.gradedSum r P Q).π a ≫ gradedTerm r a P Q
  graded : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (C.gr r).map ((c P Q).hom) ≫
          (GB.gradedComparison r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L
            true).obj Q)).hom =
      (GA.gradedComparison r P Q).hom ≫ Classical.choose (gradedSum r P Q)
  morphism : ∀ (P Q : Derived (A := A) true) (f : P ⟶ Q),
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} 0).map
        (C.omega.map ((C.high 0).map ((c P Q).hom))) (GA.homEquiv P Q f) =
      GB.homEquiv ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L true).obj Q)
        ((exactFilteredDerived L true).map f)
  forgetful_and_grade_zero : ∀ (P Q : Derived (A := A) true),
    C.omega.map ((C.high 0).map ((c P Q).hom)) ≫
        (C.gradeProjection.app
          ((GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj
            ((exactFilteredDerived L true).obj Q))) =
      (C.gradeProjection.app ((GA.filteredHom.obj (op P)).obj Q)) ≫
        (C.gr 0).map ((c P Q).hom) ∧
    C.omega.map ((C.high 0).map ((c P Q).hom)) ≫
        C.omega.map ((C.inclusion 0).app
          ((GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj
            ((exactFilteredDerived L true).obj Q))) =
      C.omega.map ((C.inclusion 0).app ((GA.filteredHom.obj (op P)).obj Q)) ≫
        C.omega.map ((c P Q).hom)

/-- An exact adjunction with invertible bounded-below derived unit gives the
canonical filtered global-Hom comparison for the constructed termwise functor.
Source: Varshavsky, §5.1.5 (exact-adjunction calculation), §§5.1.1–5.1.2
(filtered localizations) (blueprint: lem-trf-filtered-global-hom-exact-adjunction).

Proof: Resolve L^F Q by a bounded-below termwise filtered-injective J. Exactness of L
and adjunction imply that R preserves injectives. Split the finite flags of J to
identify gr(RJ) with R(gr J). The unit followed by R of the resolution Q to RJ is a
graded quasi-isomorphism, since it represents the assumed derived unit on each grade.
Termwise adjunction identifies the shift-filtered Hom complexes Hom(P,RJ) and
Hom(LP,J), in both directions preserving their filtrations. Descend along the
filtered-injective model and Hom-complex invariance. Forgetting gives the ordinary
comparison, whose H^n map is L on derived morphisms. Grading gives the finite sum of
these comparisons. The counit triangle identity identifies the H^0 filtered-morphism
map with L^F.map. Respect for F^0 and F^1 gives the inclusion and quotient squares. -/
theorem filteredGlobalHomExactAdjunction
    [EnoughInjectives A] [EnoughInjectives B]
    {R : B ⥤ A} [R.Additive] (adj : L ⊣ R)
    [IsIso adj.derivedPlus.unit] :
    Nonempty (FilteredGlobalHomExactAdjunctionData L TA TB C GA GB) := by
  sorry

end CochainComplex.FiniteFiltered
