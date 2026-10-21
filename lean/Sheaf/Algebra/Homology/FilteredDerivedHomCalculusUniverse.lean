/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
import Sheaf.Algebra.Homology.ExactFilteredCoefficientChange
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Filtered global Hom in a common larger coefficient universe

Source: Varshavsky, §§5.1.2 and 5.1.5
(blueprint: lem-trf-filtered-derived-hom-calculus).

The original localizations and truncation calculus are retained. The coefficient
universe may be enlarged independently, so two abelian categories can share Ab.
-/

@[expose] public section

set_option autoImplicit false

universe s v u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated Opposite

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{max u v} A]
variable [HasDerivedCategory.{(max s (max u v)) + 1}
  AddCommGrpCat.{max s (max u v)}]

/-- The global Hom part of the filtered calculus. Its comparisons are natural in both
variables. A bilimit bicone states the finite direct sum without choosing arbitrary
filtration bounds or an order on its support.
Source: Varshavsky, 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
structure GlobalHomCalculusIn [TriangulatedLocalization A true]
    [TriangulatedLocalization AddCommGrpCat.{max s (max u v)} false]
    (B : TruncationCalculus A true)
    (C : TruncationCalculus AddCommGrpCat.{max s (max u v)} false) where
  omegaBounded : Derived (A := A) true ⥤ BoundedDerived A
  omegaBoundedComparison : omegaBounded ⋙ ObjectProperty.ι _ ≅ B.omega
  grBounded : ℤ → Derived (A := A) true ⥤ BoundedDerived A
  grBoundedComparison : ∀ a : ℤ, grBounded a ⋙ ObjectProperty.ι _ ≅ B.gr a
  ordinaryHom : (BoundedDerived A)ᵒᵖ ⥤ BoundedDerived A ⥤
    DerivedCategory AddCommGrpCat.{max s (max u v)}
  cohomology : ∀ (P Q : BoundedDerived A) (n : ℤ),
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
      ((ordinaryHom.obj (op P)).obj Q)) ≃+ (P.obj ⟶ Q.obj⟦n⟧)
  cohomology_source : ∀ (P P' Q : BoundedDerived A) (f : P' ⟶ P) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
      ((ordinaryHom.obj (op P)).obj Q)),
    cohomology P' Q n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).map
        ((ordinaryHom.map f.op).app Q) x) = f.hom ≫ cohomology P Q n x
  cohomology_target : ∀ (P Q Q' : BoundedDerived A) (f : Q ⟶ Q') (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
      ((ordinaryHom.obj (op P)).obj Q)),
    cohomology P Q' n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).map
        ((ordinaryHom.obj (op P)).map f) x) =
      cohomology P Q n x ≫ f.hom⟦n⟧'
  ordinary_model : ∀ (P Q : BoundedDerived A) (K I : CochainComplex A ℤ),
    DegreeBound A true K → DegreeBound A false I → (∀ n : ℤ, Injective (I.X n)) →
    Nonempty (DerivedCategory.Q.obj K ≅ P.obj) →
    Nonempty (DerivedCategory.Q.obj I ≅ Q.obj) →
    Nonempty ((ordinaryHom.obj (op P)).obj Q ≅ DerivedCategory.Q.obj
      ((AddCommGrpCat.uliftFunctor.{max s u, v}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomComplex K I)))
  filteredHom : (Derived (A := A) true)ᵒᵖ ⥤ Derived (A := A) true ⥤
    Derived (A := AddCommGrpCat.{max s (max u v)}) false
  underlyingComparison : ∀ P : Derived (A := A) true,
    filteredHom.obj (op P) ⋙ C.omega ≅
      omegaBounded ⋙ ordinaryHom.obj (op (omegaBounded.obj P))
  underlying_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    C.omega.map ((filteredHom.map f.op).app Q) ≫
        (underlyingComparison P').hom.app Q =
      (underlyingComparison P).hom.app Q ≫
        (ordinaryHom.map (omegaBounded.map f).op).app (omegaBounded.obj Q)
  gradedSum : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    Bicone (fun a : ℤ =>
      (ordinaryHom.obj (op ((grBounded a).obj P))).obj ((grBounded (a + r)).obj Q))
  gradedSum_isBilimit : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (gradedSum r P Q).IsBilimit
  finite_support : ∀ (r : ℤ) (P Q : Derived (A := A) true), ∃ S : Finset ℤ,
    ∀ a : ℤ, a ∉ S →
      IsZero ((ordinaryHom.obj (op ((grBounded a).obj P))).obj ((grBounded (a + r)).obj Q))
  gradedComparison : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (C.gr r).obj ((filteredHom.obj (op P)).obj Q) ≅ (gradedSum r P Q).pt
  graded_source : ∀ (r a : ℤ) (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    (C.gr r).map ((filteredHom.map f.op).app Q) ≫
        (gradedComparison r P' Q).hom ≫ (gradedSum r P' Q).π a =
      (gradedComparison r P Q).hom ≫ (gradedSum r P Q).π a ≫
        (ordinaryHom.map ((grBounded a).map f).op).app ((grBounded (a + r)).obj Q)
  graded_target : ∀ (r a : ℤ) (P Q Q' : Derived (A := A) true) (f : Q ⟶ Q'),
    (C.gr r).map ((filteredHom.obj (op P)).map f) ≫
        (gradedComparison r P Q').hom ≫ (gradedSum r P Q').π a =
      (gradedComparison r P Q).hom ≫ (gradedSum r P Q).π a ≫
        (ordinaryHom.obj (op ((grBounded a).obj P))).map ((grBounded (a + r)).map f)
  homEquiv : ∀ P Q : Derived (A := A) true,
    (P ⟶ Q) ≃+ (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).obj
      (C.omega.obj ((C.high 0).obj ((filteredHom.obj (op P)).obj Q)))
  homEquiv_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P) (g : P ⟶ Q),
    homEquiv P' Q (f ≫ g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).map
        (C.omega.map ((C.high 0).map ((filteredHom.map f.op).app Q))) (homEquiv P Q g)
  homEquiv_target : ∀ (P Q Q' : Derived (A := A) true) (f : Q ⟶ Q') (g : P ⟶ Q),
    homEquiv P Q' (g ≫ f) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).map
        (C.omega.map ((C.high 0).map ((filteredHom.obj (op P)).map f))) (homEquiv P Q g)
  forgetful_map : ∀ (P Q : Derived (A := A) true) (f : P ⟶ Q),
    cohomology (omegaBounded.obj P) (omegaBounded.obj Q) 0
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).map
        (C.omega.map ((C.inclusion 0).app ((filteredHom.obj (op P)).obj Q)) ≫
          (underlyingComparison P).hom.app Q) (homEquiv P Q f)) ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app (omegaBounded.obj Q).obj =
        omegaBoundedComparison.hom.app P ≫ B.omega.map f ≫
          omegaBoundedComparison.inv.app Q
  graded_projection : ∀ (a : ℤ) (P Q : Derived (A := A) true) (f : P ⟶ Q),
    cohomology ((grBounded a).obj P) ((grBounded a).obj Q) 0
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).map
        (C.gradeProjection.app ((filteredHom.obj (op P)).obj Q) ≫
          (gradedComparison 0 P Q).hom ≫ (gradedSum 0 P Q).π a ≫
            (ordinaryHom.obj (op ((grBounded a).obj P))).map
              (eqToHom (congrArg (fun b : ℤ => (grBounded b).obj Q) (Int.add_zero a))))
        (homEquiv P Q f)) ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app ((grBounded a).obj Q).obj =
        (grBoundedComparison a).hom.app P ≫ (B.gr a).map f ≫
          (grBoundedComparison a).inv.app Q

/-- All three cone-normalized triangulations and the bounded/plus truncation and global
Hom calculi, kept as existential data until the theorem is proved.
Source: Varshavsky, §§5.1.2 and 5.1.5
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
structure DerivedHomCalculusIn where
  boundedModel : TriangulatedLocalization A true
  plusModel : TriangulatedLocalization A false
  abelianPlusModel : TriangulatedLocalization AddCommGrpCat.{max s (max u v)} false
  bounded : @TruncationCalculus A _ _ _ true boundedModel
  plus : @TruncationCalculus A _ _ _ false plusModel
  abelianPlus : @TruncationCalculus AddCommGrpCat.{max s (max u v)} _ _ _ false abelianPlusModel
  globalHom : @GlobalHomCalculusIn.{s, v, u} A _ _ _ _
    boundedModel abelianPlusModel bounded abelianPlus

section CoefficientTransport

variable {A}
open CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe t

private noncomputable def liftHomologyIso
    [HasDerivedCategory.{t + 1} AddCommGrpCat.{t}]
    [HasDerivedCategory.{(max s t) + 1} AddCommGrpCat.{max s t}]
(n : ℤ) :
    (AddCommGrpCat.uliftFunctor.{s, t}).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙ AddCommGrpCat.uliftFunctor.{s, t} := by
  let U := AddCommGrpCat.uliftFunctor.{s, t}
  let e : U.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ _ n ≅
      HomologicalComplex.homologyFunctor _ _ n ⋙ U :=
    NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso U)
      (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map f) U)
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) AddCommGrpCat).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight U.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors _ n) ≪≫
    e ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ n).symm U ≪≫
    Functor.associator _ _ _

section

omit [HasDerivedCategory.{(max s (max u v)) + 1} AddCommGrpCat.{max s (max u v)}]
variable [HasDerivedCategory.{t + 1} AddCommGrpCat.{t}]
variable [HasDerivedCategory.{(max s t) + 1} AddCommGrpCat.{max s t}]
variable [TriangulatedLocalization AddCommGrpCat.{t} false]
variable [TriangulatedLocalization AddCommGrpCat.{max s t} false]
variable {S : TruncationCalculus AddCommGrpCat.{t} false}
variable {T : TruncationCalculus AddCommGrpCat.{max s t} false}
private noncomputable def highHomologyIso
    (E : ExactFilteredCoefficientChangeData.{t, max s t, t + 1, (max s t) + 1}
      AddCommGrpCat.uliftFunctor.{s, t} S T) :
    S.high 0 ⋙ S.omega ⋙ (DerivedCategory.homologyFunctor _ 0 ⋙
      AddCommGrpCat.uliftFunctor.{s, t}) ≅
    E.lift ⋙ T.high 0 ⋙ (T.omega ⋙ DerivedCategory.homologyFunctor _ 0) :=
  isoWhiskerLeft (S.high 0) (isoWhiskerLeft S.omega (liftHomologyIso.{s, t} 0).symm) ≪≫
    isoWhiskerLeft (S.high 0)
      (associator S.omega AddCommGrpCat.uliftFunctor.{s, t}.mapDerivedCategory _).symm ≪≫
    (associator (S.high 0)
      (S.omega ⋙ AddCommGrpCat.uliftFunctor.{s, t}.mapDerivedCategory) _).symm ≪≫
    isoWhiskerRight E.highOmega _ ≪≫
    associator E.lift (T.high 0 ⋙ T.omega) _ ≪≫
    isoWhiskerLeft E.lift (associator (T.high 0) T.omega _)

private lemma highHomology_square
    (E : ExactFilteredCoefficientChangeData.{t, max s t, t + 1, (max s t) + 1}
      AddCommGrpCat.uliftFunctor.{s, t} S T) (X : Derived (A := AddCommGrpCat.{t}) false)
    (Y : DerivedCategory AddCommGrpCat.{t})
    (a : T.omega.obj ((T.high 0).obj (E.lift.obj X)) ⟶
      AddCommGrpCat.uliftFunctor.{s, t}.mapDerivedCategory.obj Y)
    (g : S.omega.obj ((S.high 0).obj X) ⟶ Y)
    (ha : E.highOmega.hom.app X ≫ a = AddCommGrpCat.uliftFunctor.{s, t}.mapDerivedCategory.map g) :
    (highHomologyIso E).hom.app X ≫ (DerivedCategory.homologyFunctor _ 0).map a ≫
        (liftHomologyIso.{s, t} 0).hom.app Y =
      AddCommGrpCat.uliftFunctor.{s, t}.map ((DerivedCategory.homologyFunctor _ 0).map g) := by
  change (liftHomologyIso.{s, t} 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor _ 0).map (E.highOmega.hom.app X) ≫
      (DerivedCategory.homologyFunctor _ 0).map a ≫
      (liftHomologyIso.{s, t} 0).hom.app Y = _
  have h := (liftHomologyIso.{s, t} 0).hom.naturality g
  dsimp only [Functor.comp_map] at h
  rw [← Functor.map_comp_assoc, ha, h]
  simp

end

variable [HasDerivedCategory.{(max u v) + 1} AddCommGrpCat.{max u v}]
variable [TriangulatedLocalization A true]
variable [TriangulatedLocalization AddCommGrpCat.{max u v} false]
variable {B : TruncationCalculus A true}
variable {C : TruncationCalculus AddCommGrpCat.{max u v} false}
variable (G : GlobalHomCalculus A B C)
private noncomputable def enlargedOrdinary : (BoundedDerived A)ᵒᵖ ⥤ BoundedDerived A ⥤
    DerivedCategory AddCommGrpCat.{max s (max u v)} :=
  G.ordinaryHom ⋙
    (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory

private noncomputable def enlargedCohomology (P Q : BoundedDerived A) (n : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
        (((enlargedOrdinary.{s, v, u} G).obj (op P)).obj Q) ≃+
      (P.obj ⟶ Q.obj⟦n⟧) :=
  (((liftHomologyIso.{s, max u v} n).app
    ((G.ordinaryHom.obj (op P)).obj Q)).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift).trans (G.cohomology P Q n)

private lemma enlargedCohomology_source (P P' Q : BoundedDerived A) (f : P' ⟶ P) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
      (((enlargedOrdinary.{s, v, u} G).obj (op P)).obj Q)) :
    enlargedCohomology.{s, v, u} G P' Q n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).map
        (((enlargedOrdinary.{s, v, u} G).map f.op).app Q) x) =
      f.hom ≫ enlargedCohomology.{s, v, u} G P Q n x := by
  have h := ConcreteCategory.congr_hom
    ((liftHomologyIso.{s, max u v} n).hom.naturality
      ((G.ordinaryHom.map f.op).app Q)) x
  dsimp only [enlargedCohomology, AddEquiv.trans_apply]
  change G.cohomology P' Q n _ = f.hom ≫ G.cohomology P Q n _
  rw [← G.cohomology_source P P' Q f n]
  congr 1
  exact congrArg ULift.down h

private lemma enlargedCohomology_target (P Q Q' : BoundedDerived A) (f : Q ⟶ Q') (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).obj
      (((enlargedOrdinary.{s, v, u} G).obj (op P)).obj Q)) :
    enlargedCohomology.{s, v, u} G P Q' n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} n).map
        (((enlargedOrdinary.{s, v, u} G).obj (op P)).map f) x) =
      enlargedCohomology.{s, v, u} G P Q n x ≫ f.hom⟦n⟧' := by
  have h := ConcreteCategory.congr_hom
    ((liftHomologyIso.{s, max u v} n).hom.naturality
      ((G.ordinaryHom.obj (op P)).map f)) x
  dsimp only [enlargedCohomology, AddEquiv.trans_apply]
  change G.cohomology P Q' n _ = G.cohomology P Q n _ ≫ f.hom⟦n⟧'
  rw [← G.cohomology_target P Q Q' f n]
  congr 1
  exact congrArg ULift.down h
private noncomputable def doubleLiftIso :
    AddCommGrpCat.uliftFunctor.{u, v} ⋙ AddCommGrpCat.uliftFunctor.{s, max u v} ≅
      AddCommGrpCat.uliftFunctor.{max s u, v} :=
  NatIso.ofComponents (fun X ↦
    ((AddEquiv.ulift.trans AddEquiv.ulift).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun f ↦ by ext x; rfl)

private lemma enlargedOrdinary_model (P Q : BoundedDerived A) (K I : CochainComplex A ℤ)
    (hK : DegreeBound A true K) (hI : DegreeBound A false I)
    (hInj : ∀ n : ℤ, Injective (I.X n))
    (eK : Nonempty (DerivedCategory.Q.obj K ≅ P.obj))
    (eI : Nonempty (DerivedCategory.Q.obj I ≅ Q.obj)) :
    Nonempty (((enlargedOrdinary.{s, v, u} G).obj (op P)).obj Q ≅
      DerivedCategory.Q.obj
        ((AddCommGrpCat.uliftFunctor.{max s u, v}.mapHomologicalComplex (.up ℤ)).obj
          (HomComplex K I))) := by
  obtain ⟨e⟩ := G.ordinary_model P Q K I hK hI hInj eK eI
  exact ⟨AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.mapIso e ≪≫
    AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso doubleLiftIso.{s, v, u} (.up ℤ)).app
          (HomComplex K I))⟩

section
variable {X Y : Type*} [Category* X] [Category* Y]
  [Preadditive X] [Preadditive Y] [HasZeroObject X] [HasZeroObject Y]

private noncomputable def mapFiniteSupportBicone (F : X ⥤ Y) [F.Additive]
    {f : ℤ → X} (b : Bicone f) (hb : b.IsBilimit)
    (S : Finset ℤ) (hz : ∀ i, i ∉ S → IsZero (f i)) :
    (F.mapBicone b).IsBilimit := by
  classical
  let bS : Bicone (fun i : S ↦ f i) :=
    { pt := b.pt
      π i := b.π i
      ι i := b.ι i
      ι_π i j := by
        by_cases h : i = j
        · subst j; simp
        · have h' : (i : ℤ) ≠ j := fun h' ↦ h (Subtype.ext h')
          simp [h, bicone_ι_π_ne b h'] }
  have ht : ∑ i : S, bS.π i ≫ bS.ι i = 𝟙 bS.pt := by
    apply hb.isLimit.hom_ext
    rintro ⟨j⟩
    change (∑ i : S, b.π i ≫ b.ι i) ≫ b.π j = (𝟙 b.pt) ≫ b.π j
    by_cases hj : j ∈ S
    · let j' : S := ⟨j, hj⟩
      simp only [sum_comp, Category.assoc, Category.id_comp]
      rw [Finset.sum_eq_single j']
      · simp [j']
      · intro i _ hij
        have hi : (i : ℤ) ≠ j := fun hi ↦ hij (Subtype.ext hi)
        simp [bicone_ι_π_ne b hi]
      · simp
    · exact (hz j hj).eq_of_tgt _ _
  let hbS := isBilimitOfTotal bS ht
  let hF := isBilimitOfPreserves F hbS
  refine
    { isLimit :=
        { lift := fun t ↦ hF.isLimit.lift (Fan.mk t.pt (fun i : S ↦ t.π.app ⟨i⟩))
          fac := ?_
          uniq := ?_ }
      isColimit :=
        { desc := fun t ↦ hF.isColimit.desc (Cofan.mk t.pt (fun i : S ↦ t.ι.app ⟨i⟩))
          fac := ?_
          uniq := ?_ } }
  · intro t j
    by_cases hj : j.as ∈ S
    · exact hF.isLimit.fac _ ⟨⟨j.as, hj⟩⟩
    · exact (F.map_isZero (hz j.as hj)).eq_of_tgt _ _
  · intro t m hm
    apply hF.isLimit.hom_ext
    intro i
    exact (hm ⟨i.as⟩).trans (hF.isLimit.fac (Fan.mk t.pt (fun i : S ↦ t.π.app ⟨i⟩)) i).symm
  · intro t j
    by_cases hj : j.as ∈ S
    · exact hF.isColimit.fac _ ⟨⟨j.as, hj⟩⟩
    · exact (F.map_isZero (hz j.as hj)).eq_of_src _ _
  · intro t m hm
    apply hF.isColimit.hom_ext
    intro i
    exact (hm ⟨i.as⟩).trans (hF.isColimit.fac (Cofan.mk t.pt (fun i : S ↦ t.ι.app ⟨i⟩)) i).symm

end

variable [TriangulatedLocalization AddCommGrpCat.{max s (max u v)} false]
variable {T : TruncationCalculus AddCommGrpCat.{max s (max u v)} false}
private noncomputable def enlargedFiltered
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T) :
    (Derived (A := A) true)ᵒᵖ ⥤ Derived (A := A) true ⥤
      Derived (A := AddCommGrpCat.{max s (max u v)}) false :=
  G.filteredHom ⋙ (whiskeringRight _ _ _).obj E.lift

private noncomputable def enlargedUnderlying
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T) (P : Derived (A := A) true) :
    (enlargedFiltered.{s, v, u} G E).obj (op P) ⋙ T.omega ≅
      G.omegaBounded ⋙ (enlargedOrdinary.{s, v, u} G).obj (op (G.omegaBounded.obj P)) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ E.omega ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.underlyingComparison P)
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory ≪≫
      associator _ _ _

private noncomputable def enlargedGraded
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T) (r : ℤ) (P Q : Derived (A := A) true) :
    (T.gr r).obj (((enlargedFiltered.{s, v, u} G E).obj (op P)).obj Q) ≅
      (AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.mapBicone
        (G.gradedSum r P Q)).pt :=
  (E.gr r).app _ ≪≫ AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.mapIso
    (G.gradedComparison r P Q)

private noncomputable def enlargedHomEquiv
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T) (P Q : Derived (A := A) true) :
    (P ⟶ Q) ≃+ (DerivedCategory.homologyFunctor AddCommGrpCat.{max s (max u v)} 0).obj
      (T.omega.obj ((T.high 0).obj (((enlargedFiltered.{s, v, u} G E).obj (op P)).obj Q))) :=
  ((G.homEquiv P Q).trans AddEquiv.ulift.symm).trans
    (((highHomologyIso.{s, max u v} E).app
      ((G.filteredHom.obj (op P)).obj Q)).addCommGroupIsoToAddEquiv)

private lemma enlargedCohomology_transport
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T)
    (X : Derived (A := AddCommGrpCat.{max u v}) false) (P Q : BoundedDerived A)
    (a : T.omega.obj ((T.high 0).obj (E.lift.obj X)) ⟶
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.obj
        ((G.ordinaryHom.obj (op P)).obj Q))
    (g : C.omega.obj ((C.high 0).obj X) ⟶ (G.ordinaryHom.obj (op P)).obj Q)
    (ha : E.highOmega.hom.app X ≫ a =
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map g)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).obj
      (C.omega.obj ((C.high 0).obj X))) :
    enlargedCohomology.{s, v, u} G P Q 0
      ((DerivedCategory.homologyFunctor _ 0).map a
        ((highHomologyIso.{s, max u v} E).hom.app X (ULift.up x))) =
      G.cohomology P Q 0 ((DerivedCategory.homologyFunctor _ 0).map g x) := by
  have h := ConcreteCategory.congr_hom
    (highHomology_square.{s, max u v} E X _ a g ha) (ULift.up x)
  apply congrArg (G.cohomology P Q 0)
  exact congrArg ULift.down h

private noncomputable def enlargedGlobalHom
    (E : ExactFilteredCoefficientChangeData.{max u v, max s (max u v),
      (max u v) + 1, (max s (max u v)) + 1}
      AddCommGrpCat.uliftFunctor.{s, max u v} C T) : GlobalHomCalculusIn.{s, v, u} A B T where
  omegaBounded := G.omegaBounded
  omegaBoundedComparison := G.omegaBoundedComparison
  grBounded := G.grBounded
  grBoundedComparison := G.grBoundedComparison
  ordinaryHom := enlargedOrdinary.{s, v, u} G
  cohomology := enlargedCohomology.{s, v, u} G
  cohomology_source := enlargedCohomology_source.{s, v, u} G
  cohomology_target := enlargedCohomology_target.{s, v, u} G
  ordinary_model := enlargedOrdinary_model.{s, v, u} G
  filteredHom := enlargedFiltered.{s, v, u} G E
  underlyingComparison := enlargedUnderlying.{s, v, u} G E
  underlying_source P P' Q f := by
    have h := E.omega.hom.naturality ((G.filteredHom.map f.op).app Q)
    dsimp only [Functor.comp_map] at h
    dsimp [enlargedFiltered, enlargedUnderlying, enlargedOrdinary]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
      G.underlying_source, Functor.map_comp]
  gradedSum r P Q :=
    AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.mapBicone (G.gradedSum r P Q)
  gradedSum_isBilimit r P Q := by
    classical
    exact mapFiniteSupportBicone _ _ (G.gradedSum_isBilimit r P Q)
      (G.finite_support r P Q).choose (G.finite_support r P Q).choose_spec
  finite_support r P Q := by
    obtain ⟨S, hS⟩ := G.finite_support r P Q
    exact ⟨S, fun a ha ↦
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map_isZero (hS a ha)⟩
  gradedComparison := enlargedGraded.{s, v, u} G E
  graded_source r a P P' Q f := by
    have h := (E.gr r).hom.naturality ((G.filteredHom.map f.op).app Q)
    dsimp only [Functor.comp_map] at h
    dsimp [enlargedFiltered, enlargedGraded, enlargedOrdinary]
    simp only [← Category.assoc]
    rw [h]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ (E.gr r).hom.app _ ≫
        AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map k)
        (G.graded_source r a P P' Q f)
  graded_target r a P Q Q' f := by
    have h := (E.gr r).hom.naturality ((G.filteredHom.obj (op P)).map f)
    dsimp only [Functor.comp_map] at h
    dsimp [enlargedFiltered, enlargedGraded, enlargedOrdinary]
    simp only [← Category.assoc]
    rw [h]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ (E.gr r).hom.app _ ≫
        AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map k)
        (G.graded_target r a P Q Q' f)
  homEquiv := enlargedHomEquiv.{s, v, u} G E
  homEquiv_source P P' Q f g := by
    have h := ConcreteCategory.congr_hom
      ((highHomologyIso.{s, max u v} E).hom.naturality ((G.filteredHom.map f.op).app Q))
      (ULift.up (G.homEquiv P Q g))
    change (highHomologyIso.{s, max u v} E).hom.app _
      (ULift.up (G.homEquiv P' Q (f ≫ g))) = _
    rw [G.homEquiv_source]
    simpa [Functor.comp_map, AddCommGrpCat.comp_apply, enlargedHomEquiv,
      AddEquiv.ulift, AddCommGrpCat.uliftFunctor, Iso.addCommGroupIsoToAddEquiv,
      enlargedFiltered] using h
  homEquiv_target P Q Q' f g := by
    have h := ConcreteCategory.congr_hom
      ((highHomologyIso.{s, max u v} E).hom.naturality ((G.filteredHom.obj (op P)).map f))
      (ULift.up (G.homEquiv P Q g))
    change (highHomologyIso.{s, max u v} E).hom.app _
      (ULift.up (G.homEquiv P Q' (g ≫ f))) = _
    rw [G.homEquiv_target]
    simpa [Functor.comp_map, AddCommGrpCat.comp_apply, enlargedHomEquiv,
      AddEquiv.ulift, AddCommGrpCat.uliftFunctor, Iso.addCommGroupIsoToAddEquiv,
      enlargedFiltered] using h
  forgetful_map P Q f := by
    let X := (G.filteredHom.obj (op P)).obj Q
    let a := T.omega.map ((T.inclusion 0).app (E.lift.obj X)) ≫
      (enlargedUnderlying.{s, v, u} G E P).hom.app Q
    let g := C.omega.map ((C.inclusion 0).app X) ≫ (G.underlyingComparison P).hom.app Q
    have ha : E.highOmega.hom.app X ≫ a =
        AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map g := by
      dsimp [a, g, enlargedUnderlying, enlargedOrdinary, enlargedFiltered]
      simp only [Category.id_comp, Category.comp_id]
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ k ≫
          AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map
            ((G.underlyingComparison P).hom.app Q)) (E.inclusion X)
    have h := enlargedCohomology_transport.{s, v, u} G E X
      (G.omegaBounded.obj P) (G.omegaBounded.obj Q) a g ha (G.homEquiv P Q f)
    change enlargedCohomology.{s, v, u} G _ _ 0
      ((DerivedCategory.homologyFunctor _ 0).map a
        ((highHomologyIso.{s, max u v} E).hom.app X (ULift.up (G.homEquiv P Q f)))) ≫ _ = _
    exact (congrArg (fun z ↦ z ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app (G.omegaBounded.obj Q).obj) h).trans
        (G.forgetful_map P Q f)
  graded_projection a P Q f := by
    let X := (G.filteredHom.obj (op P)).obj Q
    let q := (G.ordinaryHom.obj (op ((G.grBounded a).obj P))).map
      (eqToHom (congrArg (fun b : ℤ ↦ (G.grBounded b).obj Q) (Int.add_zero a)))
    let k := T.gradeProjection.app (E.lift.obj X) ≫
      (enlargedGraded.{s, v, u} G E 0 P Q).hom ≫
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map ((G.gradedSum 0 P Q).π a) ≫
      AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map q
    let g := C.gradeProjection.app X ≫ (G.gradedComparison 0 P Q).hom ≫
      (G.gradedSum 0 P Q).π a ≫ q
    have hk : E.highOmega.hom.app X ≫ k =
        AddCommGrpCat.uliftFunctor.{s, max u v}.mapDerivedCategory.map g := by
      dsimp [k, g, enlargedGraded]
      simp only [← Category.assoc]
      have hh := E.projection X
      simp only [← Category.assoc] at hh
      rw [hh]
      simp only [Functor.map_comp, Category.assoc]
    have h := enlargedCohomology_transport.{s, v, u} G E X
      ((G.grBounded a).obj P) ((G.grBounded a).obj Q) k g hk (G.homEquiv P Q f)
    change enlargedCohomology.{s, v, u} G _ _ 0
      ((DerivedCategory.homologyFunctor _ 0).map k
        ((highHomologyIso.{s, max u v} E).hom.app X (ULift.up (G.homEquiv P Q f)))) ≫ _ = _
    exact (congrArg (fun z ↦ z ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app ((G.grBounded a).obj Q).obj) h).trans
        (G.graded_projection a P Q f)

end CoefficientTransport

/-- Filtered derived Hom, truncation triangles, their unique functoriality, and the
canonical forgetful and graded projection maps.
Source: Varshavsky, §§5.1.2(a)–(c), 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus).

Proof:
1. Take the established calculus with coefficients in Ab at max u v. For the larger
coefficient category, take its cone-normalized bounded-below localization and truncations
from the same base calculus applied to abelian groups.
2. The exact additive universe-lift functor on abelian groups induces the filtered derived
coefficient functor of exactFilteredCoefficientChange. Its normalized forgetful, graded,
and high-zero comparisons preserve both the actual inclusion and the quotient projection.
3. Postcompose ordinary global Hom and filtered global Hom with these coefficient functors.
The canonical homology comparison for the exact universe lift identifies each new
cohomology group with ULift of the old one. Combine it with ULift.down and the old additive
Hom equivalence. Naturality follows from the homology comparison. The double universe lift
of the ordinary Hom-complex model is canonically the required single lift.
4. Transport each finite-support graded bicone through the additive derived coefficient
functor. Restrict to its finite support, use preservation of finite biproducts, and extend
back over zero summands. This proves the graded decomposition including empty support.
5. For filtered morphisms, use the high-zero homology comparison followed by the old
Hom equivalence. Its naturality follows from that of the comparison. The two compatibility
squares from step 2 identify the cohomology of inclusion and grade-zero projection with
the old maps. Thus all fields have precisely the required enlarged coefficient universe;
the input localizations, boundedness conditions, and target statement are unchanged. -/
theorem filteredDerivedHomCalculusIn [EnoughInjectives A] :
    Nonempty (DerivedHomCalculusIn.{s, v, u} A) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{max u v}
  obtain ⟨D⟩ := filteredDerivedHomCalculus A
  let := HasDerivedCategory.standard AddCommGrpCat.{(max s (max u v)) + 1}
  obtain ⟨C⟩ := filteredDerivedHomCalculus AddCommGrpCat.{max s (max u v)}
  let := D.boundedModel
  let := D.abelianPlusModel
  let := C.plusModel
  obtain ⟨E⟩ := exactFilteredCoefficientChange.{max u v, max s (max u v), (max u v) + 1,
      (max s (max u v)) + 1}
    AddCommGrpCat.uliftFunctor.{s, max u v} D.abelianPlus C.plus
  exact ⟨{ boundedModel := D.boundedModel
           plusModel := D.plusModel
           abelianPlusModel := C.plusModel
           bounded := D.bounded
           plus := D.plus
           abelianPlus := C.plus
           globalHom := enlargedGlobalHom.{s, v, u} D.globalHom E }⟩

end CochainComplex.FiniteFiltered
