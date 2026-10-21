/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

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

/-- Filtered derived Hom, truncation triangles, their unique functoriality, and the
canonical forgetful and graded projection maps.
Source: Varshavsky, §§5.1.2(a)–(c), 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus).

Proof:
1. Filtered homotopies become equal in the localization: the filtered cylinder projection
is a graded quasi-isomorphism, so the two inclusions become equal. This identifies the
localizations of complexes and of their filtered homotopy category, using
lem-weil-pbc-localization-universal-property.
2. Use lem-trf-filtered-localization-injective-model and the fully faithful exact embedding
lem-trf-bounded-filtered-localization-embedding. Truncations, grades and forgetting commute
with shifts and cones on the injective model; they descend by the localization universal
property and preserve bounded inputs.
3. A finite filtered injective is a split flag of ordinary injectives, by downward splitting.
The cone-to-quotient map for the inclusion of a filtration step is a graded quasi-isomorphism.
This gives the actual inclusion/quotient distinguished triangle. For high L and low R every
filtered chain map L to R[q] vanishes. Thus all such derived Hom groups vanish. Apply
lem-weil-pbc-triangle-morphism-extension to obtain the unique comparison fixing the middle
object; reversing the comparison proves it is an isomorphism. Naturality follows from the
actual inclusion and quotient transformations.
4. For bounded P and a filtered injective resolution Q to I, take HomComplex P I with
F^r consisting of cochains carrying F^a P into F^{a+r} I for every a. The differential
preserves these subgroups. If P has grades [a,b] and I has grades [c,e], its filtration is
whole in degree c-b and zero in degree e-a+1. If P vanishes above v and I below w, its
cochain degrees vanish below w-v. The underlying Hom complex computes ordinary global
RHom: bounded-below injective complexes are K-injective, by
lem-weil-pbc-dplus-injective-representative and lem-weil-pbc-kinjective-hom-derived.
5. The canonical graded-cochain map has kernel F^{r+1}. For surjectivity split the target
flag, extend each map gr^a P to the appropriate injective target summand across
P/F^{a+1} P, and sum the finitely many extensions. It commutes with the Hom differential.
Consequently gr^r Hom is the direct sum of Hom(gr^a P,gr^{a+r} I), with the stated sign
of the filtration index. The splittings prove surjectivity only; the comparison is canonical.
6. Source homotopies induce S(f)=(-1)^n f h and target homotopies induce T(f)=k f.
They preserve filtration and satisfy dS+Sd=s*-t* and dT+Td=u*-v*. K-injectivity on every
grade inverts source quasi-isomorphisms; the injective-model equivalence supplies target
comparisons. Descend one variable at a time, obtaining a bifunctor and natural comparisons
independent of representatives. Its output is bounded below with uniformly finite filtration.
7. Degree-zero cycles of F^0 Hom are filtered chain maps; its boundaries are filtered
null-homotopies. The model theorem and bounded embedding give the natural Hom/H^0
isomorphism. Inclusion F^0 Hom into Hom forgets precisely the filtration condition, giving
the specified forgetful map. The quotient F^0 Hom to gr^0 Hom sends the same chain map to
its actual associated graded maps; inverting gr^a(Q to I) gives every stated projection
component gr^a P to gr^a Q. The truncation arguments apply
also to bounded-below complexes, without claiming bounded-below Hom for arbitrary plus
inputs. No finite injective dimension is assumed. -/
theorem filteredDerivedHomCalculusIn [EnoughInjectives A] :
    Nonempty (DerivedHomCalculusIn.{s, v, u} A) := by
  sorry

end CochainComplex.FiniteFiltered
