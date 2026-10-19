/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro

/-!
# Bounded above acyclic complexes compute a left derived functor

Source: Stacks Project, Derived Categories, Tags 0646, 06XN, 05S8, 05S9 and the
left-derived duals of Tags 015D and 015E
(blueprint: lem-trf-bounded-above-acyclic-derived-computation).

The resolution statement retains any specified upper bound. The computation statement
uses the canonical counit, its total-derived universal property, and essential constancy
of the homotopy-category denominator diagrams at every object. The latter is the defining
condition of `Functor.IsTriangulatedLeftDerivedDefinedAt`, expanded to avoid requiring a
separate hypothesis that the fixed quasi-isomorphism system is saturated triangulated.
Left acyclicity of an object is written directly as invertibility of the counit on its
complex in degree zero. All comparison morphisms are the displayed canonical composites.
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Bounded above projective resolutions with the prescribed upper bound.
Source: Stacks Project, Derived Categories, Tag 0646(3)
(blueprint: lem-trf-bounded-above-acyclic-derived-computation).

Proof (the first two steps of the node): Starting above `b` with zero, descend in degree.
At stage `n`, form the pullback of `X.X n` and the cycles of `P` in degree `n + 1`
over the cycles of `X` in degree `n + 1`. Enough projectives gives a projective
object mapping epimorphically to this pullback. Its components define the differential
and the augmentation. Their compatibility and the square-zero identity follow from
the pullback. The cycle map remains epic: lift the pair `(x, 0)` after epimorphic
refinement, using `lem-sp-abelian-refinements`. Hence the augmentation is surjective
on homology. If a cycle maps to a boundary, lift its compatible pair with that boundary
one degree lower, again after epimorphic refinement. It is itself a boundary. The
refinement criteria therefore make the homology maps monic as well as epic. This gives
a quasi-isomorphism, and the recursion leaves every term above `b` zero. -/
theorem exists_boundedAbove_projective_resolution
    (A : Type uA) [Category.{vA} A] [Abelian A] [EnoughProjectives A]
    (X : CochainComplex A ℤ) (b : ℤ) (hX : X.IsStrictlyLE b) :
    ∃ (P : CochainComplex A ℤ) (a : P ⟶ X),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso a := by
  sorry

/-- Projective and left-acyclic bounded above complexes compute the total left derived
functor, with the canonical resolution identification and its naturality.
Source: Stacks Project, Derived Categories, Tags 06XN, 05S8, 05S9 and the dual of Tag 015E
(blueprint: lem-trf-bounded-above-acyclic-derived-computation).

The four conjuncts respectively assert projective computation, acyclic computation,
invertibility of the specified resolution comparison, and its naturality. In diagrammatic
composition order the comparison is `inv (LV.map (Q.map a)) ≫ ε.app C`.
`IsLeftDerivedFunctor` specifies the universal counit, while `hdefined` retains the stronger
Stacks essential-constancy requirement, rather than just existence of a right Kan extension.

Proof (all seven steps of the node):
1. Construct the bounded above projective resolution by the preceding downward recursion.
2. The refinement argument in its docstring proves that the augmentation is a quasi-iso.
3. A bounded above complex of projectives is K-projective by
   `lem-sc-bounded-above-projective-kprojective`. The Hom bijection of
   `lem-coef-kprojective-derived-hom-bijection` lifts the inverse of every denominator
   `s : Y ⟶ P` to `t : P ⟶ Y` in the homotopy category. Injectivity gives `t ≫ s = 1`
   and compatibility for every triangle of denominators. Thus the identity denominator
   is initial. Its image cone witnesses essential constancy with identity retraction,
   so the canonical comparison at `P` is invertible by Tags 05S8 and 05S9.
4. Projective objects and zero are therefore left acyclic. The dual of Tag 015D,
   `lem-trf-left-acyclic-short-exact`, gives closure under finite sums and under kernels
   of epimorphisms between acyclic objects, with a short exact image sequence under `V`.
5. Resolve a bounded above termwise acyclic `C` by projectives. The augmentation cone
   is bounded above, acyclic and termwise left acyclic. Descending from its zero top
   cycle, apply the preceding short exact sequence assertion to its cycle sequences.
   Their images are short exact, so the image cone is acyclic. Additivity identifies
   it with the cone of the image augmentation. The cone criterion of
   `lem-pur-quasi-iso-cone-acyclic` makes that image augmentation a quasi-isomorphism.
6. Naturality of `ε` at the augmentation, projective computation, and inversion of both
   quasi-isomorphisms now give invertibility of `ε.app C`. For any quasi-isomorphism
   `a : C ⟶ X`, the displayed inverse followed by `ε.app C` is consequently invertible.
7. For `f ≫ a' = a ≫ h`, functoriality gives
   `LV(Q(f)) ≫ LV(Q(a')) = LV(Q(a)) ≫ LV(Q(h))`. Multiply by the inverse augmentation
   maps and use naturality of `ε` at `f` to obtain exactly the final equality below.
No injectivity, boundedness or invertibility assumption is imposed on `f` or `h`. -/
theorem boundedAbove_acyclic_leftDerived_computation
    (A : Type uA) (B : Type uB) [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [EnoughProjectives A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteColimits V]
    (LV : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ LV ⟶
      V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLV : LV.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory B, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙ Over.forget X ⋙
            V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y) :
    (∀ (P : CochainComplex A ℤ) (b : ℤ), P.IsStrictlyLE b →
      (∀ i : ℤ, Projective (P.X i)) → IsIso (ε.app P)) ∧
    (∀ (C : CochainComplex A ℤ) (b : ℤ), C.IsStrictlyLE b →
      (∀ i : ℤ, IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj (C.X i)))) →
        IsIso (ε.app C)) ∧
    (∀ (C X : CochainComplex A ℤ) (b : ℤ), C.IsStrictlyLE b →
      (∀ i : ℤ, IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj (C.X i)))) →
        ∀ (a : C ⟶ X) [QuasiIso a],
          IsIso (inv (LV.map (DerivedCategory.Q.map a)) ≫ ε.app C)) ∧
    (∀ (C C' X X' : CochainComplex A ℤ) (b b' : ℤ),
      C.IsStrictlyLE b → C'.IsStrictlyLE b' →
      (∀ i : ℤ, IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj (C.X i)))) →
      (∀ i : ℤ, IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj (C'.X i)))) →
        ∀ (a : C ⟶ X) (a' : C' ⟶ X') [QuasiIso a] [QuasiIso a']
          (f : C ⟶ C') (h : X ⟶ X'), f ≫ a' = a ≫ h →
            (inv (LV.map (DerivedCategory.Q.map a)) ≫ ε.app C) ≫
                DerivedCategory.Q.map ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
              LV.map (DerivedCategory.Q.map h) ≫
                (inv (LV.map (DerivedCategory.Q.map a')) ≫ ε.app C')) := by
  sorry

end CategoryTheory
