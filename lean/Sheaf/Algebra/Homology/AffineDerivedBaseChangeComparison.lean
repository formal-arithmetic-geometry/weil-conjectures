/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.Algebra.Homology.RingTensorCohomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Affine derived base change and localization

Source: Stacks Project, More on Algebra, equation comparison-map, and
`perfect.tex`, Tag 0DJ8, affine proof
(blueprint: lem-pc-affine-derived-base-change-comparison-map).

We use the functorial K-flat models of `RingTensorCohomology`. The comparison in the
derived category is specified by its K-flat span. Lifts of the cohomology functors to
modules over the tensor algebra specify the scalar actions explicitly. All localization
isomorphisms are natural transformations of functors on unbounded complexes.
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTensorCohomology

/-- Stacks, equation comparison-map and Tag 0DJ8, affine proof.
(blueprint: lem-pc-affine-derived-base-change-comparison-map)

The K-flat comparison span becomes a unique morphism in the derived category.
Its cohomology is the previously defined comparison. The last clause gives its value
on every pair of K-flat models P -> M and E -> P. The equations fixing `es,et` use the
resolution augmentations, so these are the canonical model identifications, not arbitrary
isomorphisms. No Tor independence is assumed.

Proof: choose the A-K-flat resolution P of M and the R-K-flat resolution E of
its restriction, using lem-pc-kflat-resolution on the one-point site. The span's
left map is inverted by derived scalar extension (lem-pur-derived-change-of-rings).
Its right map is E tensor R' -> P tensor R', identified with P tensor_A A'.
Consequently the localization of the span gives the displayed unique morphism.
The cohomology factorization is natural and preserves inverses, giving the last equation.
The universal property of derived scalar extension identifies this span with the map
computed using any K-flat models and gives independence of choices and naturality. -/
theorem exists_affineDerivedBaseChangeComparison
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [HasDerivedCategory.{w} (ModuleCat.{u} B)] :
    IsIso (Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q) ∧
    ∃! c : sourceComplex R A B ⋙ DerivedCategory.Q ⟶
        targetComplex R A B ⋙ DerivedCategory.Q,
      Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q ≫ c =
        Functor.whiskerRight (spanRight R A B) DerivedCategory.Q ∧
      (∀ i : ℤ,
        Functor.whiskerRight c (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) ≫
          (Functor.isoWhiskerLeft (targetComplex R A B)
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i)).hom =
        (Functor.isoWhiskerLeft (sourceComplex R A B)
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i)).hom ≫
          comparison R A B i) ∧
      ∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ)
        (E : CochainComplex (ModuleCat.{u} R) ℤ)
        (p : P ⟶ M) (e : E ⟶ (restrict R A).obj P),
        QuasiIso p → QuasiIso e →
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat E →
        ∃ (es : DerivedCategory.Q.obj ((extend R B).obj E) ≅
            DerivedCategory.Q.obj ((sourceComplex R A B).obj M))
          (et : DerivedCategory.Q.obj ((extend R B).obj ((restrict R A).obj P)) ≅
            DerivedCategory.Q.obj ((targetComplex R A B).obj M)),
          DerivedCategory.Q.map ((extend R B).map ((augmentation R).app E)) ≫ es.hom =
            DerivedCategory.Q.map ((extend R B).map ((resolution R).map
              (e ≫ (restrict R A).map p))) ∧
          DerivedCategory.Q.map ((extend R B).map
              ((restrict R A).map ((augmentation A).app P))) ≫ et.hom =
            DerivedCategory.Q.map ((targetComplex R A B).map p) ∧
          es.hom ≫ c.app M = DerivedCategory.Q.map ((extend R B).map e) ≫ et.hom := by
  sorry

/-- Stacks, Tag 0DJ8, affine proof, including the displayed localization identities.
(blueprint: lem-pc-affine-derived-base-change-comparison-map)

`S,T` are the two cohomology functors lifted to A tensor_R B modules, with
`eS,eT` identifying their restrictions with the existing B-module models. The two
scalar equations characterize both actions: a tensor 1 acts by multiplication on M,
and 1 tensor b acts by the existing B-action. The comparison `c` is tensor-algebra-linear
and restricts to the existing canonical comparison. The localized lifts `Sl,Tl` have
the same characterization. `alpha,beta` are the two natural D-linear localization
isomorphisms, and their square identifies the localized comparison with the local one.
The last isomorphism identifies the localized target with M_q tensor-derived_A_q D.

We quantify over models Rp,Aq,Bp,D of the four prime localizations. The scalar towers
and the two equations on `f` specify their canonical maps, rather than assuming
flatness or a base-change isomorphism. Left-sided tensors in extendScalars are the
right-sided tensors in the source by tensor symmetry.

Proof, following the DAG:
1. Choose K-flat A- and R-models as in exists_affineDerivedBaseChangeComparison;
   derived change of rings gives independence and naturality.
2. Multiplication on M induces the A-action on source cohomology. It commutes with B,
   and the two R-actions agree, so these give the A tensor_R B action. On the target
   this is the evident action on P tensor_A (A tensor_R B). Naturality of the comparison
   for multiplication by a makes it linear over the tensor algebra.
3. Apply lem-pc-derived-tensor-localization-cohomology to the source: localize its
   cohomology, not its R-K-flat complex. Localize P over A to Aq for the target;
   P_q is K-flat over Aq and represents M_q. The tensor-localization formula
   lem-weil-pbc-localization-tensor-product identifies its extension to D.
4. Exact localization (lem-weil-pbc-localization-module-exact) commutes with cohomology
   and gives beta and the final identification. All tensor identifications are natural;
   on K-flat models both paths in the square are the localized comparison map. -/
theorem exists_affineDerivedBaseChangeLocalization
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    ∃ (S T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        source R A B i)
      (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        target R A B i)
      (c : S ⟶ T),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M),
        eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (source R A B i).map (a • 𝟙 M) (eS.hom.app M x)) ∧
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
        eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (target R A B i).map (a • 𝟙 M) (eT.hom.app M x)) ∧
      Functor.whiskerRight c
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
        eS.hom ≫ comparison R A B i ∧
      ∀ (q' : PrimeSpectrum (A ⊗[R] B))
        (Rp Aq Bp D : Type u) [CommRing Rp] [CommRing Aq] [CommRing Bp] [CommRing D]
        [Algebra R Rp] [Algebra A Aq] [Algebra B Bp] [Algebra (A ⊗[R] B) D]
        [IsLocalization.AtPrime Rp (q'.asIdeal.comap (algebraMap R (A ⊗[R] B)))]
        [IsLocalization.AtPrime Aq (q'.asIdeal.comap (algebraMap A (A ⊗[R] B)))]
        [IsLocalization.AtPrime Bp (q'.asIdeal.comap
          Algebra.TensorProduct.includeRight.toRingHom)]
        [IsLocalization.AtPrime D q'.asIdeal]
        [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
        [IsScalarTower R A Aq] [IsScalarTower R B Bp]
        [IsScalarTower R Rp Aq] [IsScalarTower R Rp Bp]
        [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
        [IsScalarTower A (A ⊗[R] B) D]
        [IsScalarTower A Aq D]
        (_hB : ∀ b : B, algebraMap B D b =
          algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b))
        [IsScalarTower B Bp D]
        (f : (Aq ⊗[Rp] Bp) →+* D)
        (_hfA : ∀ a : Aq,
          f (Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) = algebraMap Aq D a)
        (_hfB : ∀ b : Bp, f (Algebra.TensorProduct.includeRight b) = algebraMap Bp D b),
        ∃ (Sl Tl : CochainComplex (ModuleCat.{u} Aq) ℤ ⥤
            ModuleCat.{u} (Aq ⊗[Rp] Bp))
          (eSl : Sl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            source Rp Aq Bp i)
          (eTl : Tl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            target Rp Aq Bp i)
          (cl : Sl ⟶ Tl),
          (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Sl.obj M),
            eSl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (source Rp Aq Bp i).map (a • 𝟙 M) (eSl.hom.app M x)) ∧
          (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Tl.obj M),
            eTl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (target Rp Aq Bp i).map (a • 𝟙 M) (eTl.hom.app M x)) ∧
          Functor.whiskerRight cl
              (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫
              eTl.hom = eSl.hom ≫ comparison Rp Aq Bp i ∧
          ∃ (alpha : S ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Sl ⋙ ModuleCat.extendScalars f)
            (beta : T ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Tl ⋙ ModuleCat.extendScalars f),
            Functor.whiskerRight c (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)) ≫
                beta.hom = alpha.hom ≫
              Functor.whiskerLeft (extend A Aq)
                (Functor.whiskerRight cl (ModuleCat.extendScalars f)) ∧
            Nonempty (Tl ⋙ ModuleCat.extendScalars f ≅
              resolution Aq ⋙ extend Aq D ⋙
                HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i) := by
  sorry

end RingTensorCohomology
