/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Algebra.Homology.FlatScalarRealization
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.FlatScalarRealizationExact
import Sheaf.Algebra.Homology.FlatScalarTensorResolution
/-! # Flat scalar realization commutes with Tor -/

@[expose] public section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject

namespace SheafOfModules

/-- Exact flat scalar realization carries ordinary module Tor to sheaf derived-tensor
cohomology. Positive cohomology is zero.

Source: Stacks Project, Modules on Sites, Tags 093J, 03ER and 03EK;
Cohomology on Sites, Tags 06YQ, 06YP and 06YU; Algebra, Tag 00LY
(blueprint: lem-sfb-flat-scalar-tor-comparison).

Proof: Compose exact constant module realization with extension along alpha. The
restriction of extension is tensoring with the underlying flat algebra, hence exact;
faithful exact restriction reflects exactness, so extension is exact as well. This
gives the additive exact functor F with the stated object function. Resolve P by
free scalar modules in nonpositive cochain degrees. Constant realization and flat
extension preserve its augmentation quasi-isomorphism. The resulting bounded-above
free sheaf complex is K-flat. It computes the sheaf derived tensor by 06YU; 06YP
allows the other factor to be the actual Q[0]. Balanced tensor associativity identifies
this tensor complex with F applied to the ordinary resolution tensored with Q.
Exact F commutes with homology. Reversing the nonnegative chain indices gives Tor'_n
in degree -n and zero in positive degrees.
All constructions work with arbitrary scalar modules, zero rings, and the empty site;
no DVR or finite-presentation hypothesis is used. -/
theorem flat_scalar_tor_comparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (α : realizationRing J A ⟶ R)
    (hflat : IsFlatOnSite (J := J) (R := realizationRing J A)
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map α)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) :
    ∀ (P Q : ModuleCat.{max u v} A) (i : ℤ),
        Nonempty ((DerivedCategory.homologyFunctor _ i).obj
          ((siteDerivedTensorIndependentCoefficients J R).obj
            ((DerivedCategory.singleFunctor _ 0).obj ((flatScalarRealization J α).obj P),
              (DerivedCategory.singleFunctor _ 0).obj ((flatScalarRealization J α).obj Q))) ≅
          if i ≤ 0 then (flatScalarRealization J α).obj
            (((Tor' (ModuleCat.{max u v} A) (-i).toNat).obj P).obj Q)
            else (0 : SheafOfModules.{max u v}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) := by
  classical
  let F := flatScalarRealization J α
  have := (flatScalarRealization_exact J α hflat).1
  have := (flatScalarRealization_exact J α hflat).2
  intro P Q i
  let K := ((MonoidalCategory.tensorRight Q).mapHomologicalComplex (.down ℕ)).obj
    (projectiveResolution P).complex
  let L := K.extend (ComplexShape.embeddingUpIntLE 0)
  obtain ⟨e⟩ := flat_scalar_tensor_resolution J α hflat P Q
  let eH := (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫ (L.sc i).mapHomologyIso F
  by_cases hi : i ≤ 0
  · rw [if_pos hi]
    have hn : (ComplexShape.embeddingUpIntLE 0).f (-i).toNat = i := by
      change 0 - ((-i).toNat : ℤ) = i
      omega
    exact ⟨eH ≪≫ F.mapIso (K.extendHomologyIso
      (ComplexShape.embeddingUpIntLE 0) hn) ≪≫
        F.mapIso ((projectiveResolution P).isoLeftDerivedObj
          (MonoidalCategory.tensorRight Q) (-i).toNat).symm⟩
  · rw [if_neg hi]
    have hzX : IsZero (L.X i) := K.isZero_extend_X (ComplexShape.embeddingUpIntLE 0) i
      (by intro n; change 0 - (n : ℤ) ≠ i; omega)
    have hz : IsZero (L.homology i) :=
      (HomologicalComplex.ExactAt.of_isZero hzX).isZero_homology
    exact ⟨eH ≪≫ (F.map_isZero hz).isoZero⟩

end SheafOfModules
