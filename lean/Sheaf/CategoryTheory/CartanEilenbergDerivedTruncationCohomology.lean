/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.CartanEilenbergTruncationResolution
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Mathlib.Algebra.Homology.TotalComplexSymmetry
/-! # Computing derived cohomology of CE upper truncations

Source: Stacks Project, Tags 015X and 0156.
(blueprint: lem-sp-ce-derived-truncation-cohomology).
-/

@[expose] public section
set_option autoImplicit false
universe uA vA uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false in
/-- The mapped total of the horizontal smart truncation computes RG of the
corresponding upper truncation of the augmented complex, in every cohomological
degree. The bounded-complex wrapper Kq has exactly that underlying complex.
Source: Stacks Project, Tag 015X, Remark 13.26.15;
Tag 0156, Lemma 13.20.1 (injective-resolution computation).
(blueprint: lem-sp-ce-derived-truncation-cohomology).

Proof. The unique truncated CE augmentation gives a quasi-isomorphism into a
bounded-below complex of injectives. The right derived functor is computed by
applying G to this complex. An additive functor commutes with the finite diagonal
coproducts in each total degree. Use the mapped-total isomorphism and the total
flip sign isomorphisms to retain the original, unflipped convention. Applying
cohomology to this complex isomorphism gives the asserted identification.
Negative q and arbitrary integer cohomological degrees need no extra hypotheses:
smart truncation preserves the lower bound, and the same resolution computation
applies to the zero and negative-degree terms. -/
theorem cartanEilenberg_derived_truncation_cohomology
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
    (P : CartanEilenbergPresentation F) (q : ℤ) (Kq : CochainComplex.Plus B)
    (hKq : Kq.obj = CochainComplex.truncLE
      ((F.mapHomologicalComplex (.up ℤ)).obj
        (P.J.cocomplex.extend ComplexShape.embeddingUpNat)) q) (n : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor C n).obj
      (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Kq)) ≅
      (((CartanEilenbergPresentation.mappedFunctor G).obj
        (CochainComplex.truncLE P.I q)).total (.up ℤ)).homology n) := by
  classical
  obtain ⟨a, ⟨ha, haug⟩, _⟩ := cartanEilenberg_truncation_resolution P q
  obtain ⟨aug, ⟨hc, hqi, hterms, hge, hki, hnat⟩, _⟩ := haug
  let U := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
    (CochainComplex.truncLE P.I q)
  let V := (CartanEilenbergPresentation.mappedFunctor G).obj
    (CochainComplex.truncLE P.I q)
  let Tq : CochainComplex.Plus B := ⟨U.total (.up ℤ), ⟨0, hge⟩⟩
  let φ : Kq ⟶ Tq := ObjectProperty.homMk (eqToHom hKq ≫ aug)
  have : QuasiIso aug := hqi
  have : QuasiIso φ.hom := by dsimp [φ]; infer_instance
  have hinj (i : ℤ) : Injective (Tq.obj.X i) := hterms i
  obtain ⟨eRG⟩ := G.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso_of_quasiIso φ
    (fun i ↦ G.rightAcyclic_of_injective _) n
  have : CochainComplex.IsStrictlyGE P.I 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact P.zero_neg
  have : CochainComplex.IsStrictlyGE (CochainComplex.truncLE P.I q) 0 := inferInstance
  obtain ⟨eTotal, _⟩ := G.cartanEilenberg_mapped_total_iso (CochainComplex.truncLE P.I q)
    ⟨0, fun p hp ↦ (CochainComplex.truncLE P.I q).isZero_of_isStrictlyGE 0 p hp⟩
  let eT : V.total (.up ℤ) ≅ (G.mapHomologicalComplex (.up ℤ)).obj (U.total (.up ℤ)) :=
    (V.totalFlipIso (.up ℤ)).symm ≪≫ eTotal ≪≫
      (G.mapHomologicalComplex (.up ℤ)).mapIso (U.totalFlipIso (.up ℤ))
  exact ⟨eRG ≪≫ ((HomologicalComplex.homologyFunctor C (.up ℤ) n).mapIso eT).symm⟩
end CategoryTheory
