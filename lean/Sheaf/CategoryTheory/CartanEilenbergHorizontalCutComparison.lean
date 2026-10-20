/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Totalization and the horizontal good cut

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The total of a horizontal good cut models the derived truncation. Applying an
additive left exact functor identifies the cut inclusion with the shifted cycle
inclusion. Injectivity of the total terms is a separate assertion.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-ce-horizontal-cut-comparison).

Proof. Truncate the bicomplex horizontally at q, retaining its horizontal cycles
in the final column. Truncate the base complex K in the same way. The augmentation
into the cut is columnwise a quasi-isomorphism: use the original column hypotheses
below q, the cycles hypothesis at q, and the zero columns above q. The total of
this augmentation is a quasi-isomorphism by the finite-diagonal augmented-column
argument. The good truncation of K represents tau_{<q+1} Q(K), so localizing this
augmentation gives r. Totalizing the bicomplex inclusion gives i, and its square
with the augmentations gives the displayed derived square.
For c, use the canonical finite-diagonal sum comparison for G and the symmetry
isomorphism between the two orders of totalization. At resolution degree zero the
symmetry sign is one; this is exactly the last displayed formula.
In degree m the cut includes every summand of horizontal degree less than q and
the horizontal kernel in degree q. Its image in the full total consists of the
vertical-filtration m-q terms whose outgoing differential has vertical filtration
at least m-q+1. This is precisely the intersection defining Dec(L)^(-q). The
horizontal and vertical components of the total differential show that this
identification commutes with the differential. G preserves horizontal kernels
and finite diagonal sums, so it gives the complex isomorphism d. The construction
uses the same summand inclusions as c and hence gives the second displayed square.
All constructions vanish on negative diagonals, and empty diagonals cause no
exception. No injectivity or acyclicity assumption on G(K) is used. -/
theorem cartanEilenberg_horizontal_cut_comparison
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex.Plus B)
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hcolumns : ∀ p : ℤ, QuasiIso (e.f p))
    (hcycles : ∀ p : ℤ, QuasiIso (HomologicalComplex.cyclesMap e p))
    (q : ℤ) (hq : 0 ≤ q)
    (T S : CochainComplex.Plus B)
    (hT : T.obj = (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
      (ComplexShape.up ℤ))
    (hS : S.obj = (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
      (CochainComplex.truncLE I q)).flip).total (ComplexShape.up ℤ))
    (b : K ⟶ T) (hb : QuasiIso b.hom)
    (haug : ∀ m : ℤ, b.hom.f m ≫ (eqToHom hT).f m =
      (e.f m).f 0 ≫
        (HomologicalComplex.extendXIso
          (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) 0 m m (zero_add m))
    (L : DecreasingFiltration
      (((CartanEilenbergPresentation.mappedFunctor G).obj I).total (ComplexShape.up ℤ)))
    (hL : ∀ p m : ℤ, L.complexStep p m =
      ((((CartanEilenbergPresentation.mappedFunctor G).obj I).secondFiltration m).step p)) :
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    ∃ (i : S ⟶ T)
      (r : (t.truncLT (q + 1)).obj (DerivedCategory.Plus.Q.obj K) ≅
        DerivedCategory.Plus.Q.obj S)
      (c : (G.mapCochainComplexPlus.obj T).obj ≅
        (((CartanEilenbergPresentation.mappedFunctor G).obj I).total (ComplexShape.up ℤ)))
      (d : (G.mapCochainComplexPlus.obj S).obj ≅ L.decalageComplex (-q)),
      r.hom ≫ DerivedCategory.Plus.Q.map i =
        (t.truncLTι (q + 1)).app (DerivedCategory.Plus.Q.obj K) ≫
          DerivedCategory.Plus.Q.map b ∧
      (G.mapCochainComplexPlus.map i).hom ≫ c.hom = d.hom ≫ L.decalageι (-q) ∧
      (∀ m : ℤ, G.map (
          (HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
            (ComplexShape.up ℤ) 0 m m (zero_add m) ≫
          inv ((eqToHom hT).f m)) ≫ c.hom.f m =
        (HomologicalComplex.extendXIso
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        ((CartanEilenbergPresentation.mappedFunctor G).obj I).ιTotalOrZero
          (ComplexShape.up ℤ) m 0 m) := by
  classical
  rcases T with ⟨T, hTp⟩
  rcases S with ⟨S, hSp⟩
  dsimp only at hT hS
  subst T S
  let J := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I
  let Jq := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
    (CochainComplex.truncLE I q)
  let M := (CartanEilenbergPresentation.mappedFunctor G).obj I
  let ic : Jq.flip.total (ComplexShape.up ℤ) ⟶ J.flip.total (ComplexShape.up ℤ) :=
    HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map
          (CochainComplex.ιTruncLE I q))) (ComplexShape.up ℤ)
  let i : (⟨Jq.flip.total (ComplexShape.up ℤ), hSp⟩ : CochainComplex.Plus B) ⟶
      ⟨J.flip.total (ComplexShape.up ℤ), hTp⟩ := ObjectProperty.homMk ic
  obtain ⟨u, hu⟩ := Functor.cartanEilenberg_mapped_total_iso G I ⟨0, hzero⟩
  let c : (G.mapCochainComplexPlus.obj
      (⟨J.flip.total (ComplexShape.up ℤ), hTp⟩ : CochainComplex.Plus B)).obj ≅
      M.total (ComplexShape.up ℤ) := u.symm ≪≫ M.totalFlipIso (ComplexShape.up ℤ)
  have hcut : ∃
      (r : (DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj
          (DerivedCategory.Plus.Q.obj K) ≅
        DerivedCategory.Plus.Q.obj ⟨Jq.flip.total (ComplexShape.up ℤ), hSp⟩)
      (d : (G.mapCochainComplexPlus.obj
          (⟨Jq.flip.total (ComplexShape.up ℤ), hSp⟩ : CochainComplex.Plus B)).obj ≅
        L.decalageComplex (-q)),
      r.hom ≫ DerivedCategory.Plus.Q.map i =
        (DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app
          (DerivedCategory.Plus.Q.obj K) ≫ DerivedCategory.Plus.Q.map b ∧
      (G.mapCochainComplexPlus.map i).hom ≫ c.hom = d.hom ≫ L.decalageι (-q) := by
    exact cartanEilenberg_good_cut_identification G K I e hzero hcolumns hcycles
      q hq hTp hSp b hb (by simpa using haug) L hL u hu
  obtain ⟨r, d, hr, hd⟩ := hcut
  refine ⟨i, r, c, d, hr, hd, ?_⟩
  intro m
  change G.map (_ ≫ _ ≫ inv (𝟙 ((J.flip.total (ComplexShape.up ℤ)).X m))) ≫
      (u.inv ≫ (M.totalFlipIso (ComplexShape.up ℤ)).hom).f m = _
  simp only [IsIso.inv_id, Category.comp_id, HomologicalComplex.comp_f]
  have hu0 := hu 0 m m (zero_add m)
  have huv :
      G.map ((HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        J.flip.ιTotal (ComplexShape.up ℤ) 0 m m (zero_add m)) ≫ u.inv.f m =
      (HomologicalComplex.extendXIso
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        M.flip.ιTotal (ComplexShape.up ℤ) 0 m m (zero_add m) := by
    apply (cancel_mono (u.hom.f m)).mp
    have hui : u.inv.f m ≫ u.hom.f m = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, u.inv_hom_id]
      rfl
    erw [Category.assoc, hui, Category.comp_id]
    erw [Category.assoc, hu0]
    simp
    rfl
  rw [reassoc_of% huv]
  rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  have hs : ComplexShape.σ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) m 0 = 1 := by
    change Int.negOnePow (m * 0) = 1
    simp
  rw [hs, one_smul, HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (add_zero m)]

end CategoryTheory
