/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.CategoryTheory.CartanEilenbergHorizontalCutTerms
import Sheaf.CategoryTheory.CartanEilenbergTotalInjectiveTerms
import Sheaf.CategoryTheory.CartanEilenbergHorizontalCutComparison
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution

/-! # Injective models of the horizontal good truncation

Source: Stacks Project, Derived Categories, Tags 015X and 015N.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The horizontal good cut of a Cartan--Eilenberg resolution gives compatible
injective models of the full complex and its canonical truncation. The assertion
only concerns resolutions and termwise application of G, before deriving G.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-ce-decalage-injective-model).

Proof. Put K = F(J), extended by zero. Cut I horizontally at q, with its horizontal
cycles in column q and zero columns above q. The cycles, differential and zero maps
make this an actual bicomplex. The augmentation from the good truncation of K is a
columnwise quasi-isomorphism: below q use column_quasiIso, and in column q use the
cycles clause of horizontal_quasiIso. All terms are injective, including the last
column by horizontal_injective. The full and cut bicomplexes vanish outside the
first quadrant. Their finite-diagonal totals T and S are thus bounded below and
termwise injective. The total augmentation b is a quasi-isomorphism by the acyclic
augmented-column argument, and the cut augmentation gives r after localization.
The canonical comparison between good truncation of a complex and derived
truncation identifies its source with tau_{<q+1} Q(K). The augmentation square
gives r.hom followed by Q(i) equal to the truncation inclusion followed by Q(b).
In each total degree m, the cut total has all summands with horizontal degree
less than q and the horizontal kernel in degree q. The kernel condition for its
inclusion into the full total is exactly that the outgoing differential land in
vertical filtration m-q+1. Thus its image subcomplex is Dec(L)^(-q). An additive
left exact G preserves these kernels and the finite diagonal sums. This gives c
and d and the inclusion square. On the vertical degree zero summands the full
augmentation has exactly the displayed components, so the given component
formula for a gives the final equality. Negative source terms are zero. -/
theorem cartanEilenberg_decalage_injective_model
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G]
    (P : CartanEilenbergPresentation F)
    (L : DecreasingFiltration (P.total G))
    (hL : ∀ p m : ℤ, L.complexStep p m =
      ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration m).step p))
    (a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
        ComplexShape.embeddingUpNat ⟶ P.total G)
    (ha : ∀ n : ℕ, a.f (n : ℤ) =
      (HomologicalComplex.extendXIso
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
        ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
      G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
        (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
      (HomologicalComplex.extendXIso
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
        ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
      HomologicalComplex₂.ιTotalOrZero
        ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
        (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ))
    (q : ℤ) (hq : 0 ≤ q) :
    let K₀ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex
    let K : CochainComplex.Plus B :=
      ⟨K₀.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    ∃ (T S : CochainComplex.Plus B) (b : K ⟶ T) (i : S ⟶ T)
      (r : (t.truncLT (q + 1)).obj (DerivedCategory.Plus.Q.obj K) ≅
        DerivedCategory.Plus.Q.obj S)
      (c : (G.mapCochainComplexPlus.obj T).obj ≅ P.total G)
      (d : (G.mapCochainComplexPlus.obj S).obj ≅ L.decalageComplex (-q)),
      (∀ m, Injective (T.obj.X m)) ∧ (∀ m, Injective (S.obj.X m)) ∧
      QuasiIso b.hom ∧
      r.hom ≫ DerivedCategory.Plus.Q.map i =
        (t.truncLTι (q + 1)).app (DerivedCategory.Plus.Q.obj K) ≫
          DerivedCategory.Plus.Q.map b ∧
      (G.mapCochainComplexPlus.map i).hom ≫ c.hom =
        d.hom ≫ L.decalageι (-q) ∧
      (G.mapCochainComplexPlus.map b).hom ≫ c.hom =
        (HomologicalComplex.mapExtendIso K₀ ComplexShape.embeddingUpNat G).hom ≫ a := by
  classical
  let K₀ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex
  let K : CochainComplex.Plus B :=
    ⟨K₀.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let K' : CochainComplex.Plus B :=
    ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat), 0, inferInstance⟩
  let Iq := CochainComplex.truncLE P.I q
  obtain ⟨hqzero, hqterms⟩ := cartanEilenberg_horizontal_cut_terms P.I P.zero_neg
    P.term_injective (fun p r ↦ (P.horizontal_injective p r).1) q hq
  obtain ⟨hTge, hTinj⟩ :=
    cartanEilenberg_total_injective_terms P.I P.zero_neg P.term_injective
  obtain ⟨hSge, hSinj⟩ := cartanEilenberg_total_injective_terms Iq hqzero hqterms
  let T : CochainComplex.Plus B :=
    ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj P.I).flip).total
      (ComplexShape.up ℤ), 0, hTge⟩
  let S : CochainComplex.Plus B :=
    ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj Iq).flip).total
      (ComplexShape.up ℤ), 0, hSge⟩
  obtain ⟨aug, haug, haugq, _⟩ := Functor.cartanEilenberg_total_resolution K' P.I P.e
    ⟨0, P.zero_neg⟩ P.term_injective P.column_quasiIso
  let b₀ : K' ⟶ T := ObjectProperty.homMk aug
  obtain ⟨i, r₀, c, d, hr₀, hi, hc⟩ := cartanEilenberg_horizontal_cut_comparison G
    K' P.I P.e P.zero_neg P.column_quasiIso (fun p ↦ (P.horizontal_quasiIso p).1)
    q hq T S rfl rfl b₀ haugq (by intro m; convert haug m using 1; simp [b₀, T]) L hL
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let mF : K' ≅ K := (CochainComplex.plus B).isoMk
    (P.J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)
  let b : K ⟶ T := mF.inv ≫ b₀
  let r := (t.truncLT (q + 1)).mapIso (DerivedCategory.Plus.Q.mapIso mF.symm) ≪≫ r₀
  refine ⟨T, S, b, i, r, c, d, hTinj, hSinj, ?_, ?_, hi, ?_⟩
  · have : QuasiIso aug := haugq
    change QuasiIso (mF.inv.hom ≫ aug)
    infer_instance
  · dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [Category.assoc, hr₀]
    rw [(t.truncLTι (q + 1)).naturality_assoc]
    simp [b, Functor.map_comp, K, K₀, t]
  · have hc' (m : ℤ) :
        G.map (aug.f m) ≫ c.hom.f m =
        G.map ((P.e.f m).f 0) ≫
          (HomologicalComplex.extendXIso
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X m))
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
          ((CartanEilenbergPresentation.mappedFunctor G).obj P.I).ιTotalOrZero
            (ComplexShape.up ℤ) m 0 m := by
      rw [haug m, G.map_comp, Category.assoc]
      simpa [T, Category.assoc] using
        congrArg (fun f ↦ G.map ((P.e.f m).f 0) ≫ f) (hc m)
    ext m
    dsimp only [b, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
      HomologicalComplex.comp_f]
    change G.map ((mF.inv.hom ≫ aug).f m) ≫ c.hom.f m = _
    simp only [HomologicalComplex.comp_f, G.map_comp, Category.assoc]
    rw [hc' m]
    by_cases hm : 0 ≤ m
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [ha n]
      have hn : ComplexShape.embeddingUpNat.r (n : ℤ) = some n :=
        ComplexShape.embeddingUpNat.r_f n
      have hzero : ComplexShape.embeddingUpNat.r (0 : ℤ) = some 0 :=
        ComplexShape.embeddingUpNat.r_f 0
      simp [mF, HomologicalComplex.mapExtendIso,
        HomologicalComplex.mapExtendX_hom_eq P.J.cocomplex F hn,
        HomologicalComplex.mapExtendX_hom_eq K₀ G hn,
        HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
        eqToHom_map, K₀, K, K']
    · exact (G.map_isZero
        (HomologicalComplex.isZero_extend_X K₀ ComplexShape.embeddingUpNat m
          (fun n hn ↦ by change (n : ℤ) = m at hn; omega))).eq_of_src _ _

end CategoryTheory
