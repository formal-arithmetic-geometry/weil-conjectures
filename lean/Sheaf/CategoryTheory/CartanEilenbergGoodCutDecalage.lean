/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Sheaf.CategoryTheory.MapGoodUpperTruncation
import Sheaf.CategoryTheory.GoodTruncationTotalDecalage
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # The good-cut total and decalage

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

private theorem extend_preserves_finite_limits
    {C : Type uC} [Category.{vC} C] [Abelian C] :
    PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor C) := by
  constructor
  intro J _ _
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let e : ComplexShape.embeddingUpNat.extendFunctor C ⋙
        HomologicalComplex.eval C (ComplexShape.up ℤ) (r : ℤ) ≅
        HomologicalComplex.eval C (ComplexShape.up ℕ) r :=
      NatIso.ofComponents (fun K ↦ K.extendXIso ComplexShape.embeddingUpNat rfl)
        (fun f ↦ by
          change (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (r : ℤ) ≫
            _ = _ ≫ f.f r
          erw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat
            (i := r) (i' := (r : ℤ)) rfl]
          simp)
    exact preservesLimitsOfShape_of_natIso e.symm
  · apply Functor.preservesLimitsOfShape_of_isZero _ ?_ _
    apply Functor.isZero
    intro K
    exact HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat n
      (fun r hr ↦ by change (r : ℤ) = n at hr; omega)

private theorem flip_naturality
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    {M N : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : M ⟶ N) :
    HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
        (ComplexShape.up ℤ) ≫ (N.totalFlipIso (ComplexShape.up ℤ)).hom =
      (M.totalFlipIso (ComplexShape.up ℤ)).hom ≫
        HomologicalComplex₂.total.map f (ComplexShape.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
  intro r p h
  simp only [HomologicalComplex.comp_f]
  change M.flip.ιTotal (ComplexShape.up ℤ) r p n h ≫ _ ≫ _ =
    M.flip.ιTotal (ComplexShape.up ℤ) r p n h ≫ _ ≫ _
  erw [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  erw [HomologicalComplex₂.ιTotal_map]
  rfl


/-- The total of the horizontal good cut maps onto the shifted-cycle subcomplex.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-ce-good-cut-decalage).

Proof. First apply the pure good-truncation/decalage comparison to the mapped
bicomplex. Extension by zero preserves finite limits, as seen after evaluation:
in nonnegative degrees it is isomorphic to evaluation, and in negative degrees
it is the zero functor. Hence the actual functor/truncation comparison is an
isomorphism compatible with the inclusions. Naturality of the finite-diagonal
mapped-total comparison follows by checking its specified components. The
total-flip isomorphism is natural, including its invertible signs. Compose these
isomorphisms with the pure comparison and use their inclusion equations.

The pure comparison has the following elementary description. Fix a total degree m.
The full first-quadrant total is the finite coproduct
of the diagonal terms I^(p,m-p), 0 ≤ p ≤ m. The horizontal good cut retains every
summand p<q, replaces the summand p=q by the kernel of its outgoing horizontal
differential, and has zero summands p>q. After applying G this description remains
valid: G is additive and preserves kernels and finite coproducts. In the full
mapped total, vertical filtration m-q consists of the summands p≤q. Modulo vertical
filtration m-q+1 only the horizontal differential out of p=q can survive, since
the vertical differential raises the vertical degree. Therefore its inverse image
intersected with filtration m-q is precisely the coproduct of the retained terms
and this kernel. This intersection is the defining term of Dec(L)^(-q).
Use the coproduct inclusions and the kernel lift to construct the map into that
intersection. Projection to the retained summands and to the boundary kernel gives
its inverse. The equations are checked on each diagonal summand and hence on the
coproduct. The full inclusion is monic; cancelling it shows compatibility with the
differentials, so the degreewise isomorphisms assemble into d. The prescribed
components hu identify application of G to the full total with u. The symmetry
map exchanging the two totalization orders multiplies each summand by its usual
invertible sign. Including these signs in the component maps yields exactly the
stated square with c. Empty diagonals and m<0 are zero. When q=0 there are no
retained strict columns, leaving only the boundary kernel, with the same argument. -/
theorem cartanEilenberg_good_cut_decalage
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (q : ℤ) (hq : 0 ≤ q)
    (L : DecreasingFiltration
      (((CartanEilenbergPresentation.mappedFunctor G).obj I).total (ComplexShape.up ℤ)))
    (hL : ∀ p m : ℤ, L.complexStep p m =
      ((((CartanEilenbergPresentation.mappedFunctor G).obj I).secondFiltration m).step p))
    (u : (((CartanEilenbergPresentation.mappedFunctor G).obj I).flip).total
      (ComplexShape.up ℤ) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
          (ComplexShape.up ℤ)))
    (hu : ∀ (r : ℕ) (p n : ℤ) (h : (r : ℤ) + p = n),
      (((CartanEilenbergPresentation.mappedFunctor G).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) p n h ≫ u.hom.f n =
        (HomologicalComplex.extendXIso
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := (r : ℤ)) rfl).hom ≫
        G.map ((HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
            ComplexShape.embeddingUpNat (i := r) (i' := (r : ℤ)) rfl).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
            (ComplexShape.up ℤ) (r : ℤ) p n h)) :
    let _J := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I
    let Jq := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
      (CochainComplex.truncLE I q)
    let M := (CartanEilenbergPresentation.mappedFunctor G).obj I
    let i := HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map
          (CochainComplex.ιTruncLE I q))) (ComplexShape.up ℤ)
    let c := u.symm ≪≫ M.totalFlipIso (ComplexShape.up ℤ)
    ∃ d : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Jq.flip.total (ComplexShape.up ℤ)) ≅ L.decalageComplex (-q),
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map i ≫ c.hom =
        d.hom ≫ L.decalageι (-q) := by
  classical
  let H := G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor C
  have : PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor C) :=
    extend_preserves_finite_limits
  let Iq := CochainComplex.truncLE I q
  let M := (CartanEilenbergPresentation.mappedFunctor G).obj I
  let Mq := (CartanEilenbergPresentation.mappedFunctor G).obj Iq
  let J := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I
  let Jq := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj Iq
  let α := CochainComplex.ιTruncLE I q
  let αG := (CartanEilenbergPresentation.mappedFunctor G).map α
  let i := HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map α)) (ComplexShape.up ℤ)
  have hcutzero (p : ℤ) (hp : p < 0) : IsZero (Iq.X p) :=
    IsZero.of_iso (hzero p hp) (CochainComplex.truncLEXIso I q p (by omega))
  obtain ⟨v, hv⟩ := Functor.cartanEilenberg_mapped_total_iso G Iq ⟨0, hcutzero⟩
  let ec : Mq ≅ CochainComplex.truncLE M q :=
    asIso (CochainComplex.mapTruncLEComparison H I q)
  let eT := HomologicalComplex₂.total.mapIso ec (ComplexShape.up ℤ)
  have hM (p r : ℤ) (hp : p < 0 ∨ r < 0) : IsZero ((M.X p).X r) := by
    rcases hp with hp | hr
    · exact (HomologicalComplex.eval C (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (hzero p hp)))
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (fun a ha ↦ by change (a : ℤ) = r at ha; omega)
  obtain ⟨d₀, hd₀⟩ := HomologicalComplex₂.good_truncation_total_decalage M hM q hq L hL
  have hm : HomologicalComplex₂.total.map αG (ComplexShape.up ℤ) =
      eT.hom ≫ HomologicalComplex₂.total.map (CochainComplex.ιTruncLE M q)
        (ComplexShape.up ℤ) := by
    change HomologicalComplex₂.total.map αG (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map ec.hom (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)
    rw [← HomologicalComplex₂.total.map_comp]
    congr 1
    exact (CochainComplex.mapTruncLEComparison_ι H I q).symm
  have hn : HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map αG)
        (ComplexShape.up ℤ) ≫ u.hom =
      v.hom ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map i := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
    intro r p h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    by_cases hr : 0 ≤ r
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hr
      change Mq.flip.ιTotal (ComplexShape.up ℤ) (k : ℤ) p n h ≫ _ ≫ _ =
        Mq.flip.ιTotal (ComplexShape.up ℤ) (k : ℤ) p n h ≫ _ ≫ _
      erw [HomologicalComplex₂.ιTotal_map_assoc]
      erw [hu k p n h, reassoc_of% (hv k p n h)]
      change (HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f p))
          ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _ ≫ _ = _
      erw [HomologicalComplex.extendMap_f
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f p))
        ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← G.map_comp]
      dsimp only [i]
      simp only [Category.assoc]
      erw [HomologicalComplex₂.ιTotal_map]
      change _ = _ ≫ G.map (_ ≫
        (HomologicalComplex.extendMap
          (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f p))
          ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _)
      erw [HomologicalComplex.extendMap_f
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f p))
        ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl]
      dsimp only [Iq]
      simp only [Category.assoc, Functor.mapHomologicalComplex_map_f, Functor.id_map]
      simp only [Iso.inv_hom_id_assoc, G.map_comp]
      rfl
    · exact (HomologicalComplex.isZero_extend_X
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (Iq.X p))
        ComplexShape.embeddingUpNat r
        (fun k hk ↦ by change (k : ℤ) = r at hk; omega)).eq_of_src _ _
  let d := v.symm ≪≫ Mq.totalFlipIso (ComplexShape.up ℤ) ≪≫ eT ≪≫ d₀
  refine ⟨d, ?_⟩
  apply (cancel_epi v.hom).mp
  change v.hom ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map i ≫
      u.inv ≫ (M.totalFlipIso (ComplexShape.up ℤ)).hom = _
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc]
  rw [flip_naturality αG]
  rw [hm, hd₀]
  simp only [d, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end CategoryTheory
