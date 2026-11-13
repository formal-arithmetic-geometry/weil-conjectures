/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyStageContinuity
import WeilConjectures.AlgebraicGeometry.EtaleLimitBinaryComparisonLadder
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.FiveLemma

/-! # Kernel detection for a two-open continuity comparison

## References

* Stacks Project, Tags 09YQ and 0A50
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A class killed on the limit is killed at a later stage of a two-open system
(Stacks, Tags 09YQ and 0A50). -/
theorem etale_limit_binary_eventual_zero
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hCU : EtaleCohomologyStageContinuity U.toScheme)
    (hCV : EtaleCohomologyStageContinuity V.toScheme)
    (hCI : EtaleCohomologyStageContinuity (U ⊓ V).toScheme)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    (i₀ : I) (hi : Nonempty (D.obj (op i₀) ≅ (U ⊔ V).toScheme)) :
    ∀ (i : I) (x : H.obj i), (B.ι.app i).hom x = 0 →
      ∃ (j : I) (f : i ⟶ j), (H.map f).hom x = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨e⟩ := hi
  obtain ⟨A₁, A₂, A₄, B₁, B₂, a, b, r, a', b', v₁, v₂, v₄,
    hab, hbr, hab', hv₁, hv₂, hv₄, ha, hb, hr⟩ :=
    etale_limit_binary_comparison_ladder X U V hU hV hCU hCV hCI
      D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB i₀ e
  let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
  let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
  let B₄ := AddCommGrpCat.of
    (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) p ×
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) p)
  let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
    (((cohomologyMap WU.ι L.pt p).prod (cohomologyMap WV.ι L.pt p)).comp eB.hom.hom)
  intro i x hx
  have hz : (colimit.desc H B) (colimit.ι H i x) = 0 := by
    change (colimit.ι H i ≫ colimit.desc H B) x = 0
    rwa [colimit.ι_desc]
  have hinj := AddMonoidHom.injective_of_surjective_of_injective_of_injective
    a.hom b.hom r.hom a'.hom b'.hom r'.hom v₁.hom v₂.hom
    (colimit.desc H B).hom v₄.hom
    (AddMonoidHom.ext fun x => (ha x).symm)
    (AddMonoidHom.ext fun x => (hb x).symm)
    (AddMonoidHom.ext fun x => (hr x).symm) hab hbr hab' hv₁ hv₂ hv₄
  have hzero : colimit.ι H i x = 0 := hinj (by simpa using hz)
  have hzero' : colimit.ι H i x = colimit.ι H i (0 : H.obj i) := by
    simpa using hzero
  obtain ⟨j, f, g, hfg⟩ := (Concrete.colimit_rep_eq_iff_exists H x (0 : H.obj i)).mp hzero'
  exact ⟨j, f, by simpa using hfg⟩

end AlgebraicGeometry.Etale
