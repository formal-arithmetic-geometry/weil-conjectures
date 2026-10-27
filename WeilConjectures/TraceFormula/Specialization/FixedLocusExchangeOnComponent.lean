/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteCoherence
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF
public import WeilConjectures.Tactic.FirstOrderApply

/-!

# The exchange of the fixed loci on a component: the final rearrangement

Fact (II) of `ComponentClassReduction` asks for the factorization
`ν_F(j_! ℚ̄_ℓ) = φ ≫ ν_B ≫ Ψ_s(Ra_{B!} ≅ Ra_{F!} j_!)` of the exchange of the fixed loci on a
proper component `j : B ⟶ F`.
`TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq` computes
`ν_F(N) ≫ Ψ_s(a) ≫ Ψ_s(P)` and the exchange `ν_X` on `R(dj)_* ℚ̄_ℓ` gives the remaining factor;
this file contains the cancellation (`CategoryTheory.app_eq_comp_of_comp_map_eq`) and the
two coherences of the composition isomorphisms of the lower shriek it needs, on the fixed locus
`F` (`ProEtale.CondensedRing.lowerShriekCompOfEq_hom_app_comp_map_comp_inv`) and on the special
fixed locus `F'` (`ProEtale.CondensedRing.lowerShriekCompOfEq_hom_app_comp_map_eqToHom_comp_inv`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {Cs Cs' CF' CX' : Type*} [Category Cs] [Category Cs'] [Category CF'] [Category CX']

/-- **The final rearrangement of fact (II)**, abstractly: let `lsc' : L_{F'} ≅ L_{d'} ⋙ L_{X'}`.
If `ν' ≫ Ψ(a) ≫ Ψ(P) = lsc'(N'') ≫ L_{X'}(L_{d'}(u') ≫ g') ≫ v₁ ≫ v₂ ≫ ν_B` (the exchange of
the fixed loci through `ν_X`), `a ≫ P ≫ m = 𝟙` and
`lsc'(M') ≫ L_{X'}(g') ≫ v₁ ≫ v₂ = L_{F'}(x) ≫ y`, then
`ν = (L_{F'}(u'₀ ≫ x) ≫ y) ≫ ν_B ≫ Ψ(m)` for any `u'₀` equal to `u'` (and `ν` equal to the `ν'`
of the hypothesis). -/
lemma app_eq_comp_of_comp_map_eq {Ψ : Cs ⥤ Cs'} {LF' : CF' ⥤ Cs'} {Ld' : CF' ⥤ CX'}
    {LX' : CX' ⥤ Cs'} (lsc' : LF' ≅ Ld' ⋙ LX') {N'' M' Z : CF'} {U T V : Cs} {G' : CX'}
    {W₁ W₀ : Cs'} (ν ν' : LF'.obj N'' ⟶ Ψ.obj U) (hν : ν = ν')
    (u' u'₀ : N'' ⟶ M') (hu : u'₀ = u')
    (g' : Ld'.obj M' ⟶ G') (v₁ : LX'.obj G' ⟶ W₁) (v₂ : W₁ ⟶ W₀) (νB : W₀ ⟶ Ψ.obj V)
    (a : U ⟶ T) (P : T ⟶ V) (m : V ⟶ U) (x : M' ⟶ Z) (y : LF'.obj Z ⟶ W₀)
    (hFL : ν' ≫ Ψ.map a ≫ Ψ.map P =
      lsc'.hom.app N'' ≫ LX'.map (Ld'.map u' ≫ g') ≫ v₁ ≫ v₂ ≫ νB)
    (hC1 : a ≫ P ≫ m = 𝟙 U) (hC2 : lsc'.hom.app M' ≫ LX'.map g' ≫ v₁ ≫ v₂ = LF'.map x ≫ y) :
    ν = (LF'.map (u'₀ ≫ x) ≫ y) ≫ νB ≫ Ψ.map m := by
  subst hu hν
  have hn := lsc'.hom.naturality u'₀
  simp only [Functor.comp_map] at hn
  calc ν = ν ≫ Ψ.map (a ≫ P ≫ m) := by rw [hC1, Ψ.map_id, Category.comp_id]
    _ = _ := by
      simp only [Functor.map_comp, ← Category.assoc] at hFL ⊢
      rw [hFL]
      simp only [Category.assoc]
      rw [← reassoc_of% hn, reassoc_of% hC2]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {B F X P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **Associativity of `lowerShriekCompOfEq`**: for `aB = j ≫ aF`, `aF = d ≫ aX` and
`aB = (j ≫ d) ≫ aX`, `Ra_{F!} Rj_! ≅ Ra_{X!} Rd_! Rj_! ≅ Ra_{X!} R(jd)_! ≅ Ra_{B!}` is
`Ra_{F!} Rj_! ≅ Ra_{B!}`. -/
lemma lowerShriekCompOfEq_hom_app_comp_map_comp_inv (j : B ⟶ F) (d : F ⟶ X) {aF : F ⟶ P}
    {aX : X ⟶ P} {aB : B ⟶ P} (wd : d ≫ aX = aF) (wj : j ≫ aF = aB) (wjd : (j ≫ d) ≫ aX = aB)
    (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ d aX wd).hom.app ((boundedConstructibleLowerShriek ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app K) ≫
      (lowerShriekCompOfEq ℓ (j ≫ d) aX wjd).inv.app K =
    (lowerShriekCompOfEq ℓ j aF wj).inv.app K := by
  subst wd wj
  have h := lowerShriekComp_hom_app_comp_map_inv_comp_inv ℓ j d aX K
  simp only [lowerShriekCompOfEq_rfl]
  rw [h]
  simp

/-- **`lowerShriekCompOfEq` through a transport**: for `r ≫ d = g`, `aF = d ≫ aX`,
`aB = r ≫ aF` and `aB = g ≫ aX`, `Ra_{F!} Rr_! ≅ Ra_{X!} Rd_! Rr_! ≅ Ra_{X!} R(rd)_! = Ra_{X!} Rg_!
≅ Ra_{B!}` is `Ra_{F!} Rr_! ≅ Ra_{B!}`. -/
lemma lowerShriekCompOfEq_hom_app_comp_map_eqToHom_comp_inv (r : B ⟶ F) (d : F ⟶ X) {g : B ⟶ X}
    (hg : r ≫ d = g) {aF : F ⟶ P} {aX : X ⟶ P} {aB : B ⟶ P} (wd : d ≫ aX = aF)
    (wr : r ≫ aF = aB) (wg : g ≫ aX = aB) (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ d aX wd).hom.app ((boundedConstructibleLowerShriek ℓ r).obj K) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r d).inv.app K ≫
          eqToHom (by rw [hg])) ≫
      (lowerShriekCompOfEq ℓ g aX wg).inv.app K =
    (lowerShriekCompOfEq ℓ r aF wr).inv.app K := by
  subst hg
  simp only [eqToHom_refl, Category.comp_id]
  exact lowerShriekCompOfEq_hom_app_comp_map_comp_inv ℓ r d wd wr wg K

/-- The coherence on the fixed locus in the form of fact (II): for a proper `j : B ⟶ F` and
`d : F ⟶ X` with `j ≫ d` proper, `Ra_{F!} Rj_! ≅ Ra_{X!} Rd_! Rj_!`, then `Ra_{X!}` of
`Rd_! Rj_! ≅ Rd_! Rj_* ≅ Rd_! Rj_! ≅ R(jd)_! ≅ R(jd)_*` and of `R(jd)_* ≅ R(jd)_!`,
`Ra_{X!} R(jd)_! ≅ Ra_{B!}` and `Ra_{B!} ≅ Ra_{F!} Rj_!` compose to the identity. -/
lemma lowerShriekCompOfEq_hom_app_comp_map_comp_inv_comp_hom (j : B ⟶ F) (d : F ⟶ X)
    [IsProper j.left] [IsProper (j ≫ d).left] {aF : F ⟶ P} {aX : X ⟶ P} {aB : B ⟶ P}
    (wd : d ≫ aX = aF) (wj : j ≫ aF = aB) (wjd : (j ≫ d) ≫ aX = aB)
    (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((lowerShriekCompOfEq ℓ d aX wd).hom.app ((boundedConstructibleLowerShriek ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app K) ≫
          (boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app K) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app K ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).hom.app K)) ≫
      ((boundedConstructibleLowerShriek ℓ aX).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).inv.app K) ≫
        (lowerShriekCompOfEq ℓ (j ≫ d) aX wjd).inv.app K) ≫
      (lowerShriekCompOfEq ℓ j aF wj).hom.app K = 𝟙 _ := by
  have h := lowerShriekCompOfEq_hom_app_comp_map_comp_inv ℓ j d wd wj wjd K
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at h ⊢
  rw [reassoc_of% h, Iso.inv_hom_id_app]
  rfl

/-- The coherence on the special fixed locus in the form of fact (II): for proper `r : B ⟶ F` and
`g = r ≫ d`, `Ra_{F!} Rr_* ≅ Ra_{X!} Rd_! Rr_*`, then `Ra_{X!}` of
`Rd_! Rr_* ≅ Rd_! Rr_! ≅ R(rd)_! ≅ R(rd)_* = Rg_* ≅ Rg_!` and `Ra_{X!} Rg_! ≅ Ra_{B!}` is
`Ra_{F!} Rr_* ≅ Ra_{F!} Rr_! ≅ Ra_{B!}`. -/
lemma lowerShriekCompOfEq_hom_app_comp_map_isoLowerStar_comp_inv (r : B ⟶ F) (d : F ⟶ X)
    {g : B ⟶ X} (hg : r ≫ d = g) [IsProper r.left] [IsProper (r ≫ d).left] [IsProper g.left]
    {aF : F ⟶ P} {aX : X ⟶ P} {aB : B ⟶ P} (wd : d ≫ aX = aF) (wr : r ≫ aF = aB)
    (wg : g ≫ aX = aB) (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleLowerStar ℓ (r ≫ d)).obj K =
      (boundedConstructibleLowerStar ℓ g).obj K) :
    (lowerShriekCompOfEq ℓ d aX wd).hom.app ((boundedConstructibleLowerStar ℓ r).obj K) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        (((boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app K) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r d).inv.app K ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ d)).hom.app K) ≫
          eqToHom e) ≫
      (boundedConstructibleLowerShriek ℓ aX).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app K) ≫
      (lowerShriekCompOfEq ℓ g aX wg).inv.app K =
    (boundedConstructibleLowerShriek ℓ aF).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app K) ≫
      (lowerShriekCompOfEq ℓ r aF wr).inv.app K := by
  subst hg
  have h := lowerShriekCompOfEq_hom_app_comp_map_comp_inv ℓ r d wd wr wg K
  have n := (lowerShriekCompOfEq ℓ d aX wd).hom.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app K)
  simp only [Functor.comp_map] at n
  rw [eqToHom_refl, Category.comp_id, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, ← reassoc_of% n, h]

/-- `boundedConstructibleLowerStarCompOfEq` along `f ≫ g = f ≫ g` is the composition
isomorphism. -/
@[simp]
lemma boundedConstructibleLowerStarCompOfEq_hom_app_self (f : B ⟶ F) (g : F ⟶ X)
    (w : f ≫ g = f ≫ g) (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarCompOfEq ℓ f g w).hom.app K =
      (boundedConstructibleLowerStarComp ℓ f g).hom.app K := by
  simp [boundedConstructibleLowerStarCompOfEq]

end AlgebraicGeometry.ProEtale.CondensedRing
