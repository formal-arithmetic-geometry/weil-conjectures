/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteCoherence
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF
public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.FixedSquareClosedExchange

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

variable {Cs Cs' CF CC CC' CF' CX' : Type*} [Category Cs] [Category Cs'] [Category CF]
  [Category CC] [Category CC'] [Category CF'] [Category CX']

/-- **The final rearrangement of fact (II)**, abstractly: let `lsc' : L_{F'} ≅ L_{d'} ⋙ L_{X'}`.
If `ν ≫ Ψ(a) ≫ Ψ(P) = lsc'(L S R N) ≫ L_{X'}(L_{d'}(u') ≫ g') ≫ v₁ ≫ v₂ ≫ ν_B` (the exchange of
the fixed loci through `ν_X`), `a ≫ P ≫ m = 𝟙` and
`lsc'(M') ≫ L_{X'}(g') ≫ v₁ ≫ v₂ = L_{F'}(x) ≫ y`, then
`ν = (L_{F'}(u' ≫ x) ≫ y) ≫ ν_B ≫ Ψ(m)`. In a diagram, with `M = L S R N`:
```
L_{F'}(M) ──────────── ν ───────────> Ψ(L_F N) ──Ψ(a ≫ P)──> Ψ(V)
   │ lsc'                                                      ↑ ν_B
L_{X'}(L_{d'} M) ──L_{X'}(L_{d'} u' ≫ g')──> L_{X'}(G') ──v₁ ≫ v₂──> W₀
```
commutes, `m` is a right inverse of `a ≫ P`, and `L_{X'}(g') ≫ v₁ ≫ v₂` (through `lsc'` at `M'`)
factors as `L_{F'}(x) ≫ y`. -/
lemma app_eq_comp_of_comp_map_eq {Ψ : Cs ⥤ Cs'} {R : CF ⥤ CC} {S : CC ⥤ CC'} {L : CC' ⥤ CF'}
    {LF : CF ⥤ Cs} {LF' : CF' ⥤ Cs'}
    {Ld' : CF' ⥤ CX'} {LX' : CX' ⥤ Cs'} (lsc' : LF' ≅ Ld' ⋙ LX') {N : CF} {M' Z : CF'}
    {T V : Cs} {G' : CX'} {W₁ W₀ : Cs'}
    (ν : ((R ⋙ S ⋙ L) ⋙ LF').obj N ⟶ (LF ⋙ Ψ).obj N)
    (u' : L.obj (S.obj (R.obj N)) ⟶ M')
    (g' : Ld'.obj M' ⟶ G') (v₁ : LX'.obj G' ⟶ W₁) (v₂ : W₁ ⟶ W₀) (νB : W₀ ⟶ Ψ.obj V)
    (a : LF.obj N ⟶ T) (P : T ⟶ V) (m : V ⟶ LF.obj N) (x : M' ⟶ Z) (y : LF'.obj Z ⟶ W₀)
    (hFL : ν ≫ Ψ.map a ≫ Ψ.map P =
      lsc'.hom.app (L.obj (S.obj (R.obj N))) ≫ LX'.map (Ld'.map u' ≫ g') ≫ v₁ ≫ v₂ ≫ νB)
    (hC1 : a ≫ P ≫ m = 𝟙 (LF.obj N))
    (hC2 : lsc'.hom.app M' ≫ LX'.map g' ≫ v₁ ≫ v₂ = LF'.map x ≫ y) :
    ν = (LF'.map (u' ≫ x) ≫ y) ≫ νB ≫ Ψ.map m := by
  have hn := lsc'.hom.naturality u'
  simp only [Functor.comp_map] at hn
  calc ν = ν ≫ Ψ.map (a ≫ P ≫ m) := by rw [hC1, Ψ.map_id]; exact (Category.comp_id ν).symm
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

namespace AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.TraceSpecialization

open Scheme MonoidalCategory

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
    boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)
  (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _))
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [hσpt : IsIso σpt]
  (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
    boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)

set_option hygiene false in
/-- The specialization data determined by the support. -/
local notation "𝕋" => ofSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ
  (exceptionalExchange ℓ c.support c'.support νc) σC (dualizingExchange ℓ σpt νX)

set_option maxHeartbeats 1000000 in
-- unfolding the projections of `ofSupportExchange` against the composites is slow
/-- **Fact (II) and the class identity, for the specialization data of the support**: the class
identity `SpecializesComponentClass` of `ν_F` (`fixedLocusToPointCompactSupportExchange`) on a
proper component `j : B ⟶ F`, from the support identity `h` on `M = Rj_! ℚ̄_ℓ`, the identity `hX`
of `ν_X` on the object `T₀` receiving `Rd_! M`, the coherences `hC1` (on `F`) and `hC2` (on `F'`)
of the composition isomorphisms, fact (I) `hI` and the unit class identity `h₂` for
`φ = Ra_{F'!}(Lι'^*(u₀) ≫ ε ≫ x) ≫ y`
(`TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq`,
`CategoryTheory.app_eq_comp_of_comp_map_eq`, `TraceSpecialization.specializesComponentClass_of_eq`).
All the functors are variables here, so that the definitional unfoldings of the specialization
data cost nothing; the concrete instance only matches the hypotheses. -/
theorem specializesComponentClass_ofSupportExchange [IsProper F'.F.hom]
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] (hI : IsIso ((𝕋).ΨF.map (IsContractingAt.componentCounit (ℓ := ℓ) j)))
    {M' : Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (u : ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj
      ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ⟶
      (boundedConstructibleLowerStar ℓ F'.ι).obj M')
    {T₀ : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (κ : (boundedConstructibleLowerShriek ℓ F.d).obj
      ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _)) ⟶ T₀)
    {G' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (χ : ΨX.obj T₀ ⟶ G')
    (g' : (boundedConstructibleLowerShriek ℓ F'.d).obj M' ⟶ G')
    (h : νc.app ((boundedConstructibleLowerStar ℓ F.ι).obj
          ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
        ΨXX.map ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
        χΔ.app ((boundedConstructibleLowerShriek ℓ F.d).obj
          ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map (ΨX.map κ ≫ χ) =
      (boundedConstructibleLowerShriek ℓ c'.support).map u ≫
        (lowerStarLowerShriekCompIso ℓ F'.isPullback.w).hom.app M' ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map g')
    {W₁ W₀ : Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (P : (boundedConstructibleLowerShriek ℓ (toPoint X)).obj T₀ ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint B)).obj (𝟙_ _))
    (v₁ : (boundedConstructibleLowerShriek ℓ (toPoint X')).obj G' ⟶ W₁) (v₂ : W₁ ⟶ W₀)
    (νB : W₀ ⟶ Ψpt.obj ((boundedConstructibleLowerShriek ℓ (toPoint B)).obj (𝟙_ _)))
    (hX : νX.app T₀ ≫ Ψpt.map P =
      (boundedConstructibleLowerShriek ℓ (toPoint X')).map χ ≫ v₁ ≫ v₂ ≫ νB)
    (hC1 : ((lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d)).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _)) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map κ) ≫ P ≫
        (lowerShriekCompOfEq ℓ j (toPoint F.F) (comp_toPoint j)).hom.app (𝟙_ _) = 𝟙 _)
    {Z : Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : M' ⟶ Z)
    (y : (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).obj Z ⟶ W₀)
    (hC2 : (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)).hom.app M' ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map g' ≫ v₁ ≫ v₂ =
      (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).map x ≫ y)
    (u₀ : ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj
      ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ⟶
      (boundedConstructibleLowerStar ℓ F'.ι).obj M') (hu : u₀ = u)
    (φ : (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).obj
      ((𝕋).ΨF.obj ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ⟶ W₀)
    (hφ : φ = (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).map
      (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map u₀ ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).counit.app M') ≫ x) ≫ y)
    (h₂ : BorelMooreSection.unitClass ℓ F'.F ≫ (boundedConstructibleLowerShriek ℓ
        (toPoint F'.F)).map ((𝕋).σF ≫ inv ((𝕋).ΨF.map
          (IsContractingAt.componentCounit (ℓ := ℓ) j))) ≫
        φ ≫ νB = σpt ≫ Ψpt.map (BorelMooreSection.unitClass ℓ B)) :
    (𝕋).SpecializesComponentClass σpt
      (fixedLocusToPointCompactSupportExchange ΨC ΨX ΨXX χΔ
        (exceptionalExchange ℓ c.support c'.support νc) νX) j := by
  have hFL := fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq (F := F) (F' := F') ΨC ΨX
    ΨXX χΔ νc νX ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _)) u κ χ g' h (Ψpt.map P)
    (v₁ ≫ v₂ ≫ νB) hX
  have h₁ := CategoryTheory.app_eq_comp_of_comp_map_eq
    (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)) _ _ g' v₁ v₂ νB _ P _ x y
    hFL hC1 hC2
  subst hu hφ
  exact specializesComponentClass_of_eq _ σpt _ j hI _ νB h₁ h₂

end AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.TraceSpecialization
