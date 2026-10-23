/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CompactCohomology

/-!

# Composition of the Frobenius comparisons of the lower shriek

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type. For endomorphisms
`a_X, a_Y` with `a_X ≫ f = f ≫ a_Y`, a cartesian square `p_a ≫ f = f'_a ≫ a_Y` and a relative
Frobenius `r_a` with `r_a ≫ p_a = a_X`, `r_a ≫ f'_a = f`, a finite universal homeomorphism, the
Frobenius comparison `θ_a : Rf_! ⋙ La_Y^* ≅ La_X^* ⋙ Rf_!` is
`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison` (blueprint `sk-d-weil-push`). This
file proves that these comparisons compose (blueprint `sk-i-relative-frob` (1) and
`lem-trf-weil-shriek-iterates` (1)): for a second such pair `b_X, b_Y` and a relative Frobenius
for the composites `a ≫ b`,
```
θ_{a ≫ b} = θ_a(Lb_X^* -) ∘ La_Y^*(θ_b)
```
after the composition isomorphisms of the pullbacks.

## The relative pullback

For a proper morphism `r : X ⟶ X'` and `f' : X' ⟶ Y` the *relative pullback*
`ProEtale.CondensedRing.relativePullback` is the composite
```
Rf'_! M ⟶ Rf'_! Rr_* Lr^* M ≅ Rf'_! Rr_! Lr^* M ≅ R(r ≫ f')_! Lr^* M
```
of the unit of `Lr^* ⊣ Rr_*`, the identification `Rr_! ≅ Rr_*` and the composition isomorphism
of the lower shriek. For `f'` the structure morphism of `X'` it is the pullback on compactly
supported cohomology `ProEtale.CondensedRing.compactPullback`. It is compatible with composition
(`ProEtale.CondensedRing.relativePullback_comp_app`) and with base change
(`ProEtale.CondensedRing.map_relativePullback_app_comp_baseChange_app`), and the Frobenius
comparison is the compact-support base change followed by the relative pullback along the
relative Frobenius (`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison_hom_app_eq`).

## Main statements

- `ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison_comp`: the composition law of the
  Frobenius comparisons.

The proof follows blueprint `lem-trf-weil-shriek-iterates`, Step 2: the square defining the
relative Frobenius of `a` is the vertical pasting of the square of `r_b` along the projection
`q : X'_{a ≫ b} ⟶ X'_b` and of the square of `f'_b` along `a_Y`; the latter pastes horizontally
with the square of `b` to the square of `a ≫ b`. The exchange of the `r_b`-square is the
direct-image exchange, which carries the unit of `r_b` to the unit of its base change
`t : X'_a ⟶ X'_{a ≫ b}`, and `r_{a ≫ b} = r_a ≫ t`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.PullbackFamily

/-- An abstract coherence of composition isomorphisms of families of pullback functors, used for
the composition law of the Frobenius comparisons of the lower shriek: for maps
`r_a : A ⟶ B`, `t : B ⟶ C`, `q : C ⟶ D`, `p_b : D ⟶ A`, `p_a : B ⟶ A`, `r_b : A ⟶ D` with
`p_a ≫ r_b = t ≫ q`, the two identifications of `U r_a ⋙ U t ⋙ U q ⋙ U p_b` (applied in the
contravariant order) with the functor along `(r_a ≫ t) ≫ q ≫ p_b = (r_a ≫ p_a) ≫ r_b ≫ p_b`
agree. Stating it for abstract families keeps the computation cheap. -/
lemma comp_inv_app_coherence {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    {DA DB DC DD : Type*} [Category DA] [Category DB] [Category DC] [Category DD]
    (UAB : (A ⟶ B) → DB ⥤ DA) (UBC : (B ⟶ C) → DC ⥤ DB) (UCD : (C ⟶ D) → DD ⥤ DC)
    (UDA : (D ⟶ A) → DA ⥤ DD) (UBA : (B ⟶ A) → DA ⥤ DB) (UAD : (A ⟶ D) → DD ⥤ DA)
    (UAC : (A ⟶ C) → DC ⥤ DA) (UBD : (B ⟶ D) → DD ⥤ DB) (UAA : (A ⟶ A) → DA ⥤ DA)
    (UCA : (C ⟶ A) → DA ⥤ DC)
    (c₁ : ∀ (a : A ⟶ B) (b : B ⟶ C), UAC (a ≫ b) ≅ UBC b ⋙ UAB a)
    (c₂ : ∀ (a : A ⟶ C) (b : C ⟶ D), UAD (a ≫ b) ≅ UCD b ⋙ UAC a)
    (c₃ : ∀ (a : B ⟶ C) (b : C ⟶ D), UBD (a ≫ b) ≅ UCD b ⋙ UBC a)
    (c₄ : ∀ (a : A ⟶ B) (b : B ⟶ D), UAD (a ≫ b) ≅ UBD b ⋙ UAB a)
    (c₅ : ∀ (a : B ⟶ A) (b : A ⟶ D), UBD (a ≫ b) ≅ UAD b ⋙ UBA a)
    (c₆ : ∀ (a : A ⟶ B) (b : B ⟶ A), UAA (a ≫ b) ≅ UBA b ⋙ UAB a)
    (c₇ : ∀ (a : A ⟶ A) (b : A ⟶ D), UAD (a ≫ b) ≅ UAD b ⋙ UAA a)
    (c₈ : ∀ (a : C ⟶ D) (b : D ⟶ A), UCA (a ≫ b) ≅ UDA b ⋙ UCD a)
    (c₉ : ∀ (a : A ⟶ C) (b : C ⟶ A), UAA (a ≫ b) ≅ UCA b ⋙ UAC a)
    (c₁₀ : ∀ (a : A ⟶ D) (b : D ⟶ A), UAA (a ≫ b) ≅ UDA b ⋙ UAD a)
    (c₁₁ : ∀ (a b : A ⟶ A), UAA (a ≫ b) ≅ UAA b ⋙ UAA a)
    (c₁₂ : ∀ (a : A ⟶ D) (b : D ⟶ A), UAA (a ≫ b) ≅ UDA b ⋙ UAD a)
    (H₁ : ∀ (f : A ⟶ C) (g : C ⟶ D) (h : D ⟶ A) (K : DA),
      (UAC f).map ((c₈ g h).inv.app K) ≫ (c₉ f (g ≫ h)).inv.app K =
        (c₂ f g).inv.app ((UDA h).obj K) ≫ (c₁₂ (f ≫ g) h).inv.app K ≫
          eqToHom (by rw [Category.assoc]))
    (H₂ : ∀ (f : A ⟶ A) (g : A ⟶ D) (h : D ⟶ A) (K : DA),
      (UAA f).map ((c₁₀ g h).inv.app K) ≫ (c₁₁ f (g ≫ h)).inv.app K =
        (c₇ f g).inv.app ((UDA h).obj K) ≫ (c₁₂ (f ≫ g) h).inv.app K ≫
          eqToHom (by rw [Category.assoc]))
    (H₃ : ∀ (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (K : DD),
      (c₁ f g).inv.app ((UCD h).obj K) ≫ (c₂ (f ≫ g) h).inv.app K =
        (UAB f).map ((c₃ g h).inv.app K) ≫ (c₄ f (g ≫ h)).inv.app K ≫
          eqToHom (by rw [Category.assoc]))
    (H₄ : ∀ (f : A ⟶ B) (g : B ⟶ A) (h : A ⟶ D) (K : DD),
      (c₆ f g).inv.app ((UAD h).obj K) ≫ (c₇ (f ≫ g) h).inv.app K =
        (UAB f).map ((c₅ g h).inv.app K) ≫ (c₄ f (g ≫ h)).inv.app K ≫
          eqToHom (by rw [Category.assoc]))
    {ra : A ⟶ B} {t : B ⟶ C} {q : C ⟶ D} {pb : D ⟶ A} {pa : B ⟶ A} {rb : A ⟶ D}
    (w : pa ≫ rb = t ≫ q) (K : DA) :
    (c₁ ra t).inv.app ((UCD q).obj ((UDA pb).obj K)) ≫
        (UAC (ra ≫ t)).map ((c₈ q pb).inv.app K) ≫ (c₉ (ra ≫ t) (q ≫ pb)).inv.app K ≫
        eqToHom (show (UAA ((ra ≫ t) ≫ q ≫ pb)).obj K = (UAA ((ra ≫ pa) ≫ rb ≫ pb)).obj K by
          simp only [Category.assoc, reassoc_of% w]) =
      (UAB ra).map (((c₃ t q).inv.app ((UDA pb).obj K) ≫
          eqToHom (show (UBD (t ≫ q)).obj ((UDA pb).obj K) =
            (UBD (pa ≫ rb)).obj ((UDA pb).obj K) by rw [w]) ≫
          (c₅ pa rb).hom.app ((UDA pb).obj K)) ≫ (UBA pa).map ((c₁₀ rb pb).inv.app K)) ≫
        (c₆ ra pa).inv.app ((UAA (rb ≫ pb)).obj K) ≫ (c₁₁ (ra ≫ pa) (rb ≫ pb)).inv.app K := by
  have T₁ : ∀ {g g' : B ⟶ D} (e : g = g') (M : DD),
      (UAB ra).map (eqToHom (show (UBD g).obj M = (UBD g').obj M by rw [e])) ≫
        (c₄ ra g').inv.app M =
      (c₄ ra g).inv.app M ≫ eqToHom (show (UAD (ra ≫ g)).obj M = (UAD (ra ≫ g')).obj M by
        rw [e]) := by
    intro g g' e M
    subst e
    simp
  have T₂ : ∀ {g g' : A ⟶ D} (e : g = g'),
      eqToHom (show (UAD g).obj ((UDA pb).obj K) = (UAD g').obj ((UDA pb).obj K) by rw [e]) ≫
        (c₁₂ g' pb).inv.app K =
      (c₁₂ g pb).inv.app K ≫ eqToHom (show (UAA (g ≫ pb)).obj K = (UAA (g' ≫ pb)).obj K by
        rw [e]) := by
    intro g g' e
    subst e
    simp
  have hn := (c₆ ra pa).inv.naturality ((c₁₀ rb pb).inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, H₂, reassoc_of% (H₄ ra pa rb), ← Functor.map_comp_assoc (UAB ra)
    ((c₅ pa rb).hom.app _), Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    reassoc_of% (T₁ w.symm), reassoc_of% H₁, reassoc_of% (H₃ ra t q)]
  simp only [eqToHom_trans, eqToHom_trans_assoc]
  rw [reassoc_of% (T₂ (show ra ≫ t ≫ q = (ra ≫ t) ≫ q by simp)),
    reassoc_of% (T₂ (show ra ≫ t ≫ q = (ra ≫ pa) ≫ rb by simp [w]))]
  simp

end CategoryTheory.PullbackFamily

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The relative pullback -/

section RelativePullback

variable {X X' X'' Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom] [IsSeparated X''.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *relative pullback* `Rf'_! ⟶ Lr^* ⋙ Rg_!` along a proper morphism `r : X ⟶ X'` over
`f' : X' ⟶ Y`, for `g = r ≫ f'`: the composite
```
Rf'_! M ⟶ Rf'_! Rr_* Lr^* M ≅ Rf'_! Rr_! Lr^* M ≅ R(r ≫ f')_! Lr^* M = Rg_! Lr^* M
```
of the unit of `Lr^* ⊣ Rr_*`, the identification `Rr_! ≅ Rr_*` and the composition isomorphism
of the lower shriek. It is the middle part of the Frobenius comparison of the lower shriek
(blueprint `sk-d-weil-push`); for `f'` the structure morphism of `X'` it is the pullback
`ProEtale.CondensedRing.compactPullback` on compactly supported cohomology. -/
noncomputable def relativePullback (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y) (g : X ⟶ Y)
    (h : r ≫ f' = g) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r).unit
      _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv _) ≫
    Functor.whiskerLeft _ ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv ≫
      eqToHom (by subst h; rfl))

lemma relativePullback_app (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y) (g : X ⟶ Y)
    (h : r ≫ f' = g) (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (relativePullback ℓ r f' g h).app M =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            r).unit.app M) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app _) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app _ ≫
        eqToHom (by subst h; rfl) := by
  simp only [relativePullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, eqToHom_app]

/-- The relative pullback for `g = r ≫ f'`, written with the unit of the adjunction
`Lr^* ⊣ Rr_!` of the proper morphism `r`. -/
lemma relativePullback_app_eq_unit (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y)
    (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (relativePullback ℓ r f' (r ≫ f') rfl).app M =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app _ := by
  simp only [relativePullback_app, boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc, eqToHom_refl, Category.comp_id]

/-- The relative pullback is natural in the coefficient complex. -/
@[reassoc]
lemma relativePullback_naturality (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y) (g : X ⟶ Y)
    (h : r ≫ f' = g) {M M' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : M ⟶ M') :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map a ≫
        (relativePullback ℓ r f' g h).app M' =
      (relativePullback ℓ r f' g h).app M ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).map a) :=
  (relativePullback ℓ r f' g h).naturality a

/-- **Compatibility of the relative pullbacks with composition**: `(r₁ ≫ r₂)^♯` is `r₂^♯`
followed by `r₁^♯` and the composition isomorphism `Lr₁^* Lr₂^* ≅ L(r₁ ≫ r₂)^*`. -/
lemma relativePullback_comp_app (r₁ : X ⟶ X') (r₂ : X' ⟶ X'') (f' : X'' ⟶ Y) (g₂ : X' ⟶ Y)
    (g : X ⟶ Y) (h₂ : r₂ ≫ f' = g₂) (h₁ : r₁ ≫ g₂ = g) [IsProper r₁.left] [IsProper r₂.left]
    [IsProper (r₁ ≫ r₂).left] (M : Dᵇc(X''.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (relativePullback ℓ (r₁ ≫ r₂) f' g (by rw [Category.assoc, h₂, h₁])).app M =
      (relativePullback ℓ r₂ f' g₂ h₂).app M ≫
        (relativePullback ℓ r₁ g₂ g h₁).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r₂).obj M) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r₁ r₂).inv.app
            M) := by
  subst h₂ h₁
  have key := compactPullback_comp_aux
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r₂)
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r₁)
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (r₁ ≫ r₂))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r₂)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r₁)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r₁ ≫ r₂))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r₁ r₂)
    (boundedConstructibleLowerStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r₁ r₂)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r₁ r₂)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r₂ f').symm
    ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r₁ (r₂ ≫ f')).symm)
    ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (r₁ ≫ r₂) f').symm ≪≫
      eqToIso (by rw [Category.assoc]))
    (fun K ↦ ?_) (fun P ↦ ?_) (fun P ↦ ?_) M
  · rw [relativePullback_app, relativePullback_app, relativePullback_app]
    simpa using key
  · have hu := unit_conjugateEquiv
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        (r₁ ≫ r₂))
      ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        r₂).comp
        (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r₁))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r₁ r₂).inv K
    rw [Adjunction.comp_unit_app, Category.assoc] at hu
    exact hu
  · exact boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ r₁ r₂ P
  · simp only [Iso.trans_inv, Iso.symm_inv, eqToIso.inv, NatTrans.comp_app, eqToHom_app,
      Category.assoc]
    rw [boundedConstructibleLowerShriekComp_padicAlgCl_assoc]
    simp

end RelativePullback

/-! ### Base change of the relative pullback -/

section BaseChange

variable {X X'a X'b X'ab Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'a.hom] [QuasiCompact X'a.hom]
  [IsSeparated X'a.hom] [LocallyOfFiniteType X'b.hom] [QuasiCompact X'b.hom]
  [IsSeparated X'b.hom] [LocallyOfFiniteType X'ab.hom] [QuasiCompact X'ab.hom]
  [IsSeparated X'ab.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

set_option maxHeartbeats 1000000 in
-- the instances of the categories of sheaves make the rewriting slow
/-- **Base change of the relative pullback** (blueprint `lem-trf-weil-shriek-iterates`, Step 2):
for cartesian squares `p ≫ r = t ≫ q` (with `r` and `t` proper) and `q ≫ f'' = f' ≫ a`, the
exchange `Ex_!` of the pasted rectangle carries `La^*(r^♯)` to `t^♯` composed with the exchange
of the lower square and the pullback comparison of the upper one. -/
lemma map_relativePullback_app_comp_baseChange_app {p : X'a ⟶ X} {t : X'a ⟶ X'ab} {r : X ⟶ X'b}
    {q : X'ab ⟶ X'b} {f' : X'ab ⟶ Y} {f'' : X'b ⟶ Y} {a : Y ⟶ Y} [IsProper r.left]
    [IsProper t.left] (hT : IsPullback p t r q) (hQ : IsPullback q f' f'' a)
    (M : Dᵇc(X'b.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).map
        ((relativePullback ℓ r f'' (r ≫ f'') rfl).app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hT.paste_vert hQ)).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hQ).app M ≫
      (relativePullback ℓ t f' (t ≫ f') rfl).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q).obj M) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (t ≫ f')).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          hT.toCommSq).hom.app M) := by
  have hV := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ hT hQ
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)
  have hn := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hQ).naturality
    ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app M)
  have hU := map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ hT M
  have hU' := congrArg (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
    hU
  have hc := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ t f').inv.naturality
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      hT.toCommSq).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hn hU' hc
  rw [relativePullback_app_eq_unit, relativePullback_app_eq_unit, hV]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f'').inv.app _), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hn, reassoc_of% hU', hc]

end BaseChange

/-! ### The Frobenius comparison through the relative pullback -/

section Comparison

variable {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]

/-- The Frobenius comparison `θ_f` is the compact-support base change of the cartesian square
followed by the relative pullback along the relative Frobenius `r` and the composition
isomorphism `Lr^* Lp^* ≅ L(r ≫ p)^* = LΦ_X^*`. -/
lemma weilLowerShriekFrobeniusComparison_hom_app_eq (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y)
    {p : X' ⟶ X} {f' : X' ⟶ Y} (sq : IsPullback p f' f ΦY) (r : X ⟶ X') (hrp : r ≫ p = ΦX)
    (hrf : r ≫ f' = f) [IsFinite r.left] [IsUniversalHomeomorphism r.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
        (relativePullback ℓ r f' f hrf).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K ≫
            eqToHom (by rw [hrp])) := by
  subst hrp hrf
  simp only [weilLowerShriekFrobeniusComparison, Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj, relativePullback_app, eqToHom_refl,
    Category.comp_id, Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id]

end Comparison

/-! ### Coherence of the composition isomorphisms of the pullbacks -/

section UpperStarCoherence

variable {W X X'a X'b X'ab Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom]
  [QuasiCompact W.hom] [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType X'a.hom] [QuasiCompact X'a.hom] [IsSeparated X'a.hom]
  [LocallyOfFiniteType X'b.hom] [QuasiCompact X'b.hom] [IsSeparated X'b.hom]
  [LocallyOfFiniteType X'ab.hom] [QuasiCompact X'ab.hom] [IsSeparated X'ab.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- Associativity of the inverses of the composition isomorphisms of the pullbacks. -/
@[reassoc]
lemma boundedConstructibleUpperStarComp_inv_app_comp_inv_app (f : W ⟶ X) (g : X ⟶ X'a)
    (h : X'a ⟶ Z) (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) h).inv.app K =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g h).inv.app K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f (g ≫ h)).inv.app K ≫
      eqToHom (by rw [Category.assoc]) := by
  have hA := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ f g h K
  rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
    (f ≫ g) h).hom.app K ≫ (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      f g).hom.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K))]
  conv_rhs => rw [hA]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app_assoc, eqToHom_trans, eqToHom_refl]

/-- Associativity of the inverses of the composition isomorphisms of the pullbacks, the other
way round. -/
@[reassoc]
lemma map_boundedConstructibleUpperStarComp_inv_app_comp_inv_app (f : W ⟶ X) (g : X ⟶ X'a)
    (h : X'a ⟶ Z) (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g h).inv.app K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f (g ≫ h)).inv.app K =
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) h).inv.app K ≫
      eqToHom (by rw [Category.assoc]) := by
  rw [boundedConstructibleUpperStarComp_inv_app_comp_inv_app_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- The coherence of the composition isomorphisms of the pullbacks needed for the composition
law of the Frobenius comparisons: for a commutative square `p_a ≫ r_b = t ≫ q`, the two
identifications of `Lr_a^* Lt^* Lq^* Lp_b^*` with the pullback along
`(r_a ≫ t) ≫ q ≫ p_b = (r_a ≫ p_a) ≫ r_b ≫ p_b` agree. -/
lemma boundedConstructibleUpperStarComp_relativeFrobenius_aux (ra : X ⟶ X'a)
    {pa : X'a ⟶ X} {t : X'a ⟶ X'ab} {rb : X ⟶ X'b} {q : X'ab ⟶ X'b} (w : CommSq pa t rb q)
    (pb : X'b ⟶ X) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ra t).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ pb).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (ra ≫ t)).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q pb).inv.app K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (ra ≫ t)
        (q ≫ pb)).inv.app K ≫
      eqToHom (by simp only [Category.assoc, reassoc_of% w.w]) =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ra).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          w).hom.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ pb).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ pa).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ rb pb).inv.app
            K)) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ra pa).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (rb ≫ pb)).obj K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (ra ≫ pa)
        (rb ≫ pb)).inv.app K := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app]
  exact CategoryTheory.PullbackFamily.comp_inv_app_coherence
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun f g h K ↦ map_boundedConstructibleUpperStarComp_inv_app_comp_inv_app ℓ f g h K)
    (fun f g h K ↦ map_boundedConstructibleUpperStarComp_inv_app_comp_inv_app ℓ f g h K)
    (fun f g h K ↦ boundedConstructibleUpperStarComp_inv_app_comp_inv_app ℓ f g h K)
    (fun f g h K ↦ boundedConstructibleUpperStarComp_inv_app_comp_inv_app ℓ f g h K) w.w K

end UpperStarCoherence

end AlgebraicGeometry.ProEtale.CondensedRing
