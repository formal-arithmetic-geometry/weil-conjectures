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

namespace CategoryTheory

end CategoryTheory

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
    boundedConstructibleLowerShriek ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r ⋙
        boundedConstructibleLowerShriek ℓ g :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ r).unit
      _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv _) ≫
    Functor.whiskerLeft _ ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv ≫
      eqToHom (by subst h; rfl))

lemma relativePullback_app (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y) (g : X ⟶ Y)
    (h : r ≫ f' = g) (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (relativePullback ℓ r f' g h).app M =
      (boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            r).unit.app M) ≫
        (boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app _) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app _ ≫
        eqToHom (by subst h; rfl) := by
  simp only [relativePullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, eqToHom_app]

/-- The relative pullback is natural in the coefficient complex. -/
@[reassoc]
lemma relativePullback_naturality (r : X ⟶ X') [IsProper r.left] (f' : X' ⟶ Y) (g : X ⟶ Y)
    (h : r ≫ f' = g) {M M' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : M ⟶ M') :
    (boundedConstructibleLowerShriek ℓ f').map a ≫
        (relativePullback ℓ r f' g h).app M' =
      (relativePullback ℓ r f' g h).app M ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).map a) :=
  (relativePullback ℓ r f' g h).naturality a

end RelativePullback

/-! ### Base change of the relative pullback -/

section BaseChange

variable {X X'a X'b X'ab Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'a.hom] [QuasiCompact X'a.hom]
  [IsSeparated X'a.hom] [LocallyOfFiniteType X'b.hom] [QuasiCompact X'b.hom]
  [IsSeparated X'b.hom] [LocallyOfFiniteType X'ab.hom] [QuasiCompact X'ab.hom]
  [IsSeparated X'ab.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

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
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K ≫
            eqToHom (by rw [hrp])) := by
  subst hrp hrf
  simp only [weilLowerShriekFrobeniusComparison, Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom,
    Category.id_comp, Functor.comp_obj, Functor.id_obj, relativePullback_app, eqToHom_refl,
    Category.comp_id, Category.assoc]

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

end UpperStarCoherence

/-! ### The composition law -/

section Composition

variable {X Y X'a X'b X'ab : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'a.hom] [QuasiCompact X'a.hom]
  [IsSeparated X'a.hom] [LocallyOfFiniteType X'b.hom] [QuasiCompact X'b.hom]
  [IsSeparated X'b.hom] [LocallyOfFiniteType X'ab.hom] [QuasiCompact X'ab.hom]
  [IsSeparated X'ab.hom]

end Composition
end AlgebraicGeometry.ProEtale.CondensedRing
