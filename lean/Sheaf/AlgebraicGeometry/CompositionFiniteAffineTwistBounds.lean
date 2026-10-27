/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.AmpleIso

/-! # Finite affine covers with eventual local ample-twist bounds

Source: Stacks Project, Morphisms, Tag 0C4K, finite affine-cover reduction,
and Tag 0892(1), with finite-type permanence in Tags 01T3 and 01T4.
(blueprint: lem-sfb-composition-finite-affine-twist-bounds).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite-type morphisms with the stated relative ampleness conditions admit a finite
base affine cover with eventual ample-twist bounds on every inverse-image piece.
Here `Y_i = g ⁻¹ᵁ V i`, `X_i = f ⁻¹ᵁ (g ⁻¹ᵁ V i)`, and `f_i = f ∣_ (g ⁻¹ᵁ V i)`.
The open `X_i` is also the inverse image under `f ≫ g`. Pullback along each open inclusion
is restriction, so every module displayed is the specified restriction of `L` or `M`.
The bounds are nonnegative integers, hence `a.toNat` denotes exactly the required exponent.
The zeroth tensor power is the structure module. `Fin r` allows the empty cover.
Existential invertibility witnesses only supply the proof argument of `IsAmple`.

Source: Stacks Project, Morphisms, Tag 0C4K, finite affine-cover reduction;
Tag 0892(1); finite type in Tags 01T3 and 01T4; relative ampleness in Definition 01VH.
(blueprint: lem-sfb-composition-finite-affine-twist-bounds).

Proof:
1. By lem-sfb-finite-type-composition-base-change(1), the composite is finite type,
hence quasi-compact by def-weil-finite-type-morphism. Choose a finite affine cover of `S`
using lem-weil-pbc-qcqs-finite-affine-open-cover and enumerate it by `Fin r`. If `S` is
empty use `r = 0`; all assertions indexed by the cover are then vacuous.
2. On each piece, inverse images under a composite give `X_i = f⁻¹(Y_i)`. The canonical
restricted map `f_i` is the base change of `f` along the open inclusion `Y_i ⟶ Y`.
Apply lem-sfb-finite-type-composition-base-change(2) to obtain its finite type, which
includes quasi-compactness by def-weil-finite-type-morphism.
3. Restrict rank-one local trivializations to show that `L_i` and `M_i` are invertible
(def-sc-invertible-module). Since `V_i` is affine, the hypothesis on `M` gives ampleness
of `M_i`. Every affine open of `Y_i` is also affine open in `Y`; restricting `L_i`
above it is the same as restricting `L`. Thus the hypothesis on `L` gives the stated
relative ampleness of `L_i` for `f_i`.
4. Apply lem-sfb-relative-ample-absolute-twist to `f_i`, `L_i`, and `M_i`, using the
quasi-compactness in step 2 and all ampleness and invertibility assertions in step 3.
It supplies a nonnegative integer bound `a_i` valid for every integer `a ≥ a_i`.
Choose these bounds for each of the finitely many indices. -/
theorem exists_finite_affine_cover_eventually_isAmple_tensorPullback
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace S]
    (L : X.Modules) (M : Y.Modules) [L.IsInvertible] [M.IsInvertible]
    (hL : ∀ W : Y.Opens, IsAffineOpen W →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ W).ι).obj L).IsInvertible,
        @IsAmple (f ⁻¹ᵁ W).toScheme ((tensorPullback (f ⁻¹ᵁ W).ι).obj L) h)
    (hM : ∀ V : S.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (g ⁻¹ᵁ V).ι).obj M).IsInvertible,
        @IsAmple (g ⁻¹ᵁ V).toScheme ((tensorPullback (g ⁻¹ᵁ V).ι).obj M) h) :
    LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧
      ∃ (r : ℕ) (V : Fin r → S.Opens),
        (∀ i : Fin r, IsAffineOpen (V i)) ∧ (⨆ i : Fin r, V i) = ⊤ ∧
        ∀ i : Fin r,
          LocallyOfFiniteType (f ∣_ (g ⁻¹ᵁ V i)) ∧ QuasiCompact (f ∣_ (g ⁻¹ᵁ V i)) ∧
          ((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L).IsInvertible ∧
          ∃ hMi : ((tensorPullback (g ⁻¹ᵁ V i).ι).obj M).IsInvertible,
            (∀ W : (g ⁻¹ᵁ V i).toScheme.Opens, IsAffineOpen W →
              ∃ h : ((tensorPullback ((f ∣_ (g ⁻¹ᵁ V i)) ⁻¹ᵁ W).ι).obj
                ((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L)).IsInvertible,
                @IsAmple ((f ∣_ (g ⁻¹ᵁ V i)) ⁻¹ᵁ W).toScheme
                  ((tensorPullback ((f ∣_ (g ⁻¹ᵁ V i)) ⁻¹ᵁ W).ι).obj
                    ((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L)) h) ∧
            @IsAmple (g ⁻¹ᵁ V i).toScheme ((tensorPullback (g ⁻¹ᵁ V i).ι).obj M) hMi ∧
            ∃ a₀ : ℤ, 0 ≤ a₀ ∧ ∀ a : ℤ, a₀ ≤ a →
              ∃ h : (tensorObj ((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L)
                ((tensorPullback (f ∣_ (g ⁻¹ᵁ V i))).obj
                  (((tensorPullback (g ⁻¹ᵁ V i).ι).obj M).tensorPow a.toNat))).IsInvertible,
                @IsAmple (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).toScheme
                  (tensorObj ((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L)
                    ((tensorPullback (f ∣_ (g ⁻¹ᵁ V i))).obj
                      (((tensorPullback (g ⁻¹ᵁ V i).ι).obj M).tensorPow a.toNat))) h := by
  classical
  refine ⟨inferInstance, inferInstance, ?_⟩
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : S.Opens))).mp
      isCompact_univ
  let : Fintype s := hs.fintype
  let e := (Fintype.equivFin s).symm
  let V : Fin (Fintype.card s) → S.Opens := fun i ↦ (e i).1.1
  have hV : ∀ i, IsAffineOpen (V i) := fun i ↦ (e i).1.2
  have hcov : (⨆ i, V i) = ⊤ := by
    rw [hcover]
    calc
      (⨆ i, V i) = ⨆ i : s, i.1.1 :=
        e.surjective.iSup_comp (fun i : s ↦ i.1.1)
      _ = ⨆ i ∈ s, i.1 := iSup_subtype
  refine ⟨Fintype.card s, V, hV, hcov, fun i ↦ ?_⟩
  let U := g ⁻¹ᵁ V i
  have : LocallyOfFiniteType (f ∣_ U) := by
    unfold morphismRestrict
    infer_instance
  have : QuasiCompact (f ∣_ U) := by
    unfold morphismRestrict
    infer_instance
  have : ((tensorPullback (f ⁻¹ᵁ U).ι).obj L).IsInvertible :=
    ((invertible_pullback_tensor (f ⁻¹ᵁ U).ι).1 L).2
  obtain ⟨hMi, hMamp⟩ := hM (V i) (hV i)
  have := hMi
  have hLi : ∀ W : U.toScheme.Opens, IsAffineOpen W →
      ∃ h : ((tensorPullback ((f ∣_ U) ⁻¹ᵁ W).ι).obj
        ((tensorPullback (f ⁻¹ᵁ U).ι).obj L)).IsInvertible,
        @IsAmple ((f ∣_ U) ⁻¹ᵁ W).toScheme
          ((tensorPullback ((f ∣_ U) ⁻¹ᵁ W).ι).obj
            ((tensorPullback (f ⁻¹ᵁ U).ι).obj L)) h := by
    intro W hW
    let W' := U.ι ''ᵁ W
    obtain ⟨hLW, hLamp⟩ := hL W' (hW.image_of_isOpenImmersion U.ι)
    have := hLW
    let A := (f ∣_ U) ⁻¹ᵁ W
    let j : A.toScheme ⟶ (f ⁻¹ᵁ W').toScheme :=
      ((f ⁻¹ᵁ U).ι.isoImage A ≪≫
        X.isoOfEq (image_morphismRestrict_preimage f U W)).hom
    have hj : j ≫ (f ⁻¹ᵁ W').ι = A.ι ≫ (f ⁻¹ᵁ U).ι := by
      simp [j, W', A]
    have : IsIso j := by dsimp [j]; infer_instance
    have : ((tensorPullback j).obj
        ((tensorPullback (f ⁻¹ᵁ W').ι).obj L)).IsInvertible :=
      ((invertible_pullback_tensor j).1 _).2
    have ha := isAmple_tensorPullback_of_isAffineHom j _ hLamp
    obtain ⟨c⟩ := nonempty_tensorPullbackComp j (f ⁻¹ᵁ W').ι
    obtain ⟨d⟩ := nonempty_tensorPullbackComp A.ι (f ⁻¹ᵁ U).ι
    let b := (c.app L).symm ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj L) hj) ≪≫ d.app L
    change (tensorPullback j).obj ((tensorPullback (f ⁻¹ᵁ W').ι).obj L) ≅
      (tensorPullback A.ι).obj ((tensorPullback (f ⁻¹ᵁ U).ι).obj L) at b
    have hb : ((tensorPullback A.ι).obj
        ((tensorPullback (f ⁻¹ᵁ U).ι).obj L)).IsInvertible := IsInvertible.of_iso b
    exact ⟨hb, (isAmple_iff_of_iso b).mp ha⟩
  exact ⟨inferInstance, inferInstance, inferInstance, hMi, hLi, hMamp,
    isAmple_tensorPullback_tensorPow_of_relative (f ∣_ U) _ _ hLi hMamp⟩

end AlgebraicGeometry.Scheme.Modules
