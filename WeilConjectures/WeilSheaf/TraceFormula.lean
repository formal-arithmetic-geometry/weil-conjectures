/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.CompactlySupported

/-!

# The Grothendieck-Lefschetz trace formula

Let `X₀` be a scheme over a finite field `k` with structure morphism
`a_{X₀} : X₀ ⟶ Spec k`, let `s = Spec k̄` be the geometric point with its geometric
Frobenius `σ`, and let `X` be the geometric fiber with its geometric Frobenius `g_X`. For a
bounded below Weil complex `(K, Φ_K)` on `X` (`AlgebraicGeometry.WeilComplexPlus`), the
previous files of this folder equip the compactly supported cohomology `H_c^i(X, K)` with
the geometric Frobenius `F^i_{K,n}`. Following the reference (`reference.tex` in this
directory) this file builds the *local* side of the trace formula — the Frobenius
`F^j_{x,n}` on the cohomology of the derived stalk at a rational point — and states

`∑ᵢ (-1)ⁱ Tr(F^i_{K,n} ∣ H_c^i(X, K)) = ∑_{x ∈ X₀(F_(qⁿ))} ∑ⱼ (-1)ʲ Tr(F^j_{x,n} ∣ Hʲ(K_x̄))`

as `AlgebraicGeometry.WeilComplexPlus.trace_formula`. The two sides contain no
independently chosen Frobenius operators: every operator occurring in them is a functorial
image of the one coherent iterate `Φ_K^{[n]}` (`CategoryTheory.WeilObject.strIterate`) of
the single structure isomorphism `Φ_K`.

## The derived geometric stalk

On a separably closed point `Spec Ω` the derived global sections `RΓ(Spec Ω, -)` are
evaluation, so the derived geometric stalk at a geometric point `x̄ : Spec Ω ⟶ X` can be
*defined* as

`St_x̄ := RΓ(Spec Ω, L x̄^* -) : D⁺(X_ét, A) ⥤ D⁺(A)`

(`AlgebraicGeometry.Etale.derivedStalk`). This presentation makes the two natural
isomorphisms which the reference asks to be exposed explicitly available from the
composition constraints already in this project:

- the **pullback-stalk isomorphism** `St_x̄(L h^* -) ≅ St_{h x̄}(-)`
  (`AlgebraicGeometry.Etale.derivedStalkUpperStarIso`) is the derived form of
  `(x̄ ≫ h)^* ≅ h^* ⋙ x̄^*`, i.e. of `AlgebraicGeometry.Etale.upperStarComp`;
- the **point-reindexing isomorphism** `r_{x̄,τ} : St_{x̄ τ} ≅ St_x̄` for an automorphism `τ`
  of the source (`AlgebraicGeometry.Etale.derivedStalkReindexIso`) is the same composition
  constraint followed by the Frobenius invariance of derived global sections on the
  geometric point, `AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsPlusIso`
  — the `c_σ` already used for `RΓc`.

## The local Frobenius at a rational point

Fix `n` and let `L` be the subfield of `k̄` with `#k ^ n` elements, presented as a finite
extension `L` of `k` together with a chosen embedding `L ↪ k̄`. An `L`-rational point
`x : Spec L ⟶ X₀` (`AlgebraicGeometry.Scheme.Hom.fieldPoints`) has a canonical geometric
lift `x̄ : s ⟶ X` (`AlgebraicGeometry.Scheme.Hom.fieldPointGeometricLift`), and since the
`n`-th power of the geometric Frobenius of `k̄` fixes `L`
(`FiniteField.geometricFrobenius_pow_apply_of_pow_card`), this lift is `σⁿ`-equivariant:

`g_Xⁿ x̄ = x̄ σⁿ`

(`AlgebraicGeometry.Scheme.Hom.fieldPointGeometricLift_comp_geometricFrobeniusIterate`).
Iterating the pullback-stalk isomorphism through the intermediate translates of `x̄` and
then reindexing by `σⁿ` gives the **Frobenius trivialization**

`β_{x,n} : St_x̄ ∘ G_X^{[n]} ≅ St_x̄`

(`AlgebraicGeometry.Etale.fieldPointDerivedStalkFrobeniusIso`). Only after this
identification can a stalk of `Φ_K^{[n]}` be read as an endomorphism of the stalk, and the
local Frobenius `F_{x,n} := St_x̄(Φ_K^{[n]}) ∘ β_{x,n}⁻¹`
(`AlgebraicGeometry.WeilComplexPlus.localFrobenius`) be defined.

## The two alternating traces

Both sides are `finsum`s over `ℤ`, so no boundedness hypothesis enters the *statement*:
finiteness of the `H_c^i(X, K)` and of the stalk cohomology, and the vanishing of all but
finitely many of them, are theorems about the content of the formula. The global Frobenius
`F^i_{K,n}` is the `n`-th power (`CategoryTheory.WeilObject.autPow`) of the automorphism
produced by `AlgebraicGeometry.WeilComplexPlus.compactlySupportedCohomology`, which by the
coherence of the iterated Weil structure is the `n`-fold operator of the reference.

## Main definitions

- `AlgebraicGeometry.Etale.derivedStalk`: the derived geometric stalk `St_x̄`, with its
  `AlgebraicGeometry.Etale.derivedStalkUpperStarIso` and
  `AlgebraicGeometry.Etale.derivedStalkReindexIso`.
- `AlgebraicGeometry.specGeometricFrobeniusIterate` and
  `AlgebraicGeometry.Scheme.Hom.geometricFrobeniusIterate`: the iterates `σⁿ` and `g_Xⁿ`.
- `AlgebraicGeometry.Scheme.Hom.fieldPointGeometricLift`: the canonical geometric lift of a
  rational point.
- `AlgebraicGeometry.Etale.fieldPointDerivedStalkFrobeniusIso`: the trivialization
  `β_{x,n}`.
- `AlgebraicGeometry.WeilComplexPlus.localFrobenius` and
  `AlgebraicGeometry.WeilComplexPlus.localFrobeniusHomology`: the local geometric Frobenius
  `F_{x,n}` on the derived stalk and `F^j_{x,n}` on its cohomology.
- `CategoryTheory.WeilObject.autPow`: the `n`-th power of the automorphism of a Weil object
  for the identity endofunctor, i.e. the global Frobenius `F_{K,n}`.
- `AlgebraicGeometry.WeilComplexPlus.globalAlternatingTrace` and
  `AlgebraicGeometry.WeilComplexPlus.localAlternatingTrace`: the alternating traces
  `T_n(X, K)` and `t_{x,n}(K)`.

## Main statements

- `AlgebraicGeometry.WeilComplexPlus.trace_formula`: the Grothendieck-Lefschetz trace
  formula, for every iterate `n`. This is the deep geometric theorem the whole Weil layer
  is built to state; it is `sorry`ed here.

## Implementation notes

The point-counting form `#X₀(F_(qⁿ)) = ∑ᵢ (-1)ⁱ Tr(F^i ∣ H_c^i(X, Λ))` of the reference is
not stated here: it needs the constant complex `Λ_X` with the canonical Weil structure
coming from descent along `p_X : X ⟶ X₀`, together with the computation `t_{x,n}(Λ_X) = 1`
of its local terms, which is a further layer on top of the present one. The same holds for
the Frobenius at a closed point, `F_x := F_{x,d_x}` for `d_x = [κ(x) : k]`, which needs a
chosen embedding of the residue field into `k̄` and is used only in the theory of weights.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

/-! ### The derived geometric stalk -/

section Stalk

open Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The **derived geometric stalk** `St_x̄ : D⁺(X_ét, A) ⥤ D⁺(A)` at a geometric point
`x̄ : Spec Ω ⟶ X`, defined as the composite

`St_x̄ := RΓ(Spec Ω, L x̄^* -)`

of the derived pullback along `x̄` with the derived global sections of `Spec Ω`. Since `Ω`
is separably closed, `Spec Ω` has no nontrivial étale covers, so `RΓ(Spec Ω, -)` is
evaluation at the canonical geometric point and `St_x̄` is the derived functor of the
stalk. -/
def Etale.derivedStalk {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory.Plus A :=
  (x)^*[A].mapDerivedCategoryPlus ⋙ Etale.rightDerivedGlobalSectionsPlus A (Spec (.of Ω))

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The pullback-stalk isomorphism**: for `h : W ⟶ X` and a geometric point
`x̄ : Spec Ω ⟶ W`, there is a canonical natural isomorphism

`St_x̄(L h^* -) ≅ St_{h x̄}(-)`,

the derived form of the composition constraint `(x̄ ≫ h)^* ≅ h^* ⋙ x̄^*` of
`Etale.upperStarComp`. -/
def Etale.derivedStalkUpperStarIso {W X : Scheme.{u}} (h : W ⟶ X) (x : Spec (.of Ω) ⟶ W) :
    (h)^*[A].mapDerivedCategoryPlus ⋙ Etale.derivedStalk A x ≅
      Etale.derivedStalk A (x ≫ h) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryPlusCompIso (h)^*[A] (x)^*[A]).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A x h).symm) _

/-- **Reindexing a geometric point by an automorphism of its source**: for
`τ : Spec Ω ≅ Spec Ω` and a geometric point `x̄ : Spec Ω ⟶ X`, the geometric points `x̄ τ`
and `x̄` define canonically isomorphic points of the étale topos, giving a natural
isomorphism

`r_{x̄,τ} : St_{x̄ τ} ≅ St_x̄`.

Indeed `(τ ≫ x̄)^* ≅ x̄^* ⋙ τ^*` and derived global sections do not see `τ`, by
`Etale.upperStarCompRightDerivedGlobalSectionsPlusIso`. -/
def Etale.derivedStalkReindexIso {X : Scheme.{u}} (τ : Spec (.of Ω) ≅ Spec (.of Ω))
    (x : Spec (.of Ω) ⟶ X) :
    Etale.derivedStalk A (τ.hom ≫ x) ≅ Etale.derivedStalk A x :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A τ.hom x) ≪≫
        Functor.mapDerivedCategoryPlusCompIso (x)^*[A] (τ.hom)^*[A]) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.upperStarCompRightDerivedGlobalSectionsPlusIso A τ)

end Stalk

end AlgebraicGeometry

/-! ### Iterates of the geometric Frobenius -/

namespace FiniteField

variable (k : Type*) [Field k] [Finite k] (K : Type*) [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]

/-- An element of an algebraic extension of a finite field `k` which is fixed by the
`n`-th power of the arithmetic Frobenius, i.e. which satisfies `z ^ (#k ^ n) = z`, is
fixed by the `n`-th power of the geometric Frobenius. This is the field-theoretic input
for `AlgebraicGeometry.Scheme.Hom.fieldPointGeometricLift_comp_geometricFrobeniusIterate`:
the geometric Frobenius `σⁿ` of `Spec k̄` fixes `Spec F_(qⁿ)`. -/
theorem geometricFrobenius_pow_apply_of_pow_card (n : ℕ) (z : K)
    (hz : z ^ (Nat.card k ^ n) = z) : (geometricFrobenius k K ^ n) z = z := by
  let _ : Fintype k := Fintype.ofFinite k
  have hg : geometricFrobenius k K = (frobeniusAlgEquivOfAlgebraic k K).symm := rfl
  have h : geometricFrobenius k K ^ n = ((frobeniusAlgEquivOfAlgebraic k K) ^ n).symm := by
    simp only [hg, ← AlgEquiv.aut_inv, inv_pow]
  rw [h, AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ← Nat.card_eq_fintype_card]
  exact hz.symm

end FiniteField

namespace AlgebraicGeometry

open FiniteField Scheme

section FrobeniusIterate

variable (k : Type u) [Field k] [Finite k]

/-- The `n`-fold composite `σⁿ : Spec k̄ ≅ Spec k̄` of the geometric Frobenius of the
geometric point, defined so that `σ⁰ = 𝟙` and `σⁿ⁺¹ = σ ≫ σⁿ`. -/
def specGeometricFrobeniusIterate :
    ℕ → (Spec (.of (AlgebraicClosure k)) ≅ Spec (.of (AlgebraicClosure k)))
  | 0 => Iso.refl _
  | n + 1 => specGeometricFrobenius k ≪≫ specGeometricFrobeniusIterate n

@[simp]
lemma specGeometricFrobeniusIterate_zero :
    specGeometricFrobeniusIterate k 0 = Iso.refl _ := by
  simp [specGeometricFrobeniusIterate]

lemma specGeometricFrobeniusIterate_succ (n : ℕ) :
    specGeometricFrobeniusIterate k (n + 1) =
      specGeometricFrobenius k ≪≫ specGeometricFrobeniusIterate k n := by
  simp [specGeometricFrobeniusIterate]

/-- The `n`-fold geometric Frobenius of `Spec k̄` is the spectrum of the `n`-th power of
the geometric Frobenius of `k̄`. -/
lemma specGeometricFrobeniusIterate_hom (n : ℕ) :
    (specGeometricFrobeniusIterate k n).hom =
      Spec.map (CommRingCat.ofHom
        ((geometricFrobenius k (AlgebraicClosure k) ^ n :
            AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
          AlgebraicClosure k →+* AlgebraicClosure k)) := by
  induction n with
  | zero =>
    have h : CommRingCat.ofHom
        ((geometricFrobenius k (AlgebraicClosure k) ^ 0 :
            AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
          AlgebraicClosure k →+* AlgebraicClosure k) = 𝟙 _ := by
      ext x; simp
    rw [specGeometricFrobeniusIterate_zero, Iso.refl_hom, h, Spec.map_id]
  | succ n ih =>
    have h : CommRingCat.ofHom
        ((geometricFrobenius k (AlgebraicClosure k) ^ (n + 1) :
            AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
          AlgebraicClosure k →+* AlgebraicClosure k) =
        CommRingCat.ofHom
          ((geometricFrobenius k (AlgebraicClosure k) ^ n :
              AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
            AlgebraicClosure k →+* AlgebraicClosure k) ≫
          CommRingCat.ofHom
            ((geometricFrobenius k (AlgebraicClosure k) :
                AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
              AlgebraicClosure k →+* AlgebraicClosure k) := by
      ext x; simp [pow_succ']
    rw [specGeometricFrobeniusIterate_succ, Iso.trans_hom, ih, specGeometricFrobenius, h,
      Spec.map_comp]

/-- **The geometric Frobenius `σⁿ` fixes the subfield with `#k ^ n` elements**: for a
finite extension `L` of `k` with `#L = #k ^ n` embedded in `k̄`, the morphism
`π : Spec k̄ ⟶ Spec L` satisfies `σⁿ ≫ π = π`. -/
lemma specGeometricFrobeniusIterate_hom_comp_specMap_algebraMap (L : Type u) [Field L]
    [Finite L] [Algebra L (AlgebraicClosure k)] (n : ℕ) (hL : Nat.card L = Nat.card k ^ n) :
    (specGeometricFrobeniusIterate k n).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure k))) =
      Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure k))) := by
  let _ : Fintype L := Fintype.ofFinite L
  rw [specGeometricFrobeniusIterate_hom, ← Spec.map_comp]
  congr 1
  ext a
  refine geometricFrobenius_pow_apply_of_pow_card k _ n _ ?_
  rw [← map_pow, ← hL, Nat.card_eq_fintype_card, FiniteField.pow_card]

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The `n`-fold composite `g_Xⁿ : X ≅ X` of the geometric Frobenius of the geometric
fiber, defined so that `g_X⁰ = 𝟙` and `g_Xⁿ⁺¹ = g_X ≫ g_Xⁿ`. -/
def geometricFrobeniusIterate : ℕ → (f.geometricFiber ≅ f.geometricFiber)
  | 0 => Iso.refl _
  | n + 1 => f.geometricFrobenius ≪≫ geometricFrobeniusIterate n

@[simp]
lemma geometricFrobeniusIterate_zero : f.geometricFrobeniusIterate 0 = Iso.refl _ := by
  simp [geometricFrobeniusIterate]

lemma geometricFrobeniusIterate_succ (n : ℕ) :
    f.geometricFrobeniusIterate (n + 1) =
      f.geometricFrobenius ≪≫ f.geometricFrobeniusIterate n := by
  simp [geometricFrobeniusIterate]

/-- The iterated geometric Frobenius of the geometric fiber commutes with the projection
to the model: `p_X ∘ g_Xⁿ = p_X`. -/
@[reassoc (attr := simp)]
lemma geometricFrobeniusIterate_hom_proj (n : ℕ) :
    (f.geometricFrobeniusIterate n).hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  induction n with
  | zero => simp
  | succ n ih => rw [geometricFrobeniusIterate_succ, Iso.trans_hom, Category.assoc, ih,
      geometricFrobenius_hom_proj]

/-- The iterated geometric Frobenius of the geometric fiber is semilinear over `k̄`:
`a_X ∘ g_Xⁿ = σⁿ ∘ a_X`. -/
@[reassoc (attr := simp)]
lemma geometricFrobeniusIterate_hom_struct (n : ℕ) :
    (f.geometricFrobeniusIterate n).hom ≫ f.geometricFiberStruct =
      f.geometricFiberStruct ≫ (specGeometricFrobeniusIterate k n).hom := by
  induction n with
  | zero => simp
  | succ n ih => rw [geometricFrobeniusIterate_succ, Iso.trans_hom, Category.assoc, ih,
      geometricFrobenius_hom_struct_assoc, specGeometricFrobeniusIterate_succ, Iso.trans_hom]

end Scheme.Hom

end FrobeniusIterate

/-! ### Rational points and their canonical geometric lifts -/

section RationalPoint

open Scheme.Hom

/-- The morphism `π : Spec k̄ ⟶ Spec L` induced by a chosen embedding `L ↪ k̄` of an
extension `L` of the finite field `k` into the algebraic closure. -/
def specAlgebraicClosureOver (k : Type u) [Field k] [Finite k] (L : Type u) [Field L]
    [Algebra L (AlgebraicClosure k)] : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure k)))

/-- The chosen embedding of `L` into `k̄` is one of `k`-algebras: `π ≫ (Spec k̄ ⟶ Spec k)`
is the structure morphism of the geometric point. -/
lemma specAlgebraicClosureOver_comp (k : Type u) [Field k] [Finite k] (L : Type u) [Field L]
    [Algebra k L] [Algebra L (AlgebraicClosure k)] [IsScalarTower k L (AlgebraicClosure k)] :
    specAlgebraicClosureOver k L ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      specAlgebraicClosure k := by
  rw [specAlgebraicClosureOver, specAlgebraicClosure, ← Spec.map_comp]
  congr 1
  ext a
  exact (IsScalarTower.algebraMap_apply k L (AlgebraicClosure k) a).symm

variable {k : Type u} [Field k] [Finite k] (L : Type u) [Field L] [Algebra k L]
  [Algebra L (AlgebraicClosure k)] [IsScalarTower k L (AlgebraicClosure k)]
  {X₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k)}

/-- **The canonical geometric lift of a rational point**: an `L`-rational point
`x : Spec L ⟶ X₀` of `X₀` determines, together with the chosen embedding `L ↪ k̄` and its
morphism `π : Spec k̄ ⟶ Spec L`, the geometric point

`x̄ := (x ∘ π, id) : s ⟶ X = X₀ ×_{Spec k} s`

of the geometric fiber. -/
def Scheme.Hom.fieldPointGeometricLift (x : aX.fieldPoints L) :
    Spec (.of (AlgebraicClosure k)) ⟶ aX.geometricFiber :=
  pullback.lift (specAlgebraicClosureOver k L ≫ x.1) (𝟙 _) (by
    rw [Category.assoc, x.2, Category.id_comp]
    exact specAlgebraicClosureOver_comp k L)

@[reassoc (attr := simp)]
lemma Scheme.Hom.fieldPointGeometricLift_proj (x : aX.fieldPoints L) :
    fieldPointGeometricLift L x ≫ aX.geometricFiberProj =
      specAlgebraicClosureOver k L ≫ x.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.fieldPointGeometricLift_struct (x : aX.fieldPoints L) :
    fieldPointGeometricLift L x ≫ aX.geometricFiberStruct = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- **The geometric lift of an `F_(qⁿ)`-rational point is `σⁿ`-equivariant**:

`g_Xⁿ ∘ x̄ = x̄ ∘ σⁿ`.

This is the identity which lets a stalk of the `n`-fold iterated Weil structure be read as
an endomorphism of the stalk at `x̄`. It rests on the fact that the `n`-th power of the
geometric Frobenius of `k̄` fixes the subfield `L` with `#k ^ n` elements. -/
theorem Scheme.Hom.fieldPointGeometricLift_comp_geometricFrobeniusIterate [Finite L] (n : ℕ)
    (hL : Nat.card L = Nat.card k ^ n) (x : aX.fieldPoints L) :
    fieldPointGeometricLift L x ≫ (aX.geometricFrobeniusIterate n).hom =
      (specGeometricFrobeniusIterate k n).hom ≫ fieldPointGeometricLift L x := by
  refine pullback.hom_ext ?_ ?_
  · change (_ ≫ _) ≫ aX.geometricFiberProj = (_ ≫ _) ≫ aX.geometricFiberProj
    rw [Category.assoc, geometricFrobeniusIterate_hom_proj, fieldPointGeometricLift_proj,
      Category.assoc, fieldPointGeometricLift_proj, ← Category.assoc, specAlgebraicClosureOver,
      specGeometricFrobeniusIterate_hom_comp_specMap_algebraMap k L n hL]
  · change (_ ≫ _) ≫ aX.geometricFiberStruct = (_ ≫ _) ≫ aX.geometricFiberStruct
    rw [Category.assoc, geometricFrobeniusIterate_hom_struct, ← Category.assoc,
      fieldPointGeometricLift_struct, Category.id_comp, Category.assoc,
      fieldPointGeometricLift_struct, Category.comp_id]

end RationalPoint

/-! ### The local geometric Frobenius on the derived stalk -/

section LocalFrobenius

open Scheme.Hom Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k)}

/-- The `n`-fold Frobenius pullback is computed, on the stalk at a geometric point `x̄`, by
the stalk at the translated geometric point `g_Xⁿ x̄`:

`G_X^{[n]} ⋙ St_x̄ ≅ St_{g_Xⁿ x̄}`.

It is the `n`-fold iterate of the pullback-stalk isomorphism
`Etale.derivedStalkUpperStarIso`, the recursion running through the intermediate
translates of `x̄`. -/
def Etale.derivedStalkGeometricFrobeniusIterateIso :
    ∀ (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ aX.geometricFiber),
      ((Etale.frobeniusPullback A aX).mapDerivedCategoryPlus).iterate n ⋙
          Etale.derivedStalk A x ≅
        Etale.derivedStalk A (x ≫ (aX.geometricFrobeniusIterate n).hom)
  | 0, x =>
      Functor.leftUnitor _ ≪≫
        eqToIso (by rw [geometricFrobeniusIterate_zero, Iso.refl_hom, Category.comp_id])
  | n + 1, x =>
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (Etale.derivedStalkUpperStarIso A aX.geometricFrobenius.hom x) ≪≫
        derivedStalkGeometricFrobeniusIterateIso n (x ≫ aX.geometricFrobenius.hom) ≪≫
        eqToIso (by rw [geometricFrobeniusIterate_succ, Iso.trans_hom, Category.assoc])

variable (L : Type u) [Field L] [Finite L] [Algebra k L] [Algebra L (AlgebraicClosure k)]
  [IsScalarTower k L (AlgebraicClosure k)]

/-- **The rational-point Frobenius trivialization `β_{x,n}`**: for an `L`-rational point
`x` of `X₀`, with `#L = #k ^ n`, and its canonical geometric lift `x̄`, the natural
isomorphism

`β_{x,n} : St_x̄ ∘ G_X^{[n]} ≅ St_x̄`

obtained by composing the translation isomorphism
`Etale.derivedStalkGeometricFrobeniusIterateIso`, the `σⁿ`-equivariance
`g_Xⁿ x̄ = x̄ σⁿ` of the geometric lift, and the point-reindexing isomorphism
`Etale.derivedStalkReindexIso` for `σⁿ`. This is the identification which is missing
before a stalk of `Φ_K^{[n]}` can be read as an endomorphism of the stalk. -/
def Etale.fieldPointDerivedStalkFrobeniusIso (n : ℕ) (hL : Nat.card L = Nat.card k ^ n)
    (x : aX.fieldPoints L) :
    ((Etale.frobeniusPullback A aX).mapDerivedCategoryPlus).iterate n ⋙
        Etale.derivedStalk A (fieldPointGeometricLift L x) ≅
      Etale.derivedStalk A (fieldPointGeometricLift L x) :=
  Etale.derivedStalkGeometricFrobeniusIterateIso A n _ ≪≫
    eqToIso (congrArg (Etale.derivedStalk A)
      (fieldPointGeometricLift_comp_geometricFrobeniusIterate L n hL x)) ≪≫
    Etale.derivedStalkReindexIso A (specGeometricFrobeniusIterate k n) _

/-- **The local geometric Frobenius `F_{x,n}`** on the derived stalk of a bounded below
Weil complex `(K, Φ_K)` at the geometric lift `x̄` of an `L`-rational point `x`, for
`#L = #k ^ n`:

`K_x̄ --β_{x,n}⁻¹--> St_x̄(G_X^{[n]} K) --St_x̄(Φ_K^{[n]})--> K_x̄`.

It is an endomorphism of the derived stalk `K_x̄ = St_x̄(K)`, the functorial image of the
single coherent iterate `Φ_K^{[n]}` of the Weil structure; changing the embedding
`L ↪ k̄` changes it by conjugation, so its trace does not depend on that choice. -/
def WeilComplexPlus.localFrobenius (n : ℕ) (hL : Nat.card L = Nat.card k ^ n)
    (x : aX.fieldPoints L) (K : WeilComplexPlus A aX) :
    (Etale.derivedStalk A (fieldPointGeometricLift L x)).obj K.obj ⟶
      (Etale.derivedStalk A (fieldPointGeometricLift L x)).obj K.obj :=
  (Etale.fieldPointDerivedStalkFrobeniusIso A L n hL x).inv.app K.obj ≫
    (Etale.derivedStalk A (fieldPointGeometricLift L x)).map
      (WeilObject.strIterate K n).hom

/-- **The local geometric Frobenius on stalk cohomology**,
`F^j_{x,n} := Hʲ(F_{x,n}) : Hʲ(K_x̄) ⟶ Hʲ(K_x̄)`. -/
def WeilComplexPlus.localFrobeniusHomology (j : ℤ) (n : ℕ)
    (hL : Nat.card L = Nat.card k ^ n) (x : aX.fieldPoints L) (K : WeilComplexPlus A aX) :
    (DerivedCategory.Plus.homologyFunctor A j).obj
        ((Etale.derivedStalk A (fieldPointGeometricLift L x)).obj K.obj) ⟶
      (DerivedCategory.Plus.homologyFunctor A j).obj
        ((Etale.derivedStalk A (fieldPointGeometricLift L x)).obj K.obj) :=
  (DerivedCategory.Plus.homologyFunctor A j).map (K.localFrobenius A L n hL x)

end LocalFrobenius

end AlgebraicGeometry

/-! ### Traces -/

namespace CategoryTheory.WeilObject

variable {C : Type u} [Category.{u'} C]

/-- A Weil object for the *identity* endofunctor is an object `M` equipped with an
automorphism `Φ : M ≅ M`; this is the underlying endomorphism of `M`. -/
def aut (M : WeilObject (𝟭 C)) : End M.obj :=
  M.str.hom

/-- **The `n`-th Frobenius power `Φⁿ` of an object with an automorphism**. The transports
`AlgebraicGeometry.WeilComplexPlus.compactlySupportedGlobalSections` and
`AlgebraicGeometry.WeilComplexPlus.compactlySupportedCohomology` of a Weil complex land in
the category of objects with an automorphism, and their `autPow n` are the global Frobenius
operators `F_{K,n}` and `F^i_{K,n}` of the trace formula: by the coherence of the iterated
Weil structure these powers agree with the `n`-fold construction `Φ^[n]` of
`WeilObject.strIterate`. -/
def autPow (M : WeilObject (𝟭 C)) (n : ℕ) : End M.obj :=
  M.aut ^ n

@[simp]
lemma autPow_zero (M : WeilObject (𝟭 C)) : M.autPow 0 = 𝟙 M.obj :=
  pow_zero _

lemma autPow_succ (M : WeilObject (𝟭 C)) (n : ℕ) :
    M.autPow (n + 1) = M.aut ≫ M.autPow n :=
  pow_succ M.aut n

end CategoryTheory.WeilObject

namespace ModuleCat

/-- The trace of an endomorphism of an object of `ModuleCat Λ`. It is the trace of the
underlying `Λ`-linear endomorphism, hence `0` unless the module is finite free; finiteness
is therefore not part of the statement of the trace formula, only of its content. -/
def traceEnd {Λ : Type u'} [CommRing Λ] {M : ModuleCat.{u} Λ} (f : M ⟶ M) : Λ :=
  LinearMap.trace Λ M f.hom

end ModuleCat

namespace AlgebraicGeometry

section Trace

open Scheme.Hom Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k)}

/-- **The global alternating trace** `T_n(X, K)` of the `n`-th geometric Frobenius on the
compactly supported cohomology of a bounded below Weil complex:

`T_n(X, K) = ∑ᵢ (-1)ⁱ Tr(F^i_{K,n} ∣ H_c^i(X, K))`.

Every operator in this expression is constructed from the single structure isomorphism
`Φ_K` of the Weil complex, through
`AlgebraicGeometry.WeilComplexPlus.compactlySupportedCohomology`. The sum is a `finsum`:
it is the honest alternating sum as soon as only finitely many `H_c^i(X, K)` are nonzero,
and the individual traces vanish unless the `H_c^i(X, K)` are finite free; both are
theorems about the content of the formula, not part of its statement. -/
def WeilComplexPlus.globalAlternatingTrace (hΛ : IsAddTorsion Λ) (c₀ : Compactification aX)
    (n : ℕ) (K : WeilComplexPlus (ModuleCat.{u + 1} Λ) aX) : Λ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) •
    ModuleCat.traceEnd
      (((WeilComplexPlus.compactlySupportedCohomology Λ i hΛ c₀).obj K).autPow n)

variable (L : Type u) [Field L] [Finite L] [Algebra k L] [Algebra L (AlgebraicClosure k)]
  [IsScalarTower k L (AlgebraicClosure k)]

/-- **The local alternating term** `t_{x,n}(K)` at an `L`-rational point `x` of `X₀`, for
`#L = #k ^ n`:

`t_{x,n}(K) = ∑ⱼ (-1)ʲ Tr(F^j_{x,n} ∣ Hʲ(K_x̄))`.

Here `F^j_{x,n}` is the local geometric Frobenius
`AlgebraicGeometry.WeilComplexPlus.localFrobeniusHomology` on the cohomology of the derived
stalk at the canonical geometric lift `x̄` of `x`. As for the global trace the sum is a
`finsum`; it is finite because a bounded constructible `K` has only finitely many nonzero
stalk cohomology objects. -/
def WeilComplexPlus.localAlternatingTrace (n : ℕ) (hL : Nat.card L = Nat.card k ^ n)
    (x : aX.fieldPoints L) (K : WeilComplexPlus (ModuleCat.{u + 1} Λ) aX) : Λ :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
    ModuleCat.traceEnd
      (WeilComplexPlus.localFrobeniusHomology (ModuleCat.{u + 1} Λ) L j n hL x K)

/-- **The Grothendieck-Lefschetz trace formula, all iterates.**

Let `X₀` be a scheme of finite type over a finite field `k` admitting a compactification
`c₀` of its structure morphism `a_{X₀} : X₀ ⟶ Spec k`, let `X` be its geometric fiber and
let `(K, Φ_K)` be a bounded below Weil complex on `X` with coefficients in a torsion ring
`Λ`. Let `L` be the subfield of `k̄` with `#k ^ n` elements. Then

`∑ᵢ (-1)ⁱ Tr(F^i_{K,n} ∣ H_c^i(X, K)) = ∑_{x ∈ X₀(L)} ∑ⱼ (-1)ʲ Tr(F^j_{x,n} ∣ Hʲ(K_x̄))`.

The formula contains no independently chosen Frobenius operators: the global operator
`F^i_{K,n}` of `AlgebraicGeometry.WeilComplexPlus.globalAlternatingTrace` and every local
operator `F^j_{x,n}` of `AlgebraicGeometry.WeilComplexPlus.localAlternatingTrace` are
functorial images of the one coherent iterate `Φ_K^{[n]}` of the single structure
isomorphism `Φ_K`, through `Rf_!` and `RΓ` on the one side and through the derived
geometric stalk on the other. -/
theorem WeilComplexPlus.trace_formula (hΛ : IsAddTorsion Λ) (c₀ : Compactification aX)
    [QuasiCompact aX] [LocallyOfFiniteType aX] (n : ℕ) (hL : Nat.card L = Nat.card k ^ n)
    (K : WeilComplexPlus (ModuleCat.{u + 1} Λ) aX) :
    WeilComplexPlus.globalAlternatingTrace Λ hΛ c₀ n K =
      ∑ᶠ x : aX.fieldPoints L, WeilComplexPlus.localAlternatingTrace Λ L n hL x K :=
  sorry

end Trace

end AlgebraicGeometry

end

end
