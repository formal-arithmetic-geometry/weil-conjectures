/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# The iterated Frobenius operators of a Weil sheaf

Let `e : X ≅ X` be an automorphism. The trace formula for the `n`-th Frobenius, `n : ℕ`, uses the
power `eⁿ` of `e` (`CategoryTheory.Iso.pow e n`), defined like the power in a monoid by `e⁰ = 𝟙`
and `e^{n+1} = eⁿ ≫ e`. For a Weil sheaf `(F, φ_F)` of `ℚ̄_ℓ`-modules for `e`, the `n`-fold iterate
of its structure isomorphism makes `F` a Weil sheaf for `eⁿ`
(`ProEtale.CondensedRing.WeilSheaf.pow`):
```
φ_F^{(0)} : 𝟙^* F ≅ F,
φ_F^{(n+1)} : (eⁿ ≫ e)^* F ≅ (eⁿ)^* e^* F --(eⁿ)^* φ_F--> (eⁿ)^* F --φ_F^{(n)}--> F,
```
the first isomorphism being the identity isomorphism `ProEtale.CondensedRing.upperStarId` and the
second the composition isomorphism `ProEtale.CondensedRing.upperStarComp` of pullbacks on module
objects.

The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of the Weil sheaf `(F, φ_F^{(n)})` for
`eⁿ` (`ProEtale.CondensedRing.WeilSheaf.stalkFunctor`) is the stalk of `F` with its `n`-th
Frobenius operator. For `x̄` the geometric point over an `𝔽_{qⁿ}`-rational point this is the
action of the Frobenius of `𝔽_{qⁿ}` on the stalk.

## Main definitions

- `CategoryTheory.Iso.pow`: the power `eⁿ` of an automorphism.
- `CategoryTheory.Iso.powStr`: the iterated structure isomorphism `(P eⁿ) a ≅ a` for a family of
  endofunctors `P` contravariant in endomorphisms up to identity and composition isomorphisms.
- `ProEtale.CondensedRing.WeilSheaf.pow`: a Weil sheaf for `e` as a Weil sheaf for `eⁿ`.

## Implementation notes

The recursion is carried out in the generic `CategoryTheory.Iso.powStr` and only then
instantiated with the pullbacks on module objects: done directly on module objects, the kernel
times out while checking the recursive definition.

The coherence of `φ_F^{(n)}` with the iterated structure isomorphism
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate`, through the iterated composition isomorphism
`(eⁿ)^* ≅ (e^*)ⁿ`, and the identity relating `φ_F^{(n+m)}` to `φ_F^{(n)}` and `φ_F^{(m)}` up to
the composition isomorphisms, are not proved here.

-/

@[expose] public section

universe v u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] {X : C} (e : X ≅ X)

/-- The power `e.pow n = eⁿ` of an automorphism, defined recursively by `e⁰ = 𝟙` and
`e^{n+1} = eⁿ ≫ e`. -/
def pow (e : X ≅ X) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | n + 1 => pow e n ≪≫ e

@[simp]
lemma pow_zero : e.pow 0 = Iso.refl X :=
  rfl

lemma pow_succ (n : ℕ) : e.pow (n + 1) = e.pow n ≪≫ e :=
  rfl

@[simp]
lemma pow_one : e.pow 1 = e :=
  Iso.refl_trans e

@[simp]
lemma pow_refl (n : ℕ) : (Iso.refl X).pow n = Iso.refl X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, Iso.refl_trans]

/-- A morphism `s` with `e ≫ s = s` satisfies `eⁿ ≫ s = s`. -/
lemma pow_hom_comp_of_hom_comp {Y : C} {s : X ⟶ Y} (h : e.hom ≫ s = s) (n : ℕ) :
    (e.pow n).hom ≫ s = s := by
  induction n with
  | zero => exact Category.id_comp s
  | succ n ih => rw [pow_succ, Iso.trans_hom, Category.assoc, h, ih]

/-- The iterated structure isomorphism `(P eⁿ) a ≅ a` of an object `a` with an isomorphism
`φ : P e a ≅ a`, for a family of endofunctors `P g` indexed by the endomorphisms `g` of `X`,
contravariant up to an identity isomorphism `P 𝟙 ≅ 𝟭` and the composition isomorphisms
`P (f ≫ g) ≅ P g ⋙ P f`: it is the identity isomorphism at `a` for `n = 0`, and the composite
`P (eⁿ ≫ e) a ≅ P eⁿ (P e a) ≅ P eⁿ a ≅ a` of the composition isomorphism, `P eⁿ φ` and the
iterated structure isomorphism for `n`. -/
noncomputable def powStr {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (id : P (𝟙 X) ≅ 𝟭 D) (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D}
    (φ : (P e.hom).obj a ≅ a) : ∀ n : ℕ, (P (e.pow n).hom).obj a ≅ a
  | 0 => id.app a
  | n + 1 =>
    (comp (e.pow n).hom e.hom).app a ≪≫ (P (e.pow n).hom).mapIso φ ≪≫ powStr P id comp φ n

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X : Over (Spec (.of k))} {e : X ≅ X}

/-- A Weil sheaf `(F, φ_F)` for `e` as a Weil sheaf for `eⁿ`, with the iterated structure
isomorphism `φ_F^{(n)} : (eⁿ)^* F ≅ F`: `φ_F^{(0)}` is the identity isomorphism `upperStarId`
and `φ_F^{(n+1)}` is the composite `(eⁿ ≫ e)^* F ≅ (eⁿ)^* e^* F ≅ (eⁿ)^* F ≅ F` of the composition
isomorphism `upperStarComp`, `(eⁿ)^* φ_F` and `φ_F^{(n)}`. -/
noncomputable def WeilSheaf.pow (F : WeilSheaf ℓ e) (n : ℕ) : WeilSheaf ℓ (e.pow n) :=
  IsoAlgebra.mk F.carrier
    (e.powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) F.str n)

end AlgebraicGeometry.ProEtale.CondensedRing
