/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Signed double-cone interchange for endomorphism fibres

Source: blueprint main-20261015, derived Nakayama first reduction, Cones paragraph;
Stacks Tags 014E, 014Q and 011G (blueprint: lem-pe-endomorphism-fibre-double-cone).

All coordinates below are projection morphisms in an arbitrary abelian category.
The fibre is Mathlib's actual mapping cocone, with its reordered coordinates (v,u).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex.EndomorphismFibreDoubleCone

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- The diagonal endomorphism of the cone, using the existing strict cone map.
Source: Stacks 014E; blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable abbrev coneEnd {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCone f ⟶ mappingCone f :=
  mappingCone.map f f s t h.symm

/-- The diagonal fibre map is the existing map of mapping cocones.
Source: Stacks 014E and 011G; blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable abbrev fibreMap {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCocone s ⟶ mappingCocone t :=
  (mappingCone.map s t f f h)⟦(-1 : ℤ)⟧'

/-- The specified signed shift sigma_1(v,u)=(v,-u) of the endomorphism fibre.
This is the negative of the inverse cone shift, shifted by -1, followed by the
canonical commutation of shifts. The inverse cone shift scales the source summand
by -1 and the target summand by 1. These are the first and second fibre summands,
so its negative has coefficients (1,-1) in fibre order (v,u).
Source: Stacks 011G (shift of cochain complexes) and 014E (mapping cone);
blueprint Cones paragraph (blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable def sigmaOne {A : CochainComplex D ℤ} (s : A ⟶ A) :
    mappingCocone (s⟦(1 : ℤ)⟧') ≅ (mappingCocone s)⟦(1 : ℤ)⟧ :=
  (1 : ℤ).negOnePow •
    ((CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-1 : ℤ)).mapIso
        (mappingCone.shiftIso s 1).symm ≪≫
      (shiftFunctorComm (CochainComplex D ℤ) (1 : ℤ) (-1 : ℤ)).app (mappingCone s))

/-- The four projections specifying Phi(b,a,b',a')=(b,b',a,-a').
Source: Stacks 014E, 014Q and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def Formula {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (e : mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h)) : Prop :=
  ∀ q : ℤ,
    (e.hom.f q ≫ (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.fst t).f q =
      (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.snd f).v q q (add_zero q)) ∧
    (e.hom.f q ≫ (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.snd t).v q (q - 1) (by omega) =
      (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.snd f).v (q - 1) (q - 1) (add_zero _)) ∧
    (e.hom.f q ≫ (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.fst s).f (q + 1) =
      (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.fst f).1.v q (q + 1) rfl) ∧
    (e.hom.f q ≫ (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.snd s).v (q + 1) q (by omega) =
      -((mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.fst f).1.v (q - 1) q (by omega)))

/-- The four projections specifying Psi(b,b',a,h)=(b,a,b',-h).
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def InverseFormula {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (e : mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h)) : Prop :=
  ∀ q : ℤ,
    (e.inv.f q ≫ (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.snd f).v q q (add_zero q) =
      (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.fst t).f q) ∧
    (e.inv.f q ≫ (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.fst f).1.v q (q + 1) rfl =
      (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.fst s).f (q + 1)) ∧
    (e.inv.f q ≫ (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.snd f).v (q - 1) (q - 1) (add_zero _) =
      (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.snd t).v q (q - 1) (by omega)) ∧
    (e.inv.f q ≫ (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.fst f).1.v (q - 1) q (by omega) =
      -((mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.snd s).v (q + 1) q (by omega)))

/-- The zero-second-coordinate condition on the strict augmentation eta_J=(J,0).
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def Augmentation {M A : CochainComplex D ℤ} (s : A ⟶ A) (J : M ⟶ A)
    (η : M ⟶ mappingCocone s) : Prop :=
  η ≫ mappingCocone.fst s = J ∧
    ∀ q : ℤ, η.f q ≫ (mappingCocone.snd s).v q (q - 1) (by omega) = 0

/-- The signed interchange, its naturality, triangle identities and augmentation identity.

Source: blueprint main-20261015, derived Nakayama first reduction, Cones paragraph;
Stacks 014E, 014Q and 011G (blueprint: lem-pe-endomorphism-fibre-double-cone).

Proof:
1. Finite biproducts and bilinear composition (def-sp-abelian) give the fibre differential
   (dv,-du-sv); its square vanishes since s commutes with d. Intertwining maps act
   diagonally. The relation fs=tf makes c=diag(t,s) a chain endomorphism of Cone(f).
2. Expand cones and shifts (def-weil-abstract-derived-category). The source differential
   is (db+fa,-da,-db'-fa'-tb,da'-sa); the target differential on (b,b',a,h) is
   (db+fa,-db'-tb+fh,-da,dh+sa). The signed permutation intertwines them.
3. The inverse permutation (b,b',a,h) maps to (b,a,b',-h); both composites are identities
   by the biproduct equations. Strict squares act diagonally, so commute with Phi.
4. The signed shift is (v,u) maps to (v,-u). Inclusion gives (b,b',0,0) on both
   routes. The negative boundary followed by the signed shift gives (-a,a'), exactly
   the negative target boundary after Phi. These also verify the intertwining equations
   needed to form the two fibre maps.
5. Since sJ=tJ'=0, (J,0) and (J',0) commute with the fibre differentials. The square
   fJ=J'g makes the diagonal cone map J_C a chain map, with cJ_C=0; hence (J_C,0)
   is a chain map as well. Diagonal maps give the square of the two augmentations.
6. Applying Phi to (J'm',Jm,0,0) gives (J'm',0,Jm,0), exactly the cone map of the
   augmentations. All identities are finite biproduct projection calculations, with no
   boundedness, products or surjectivity assumptions. -/
theorem exists_interchange :
    ∃ e : ∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h),
    (∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      Formula s t f h (e s t f h) ∧ InverseFormula s t f h (e s t f h)) ∧
    (∀ {A B A' B' : CochainComplex D ℤ}
      (s : A ⟶ A) (t : B ⟶ B) (s' : A' ⟶ A') (t' : B' ⟶ B')
      (f : A ⟶ B) (f' : A' ⟶ B') (h : s ≫ f = f ≫ t) (h' : s' ≫ f' = f' ≫ t')
      (α : A ⟶ A') (β : B ⟶ B') (hα : s ≫ α = α ≫ s')
      (hβ : t ≫ β = β ≫ t') (hsq : f ≫ β = α ≫ f'),
      ∃ (hc : coneEnd s t f h ≫ mappingCone.map f f' α β hsq =
          mappingCone.map f f' α β hsq ≫ coneEnd s' t' f' h')
        (hk : fibreMap s t f h ≫ fibreMap t t' β hβ =
          fibreMap s s' α hα ≫ fibreMap s' t' f' h'),
      fibreMap (coneEnd s t f h) (coneEnd s' t' f' h')
          (mappingCone.map f f' α β hsq) hc ≫ (e s' t' f' h').hom =
        (e s t f h).hom ≫ mappingCone.map (fibreMap s t f h) (fibreMap s' t' f' h')
          (fibreMap s s' α hα) (fibreMap t t' β hβ) hk) ∧
    (∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      ∃ (hi : t ≫ mappingCone.inr f = mappingCone.inr f ≫ coneEnd s t f h)
        (hp : coneEnd s t f h ≫ (mappingCone.triangle f).mor₃ =
          (mappingCone.triangle f).mor₃ ≫ s⟦(1 : ℤ)⟧'),
      (fibreMap t (coneEnd s t f h) (mappingCone.inr f) hi ≫ (e s t f h).hom =
        mappingCone.inr (fibreMap s t f h)) ∧
      (fibreMap (coneEnd s t f h) (s⟦(1 : ℤ)⟧') (mappingCone.triangle f).mor₃ hp ≫
          (sigmaOne s).hom =
        (e s t f h).hom ≫ (mappingCone.triangle (fibreMap s t f h)).mor₃)) ∧
    (∀ {A B M M' : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t) (g : M ⟶ M') (J : M ⟶ A) (J' : M' ⟶ B),
      J ≫ s = 0 → J' ≫ t = 0 → ∀ hJ : J ≫ f = g ≫ J',
      ∃ (η : M ⟶ mappingCocone s) (η' : M' ⟶ mappingCocone t)
        (ηC : mappingCone g ⟶ mappingCocone (coneEnd s t f h)),
      Augmentation s J η ∧ Augmentation t J' η' ∧
      Augmentation (coneEnd s t f h) (mappingCone.map g f J J' hJ.symm) ηC ∧
      ∃ hs : g ≫ η' = η ≫ fibreMap s t f h,
        ηC ≫ (e s t f h).hom =
          mappingCone.map g (fibreMap s t f h) η η' hs) := by
  sorry

end CochainComplex.EndomorphismFibreDoubleCone
