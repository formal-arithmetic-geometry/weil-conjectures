/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Square-zero algebra extensions with a specified kernel

Source: Stacks Project, Deformation Theory, Tags 0GPT and 0GPW
(blueprint: def-sfb-square-zero-algebra-extension).

The pushout and fibre-product predicates specify universal properties and actual
pairs of elements, respectively. They make no choice of an extension object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace Algebra.SquareZero

/-- An extension with specified kernel, quotient and quotient-module action.
Source: Stacks, Tag 0GPT (blueprint: def-sfb-square-zero-algebra-extension). -/
structure Extension (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right) where
  ring : CommRingCat.{u}
  base : a.left ⟶ ring
  projection : ring ⟶ a.right
  triangle : base ≫ projection = a.hom
  injection : M →+ ring
  injective : Function.Injective injection
  surjective : Function.Surjective projection
  exact : ∀ e : ring, projection e = 0 ↔ ∃ m : M, injection m = e
  square_zero : ∀ m n : M, injection m * injection n = 0
  action : ∀ (e : ring) (m : M), e * injection m = injection (projection e • m)

/-- A map of extensions inducing the displayed ring and additive kernel maps.
Its base equation says precisely that it is an algebra map over the common base.
Source: Stacks, Tag 0GPV (blueprint: def-sfb-square-zero-algebra-extension). -/
structure Hom {R A B : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ B}
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (E : Extension (Arrow.mk a) M) (F : Extension (Arrow.mk b) N)
    (f : A ⟶ B) (u : M →+ N) where
  map : E.ring ⟶ F.ring
  base : E.base ≫ map = F.base
  quotient : map ≫ F.projection = E.projection ≫ f
  kernel : ∀ m : M, map (E.injection m) = F.injection (u m)

/-- Isomorphism respecting the specified base, kernel and quotient.
Source: Stacks, Tag 0GPT (blueprint: def-sfb-square-zero-algebra-extension). -/
def IsIsomorphic {a : Arrow CommRingCat.{u}} {M : ModuleCat.{u} a.right}
    (E F : Extension a M) : Prop :=
  ∃ e : E.ring ≅ F.ring, E.base ≫ e.hom = F.base ∧
    e.hom ≫ F.projection = E.projection ∧
    ∀ m : M, e.hom (E.injection m) = F.injection m

/-- The split extension is exactly the existing trivial square-zero ring, with its
specified inclusions and projection. No splitting is assumed for other extensions.
Source: Stacks, Tag 0GPT (blueprint: def-sfb-square-zero-algebra-extension). -/
def IsSplit {a : Arrow CommRingCat.{u}} {M : ModuleCat.{u} a.right}
    (E : Extension a M) : Prop :=
  ∃ e : E.ring ≃+ TrivSqZeroExt a.right M,
    (∀ x y : E.ring, (e (x * y)).fst = (e x).fst * (e y).fst ∧
      (e (x * y)).snd = (e x).fst • (e y).snd + (e y).fst • (e x).snd) ∧
    (∀ r : a.left, e (E.base r) = TrivSqZeroExt.inl (a.hom r)) ∧
    (∀ m : M, e (E.injection m) = TrivSqZeroExt.inr m) ∧
    ∀ x : E.ring, (e x).fst = E.projection x

/-- Universal coefficient pushout, among extensions with the new specified kernel.
Source: Stacks, Tag 0GPW (blueprint: def-sfb-square-zero-algebra-extension). -/
def IsPushout {R A : CommRingCat.{u}} {a : R ⟶ A}
    {M N : ModuleCat.{u} A} (u : M ⟶ N)
    (E : Extension (Arrow.mk a) M) (F : Extension (Arrow.mk a) N) : Prop :=
  ∃ h : Hom E F (𝟙 A) u.hom.toAddMonoidHom,
    ∀ (G : Extension (Arrow.mk a) N) (k : Hom E G (𝟙 A) u.hom.toAddMonoidHom),
      ∃! l : Hom F G (𝟙 A) (AddMonoidHom.id N), h.map ≫ l.map = k.map

/-- The fibre product over the quotient, with the paired specified kernel. The
unique-pair property identifies the entire middle ring, not just its kernel.
Source: Stacks, Tag 0GPW (blueprint: def-sfb-square-zero-algebra-extension). -/
def IsFiberProduct {R A : CommRingCat.{u}} {a : R ⟶ A} {M : ModuleCat.{u} A}
    (E F : Extension (Arrow.mk a) M)
    (T : Extension (Arrow.mk a) (ModuleCat.of A (M × M))) : Prop :=
  ∃ (p : Hom T E (𝟙 A) (AddMonoidHom.fst M M))
    (q : Hom T F (𝟙 A) (AddMonoidHom.snd M M)),
    ∀ (e : E.ring) (f : F.ring), E.projection e = F.projection f →
      ∃! t : T.ring, p.map t = e ∧ q.map t = f

/-- Baer addition is the fibre product followed by pushout along kernel addition.
Source: Stacks, Tags 0GPU and 0GPW
(blueprint: def-sfb-square-zero-algebra-extension). -/
def IsBaerSum {R A : CommRingCat.{u}} {a : R ⟶ A} {M : ModuleCat.{u} A}
    (E F G : Extension (Arrow.mk a) M) : Prop :=
  ∃ T : Extension (Arrow.mk a) (ModuleCat.of A (M × M)),
    IsFiberProduct E F T ∧
      IsPushout (ModuleCat.ofHom (LinearMap.fst A M M + LinearMap.snd A M M)) T G

end Algebra.SquareZero
