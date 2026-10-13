/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.Paper.DerivedHomMayerVietoris
/-! # Quasi-coherent realization of a graded action

Source: Stacks Project, Tag 0897, relative-spectrum construction; Tags 01LX and 01SB.
(blueprint: lem-weil-pbc-graded-module-quasicoherent-realization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- A quasi-coherent graded action has a geometric realization, without a finiteness
assumption on its homogeneous generators, the algebra, or the base.

Source: Stacks Project, Tag 0897, relative-spectrum construction, using 01LX and 01SB.
(blueprint: lem-weil-pbc-graded-module-quasicoherent-realization).

Proof: On an affine open U = Spec C of X take the direct sum of the modules of
sections G_m(U). The internal decomposition of B extends the homogeneous maps mu
uniquely by finite sums to a B-action on this direct sum. Additivity of mu and its
multiplication law imply the module laws. The scalar formula identifies the A-action
with the action through A -> C; taking a = 1 gives the identity action. The commuting
C-action therefore extends to C tensor_A B. Quasi-coherence identifies restrictions
on affine basic opens with localization. Localization commutes with direct sums and
with the homogeneous action, so these local modules and actions agree on overlaps.
They glue to a quasi-coherent module over the pulled-back algebra sheaf. Relative
Spec base change identifies its spectrum with Y; affine module correspondence gives
F and an algebra-linear identification of its pushforward with that module. After
restriction of scalars, the homogeneous inclusions give the coproduct cocone iota.
On each affine open the action of b on the m-th summand is mu m k b, hence its
inclusion equals inclusion followed by multiplication by fB^sharp(b). Equality of
sheaf maps can be checked on the affine cover, giving the asserted global formula.
The construction uses no finite generators and works for zero summands and empty X. -/
theorem gradedModule_quasicoherent_realization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    ∃ (F : Y.Modules), F.IsQuasicoherent ∧
      ∃ (iota : ∀ m : ℕ, G m ⟶ (Scheme.Modules.pushforward pi).obj F),
        Nonempty (IsColimit (Cofan.mk ((Scheme.Modules.pushforward pi).obj F) iota)) ∧
          ∀ (k m : ℕ) (b : graded k),
            mu m k b ≫ iota (m + k) = iota m ≫
              (Scheme.Modules.pushforward pi).map
                (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val)) := by sorry

end AlgebraicGeometry
