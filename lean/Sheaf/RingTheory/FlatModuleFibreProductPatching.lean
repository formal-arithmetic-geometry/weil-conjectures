/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Tensor

/-!
# Flat module patching over a surjective ring fibre product

Source: Stacks Project, More on Algebra, Situation 08KH and Lemma 0D2I (1), (2)
(blueprint: lem-sfb-flat-module-fibre-product-patching).

Scalar extension is Mathlib's `ModuleCat.extendScalars`, hence tensor product.
For a surjection q, extension along q is canonically M'/ker(q)M'.
The ring and module pullbacks are categorical pullbacks, canonically the
coordinatewise fibre products in the statement. The reconstruction isomorphism
is characterized by its two unit maps, so it specifies the canonical map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.FibreProductPatching

/-- The left map to the common reduction, restricted to the ring fibre product.
Source: Stacks Project, Situation 08KH, the map n ↦ φ(n ⊗ 1)
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def leftMap
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (N : ModuleCat.{max u v} B) (M' : ModuleCat.{max u v} A')
    (φ : (extendScalars b.hom).obj N ≅ (extendScalars q.hom).obj M') :
    (restrictScalars (pullback.fst b q).hom).obj N ⟶
      (restrictScalars ((pullback.fst b q) ≫ b).hom).obj
        ((extendScalars q.hom).obj M') :=
  (restrictScalars (pullback.fst b q).hom).map
      ((extendRestrictScalarsAdj b.hom).unit.app N) ≫
    (restrictScalarsComp'App (pullback.fst b q).hom b.hom
      ((pullback.fst b q) ≫ b).hom rfl _).inv ≫
    (restrictScalars ((pullback.fst b q) ≫ b).hom).map φ.hom

/-- The right quotient map to the common reduction, with the same scalar action.
Source: Stacks Project, Situation 08KH, the map M' → M'/IM'
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def rightMap
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (M' : ModuleCat.{max u v} A') :
    (restrictScalars (pullback.snd b q).hom).obj M' ⟶
      (restrictScalars ((pullback.fst b q) ≫ b).hom).obj
        ((extendScalars q.hom).obj M') :=
  (restrictScalars (pullback.snd b q).hom).map
      ((extendRestrictScalarsAdj q.hom).unit.app M') ≫
    (restrictScalarsComp'App (pullback.snd b q).hom q.hom
      ((pullback.fst b q) ≫ b).hom
      (congrArg CommRingCat.Hom.hom (pullback.condition (f := b) (g := q))) _).inv

/-- The patched module with its coordinatewise action by the ring fibre product.
Source: Stacks Project, Situation 08KH, N ×_M M'
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def patchedModule
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (N : ModuleCat.{max u v} B) (M' : ModuleCat.{max u v} A')
    (φ : (extendScalars b.hom).obj N ≅ (extendScalars q.hom).obj M') :
    ModuleCat.{max u v} (pullback (C := CommRingCat) b q) :=
  pullback (leftMap b q N M' φ) (rightMap b q M')

/-- The scalar-extension map S ⊗_R L → T ⊗_R L, viewed as R-linear.
Its formula is s ⊗ l ↦ f(s) ⊗ l. The equation h fixes the R-action on T.
Source: Stacks Project, Lemma 0D2I (2), the maps between the three base changes
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def transition
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (f : S →+* T) (t : R →+* T) (h : t = f.comp r)
    (L : ModuleCat.{max u v} R) :
    (restrictScalars r).obj ((extendScalars r).obj L) ⟶
      (restrictScalars t).obj ((extendScalars t).obj L) :=
  (restrictScalars r).map
      (((extendRestrictScalarsAdj r).homEquiv _ _).symm
        ((extendRestrictScalarsAdj t).unit.app L ≫
          (restrictScalarsComp'App r f t h _).hom)) ≫
    (restrictScalarsComp'App r f t h _).inv

/-- The common-reduction map from the B scalar extension of an R-module.
Source: Stacks Project, Lemma 0D2I (2)
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def transitionLeft
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (L : ModuleCat.{max u v} (pullback (C := CommRingCat) b q)) :=
  transition (pullback.fst b q).hom b.hom ((pullback.fst b q) ≫ b).hom rfl L

/-- The common-reduction map from the A' scalar extension of an R-module.
Source: Stacks Project, Lemma 0D2I (2)
(blueprint: lem-sfb-flat-module-fibre-product-patching). -/
noncomputable def transitionRight
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (L : ModuleCat.{max u v} (pullback (C := CommRingCat) b q)) :=
  transition (pullback.snd b q).hom q.hom ((pullback.fst b q) ≫ b).hom
    (congrArg CommRingCat.Hom.hom (pullback.condition (f := b) (g := q))) L

/-- Compatible flat modules patch to a flat module, without finiteness assumptions.
Source: Stacks Project, Lemma 0D2I (1), in Situation 08KH
(blueprint: lem-sfb-flat-module-fibre-product-patching).

Proof:
1. Set J = ker(R → B). Surjectivity of q gives R/J = B and J = I.
   By [lem-sfb-patched-module-base-change] the two scalar extensions of P are
   N and M'. By [lem-weil-pbc-tensor-over-quotient-ring], P/JP = N, flat over B.
2. Tensor associativity, written on pure tensors, identifies T tensor_R P with
   T tensor_A' M' for every A'-module T. For T = I this identifies the composite
   J tensor_R P → P → M' with ideal multiplication into the flat module M'.
   It is injective, hence J tensor_R P → P is injective too.
3. For a finitely generated ideal b of R, use the flatness of N and the quotient
   tensor identification to detect zero products after reduction to B. Right
   exactness [lem-weil-pbc-tensor-right-exact] then reduces injectivity for b
   to injectivity for b ∩ J, which need not be finitely generated.
4. For c ⊆ J let d = A'c inside I = J. The calculation
   (0,i)(0,a'k) = (0,ia')(0,k) shows Jd ⊆ c.
   Apply [lem-sfb-tensor-inclusion-flat-reduction] using steps 1 and 2:
   c tensor_R P → d tensor_R P is injective.
5. Step 2 for T = d identifies ideal multiplication with multiplication into M',
   injective by its flatness. Step 4 gives injectivity for c, and step 3 for all
   finitely generated ideals. Apply [lem-weil-pbc-flat-fg-ideal-criterion].
-/
theorem flat_patchedModule
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (hq : Function.Surjective q)
    (N : ModuleCat.{max u v} B) (M' : ModuleCat.{max u v} A')
    (φ : (extendScalars b.hom).obj N ≅ (extendScalars q.hom).obj M')
    [Module.Flat B N] [Module.Flat A' M'] :
    Module.Flat (pullback (C := CommRingCat) b q) (patchedModule b q N M' φ) := by
  sorry

/-- The canonical map from a flat module to the fibre product of its base changes
is an isomorphism. The projection equations specify l ↦ (1 ⊗ l, 1 ⊗ l).
Source: Stacks Project, Lemma 0D2I (2), in Situation 08KH
(blueprint: lem-sfb-flat-module-fibre-product-patching).

Proof (step 6 of the node): the coordinate inclusion R → B ⊕ A' and the
difference map B ⊕ A' → A form a short exact sequence: the fibre-product
equation identifies the kernel, and q is onto. Tensor with flat L, using
[lem-weil-pbc-flat-tensor-exact]. The tensor universal property
[def-weil-pbc-module-tensor-product] identifies L tensor_R R with L and
L tensor_R (B ⊕ A') with the sum of the two base changes. The kernel of the
tensored difference is their fibre product, and the induced map has the stated
unit coordinates. Swapping tensor factors gives the node's l tensor 1 convention.
-/
theorem exists_reconstruction_iso
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (hq : Function.Surjective q)
    (L : ModuleCat.{max u v} (pullback (C := CommRingCat) b q))
    [Module.Flat (pullback (C := CommRingCat) b q) L] :
    ∃ e : L ≅ pullback (transitionLeft b q L) (transitionRight b q L),
      e.hom ≫ pullback.fst _ _ =
        (extendRestrictScalarsAdj (pullback.fst b q).hom).unit.app L ∧
      e.hom ≫ pullback.snd _ _ =
        (extendRestrictScalarsAdj (pullback.snd b q).hom).unit.app L := by
  sorry

end ModuleCat.FibreProductPatching
