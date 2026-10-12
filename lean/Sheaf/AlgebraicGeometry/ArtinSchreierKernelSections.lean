/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sections of the Artin–Schreier kernel

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md`,
first sentence of the proof: the kernel is the constant prime-field sheaf.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The constant-sheaf inclusion is injective on sections and every section satisfying
`a ^ p = a` is in its image. This allows locally varying prime-field constants; it does
not assert that a root over a disconnected scheme is a single constant.
Source: blueprint `lem-sc-as-sequence`, first sentence of its proof; Stacks Tag 0A3J.
(blueprint: lem-sc-as-kernel-sections)

Proof:
1. The structural map to `Spec k` makes `p` vanish in each section ring and in every
   local ring of every etale object. At each underlying point the local-ring theorem
   `IsLocalRing.pow_eq_self_iff_existsUnique_zmod` identifies a root with a unique
   prime-field constant. Equality of germs gives equality with that constant on an
   open neighborhood. These neighborhoods are also etale objects over the base.
2. Sections of the constant sheaf are locally images of constants under the
   sheafification unit. If two sections have the same image under `iota`, refine their
   two covering sieves to a common cover where both are constants. At every point of
   this cover their constants agree, by the uniqueness part of the local-ring theorem
   and `hiota`. Further restrict to the open neighborhoods from step 1. Thus the two
   constant-sheaf sections agree locally, and sheaf separatedness makes them equal.
   On an empty object both sheaves have their unique section. This proves injectivity.
3. For a root `x`, use the open cover from step 1. On each member take the image under
   the sheafification unit of its prime-field constant. The formulas `hrestr` and
   `hiota` identify its image under `iota` with the restriction of `x`. On overlaps
   these sections agree by step 2. The sheaf condition glues them to a section `y`,
   and separatedness in the target shows `iota(y) = x`. The empty covering gives the
   same conclusion for the empty object. -/
theorem artinSchreier_kernel_sections
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (p : ℕ) [CharP k p] (hp : p.Prime)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (iota : C.constantZMod p ⟶ G)
    (hrestr : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hiota : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    ∀ U : C.Etaleᵒᵖ, Function.Injective (iota.hom.app U) ∧
      ∀ x : G.obj.obj U, (a U x) ^ p = a U x → ∃ y, iota.hom.app U y = x := by
  sorry

end AlgebraicGeometry
