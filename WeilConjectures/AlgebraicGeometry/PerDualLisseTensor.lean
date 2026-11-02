/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dual of a lisse tensor

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md`
(blueprint: lem-per-dual-lisse-tensor).

The statement uses the native module-object derived category.  The dualizing object is
the chosen bounded-constructible upper exceptional functor at the structure morphism,
applied to the coefficient unit.  The ordinary dual of a lisse module is its internal Hom
into the unit, placed in degree zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.exceptionalInverseImageCompactification
attribute [local irreducible] CondensedRing.exceptionalInverseImageProperPushforward

/-- The Verdier dual of a bounded constructible complex tensored with a lisse module is
canonically the tensor of its Verdier dual with the ordinary module dual.

(blueprint: lem-per-dual-lisse-tensor)
Source: latest blueprint, `part-weights-riemann-hypothesis/sec-fourier-transform/`
`sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md` and its proof
(`lem-per-dual-lisse-tensor.proof.md`), paragraphs 1--3.

Proof (the four DAG steps):
1. Work in the ordinary uncompleted derived category over the pulled-back condensed
   coefficient ring. The module-object/ringed-site comparison preserves tensor, internal
   Hom, evaluation and restriction. Tensor--Hom currying gives
   `RHom(K ⊗ᴸ L, omega) ≅ RHom(K, RHom(L, omega))`.
2. On a pro-etale cover trivializing `L` as a finite free module, strict-perfect Hom
   identifies `RHom(L, omega)` with the corresponding finite power of `omega`.
   The ordinary-to-derived dual map is locally the identity, and the evaluation map
   `L`'s ordinary dual tensored with `omega` to `RHom(L, omega)` is locally the
   finite-free coordinate isomorphism. Hom restriction and tensor pullback preserve it.
3. Put `V = Hom(L, B)`. Transpose evaluation, using symmetry, to obtain
   `beta : RHom(K, omega) ⊗ᴸ V → RHom(K, V ⊗ᴸ omega)`. On a trivializing slice
   both sides are the same finite power of `RHom(K, omega)` and `beta` is the identity.
   This uses finite products and adjunction and requires no perfectness of `K`.
4. Exact restriction commutes with cohomology. The comparison cones vanish on the cover,
   so sheaf descent makes them vanish globally. Invert the first comparison inside
   `RHom(K, -)` and invert `beta`; their composition with currying is the asserted
   canonical isomorphism. This is compatible with all slice restrictions.
-/
theorem per_dual_lisse_tensor
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpell : p ≠ ell)
    (hbase : Finite k ∨ IsAlgClosed k)
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (L : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) L) :
    letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
    letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
    letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
    letI : Fact (ringChar k).Prime :=
      ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
    letI : Fact (ringChar k ≠ ell) :=
      ⟨by rw [ringChar.eq k p]; exact hpell⟩
    let aX : X ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk X.hom
    let c := exceptionalInverseImageCompactification aX
    ∀ (H : PreservesBoundedConstructiblePushforwards
        (Profinite.padicAlgClRingObj ell) k)
      (hAdj : (exceptionalInverseImageProperPushforward
        (Profinite.padicAlgClRingObj ell) aX
        (H (X := c.overObj) (Y := Over.mk (𝟙 (Spec (.of k)))) c.overG)).IsLeftAdjoint),
    letI := hAdj
    let omega :=
      (CondensedRing.boundedConstructibleUpperShriekOfRightAdjoint
        (Profinite.padicAlgClRingObj ell) ell aX
        (H (X := c.overObj) (Y := Over.mk (𝟙 (Spec (.of k)))) c.overG)).obj
        ⟨𝟙_ _, CondensedRing.boundedConstructible_tensorUnit
          (Profinite.padicAlgClRingObj ell) (Spec (.of k))⟩
    let DK :=
      (CondensedRing.derivedHom (Profinite.padicAlgClRingObj ell) X.left).obj (op K.obj)
    Nonempty
      (((CondensedRing.derivedHom (Profinite.padicAlgClRingObj ell) X.left).obj
          (op (((CondensedRing.derivedTensor (Profinite.padicAlgClRingObj ell) X.left).obj
            K.obj).obj ((DerivedCategory.singleFunctor _ 0).obj L)))).obj
          omega.obj ≅
      ((CondensedRing.derivedTensor (Profinite.padicAlgClRingObj ell) X.left).obj
          (DK.obj omega.obj)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ihom L).obj (𝟙_ _)))) := by
  sorry

end AlgebraicGeometry.ProEtale
