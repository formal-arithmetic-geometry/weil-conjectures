/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.ConstantModuleFiniteTypeReflection
import WeilConjectures.AlgebraicGeometry.ConstantKernelSpecToposNonempty
import WeilConjectures.AlgebraicGeometry.ConstantKernelSectionwiseFiniteType

/-! # Constructibility of the constant kernel forces finite generation

Let `k` be a separably closed field and `X = Spec k`. With `A = ULift (ZMod 2)`,
`V = ℕ →₀ A`, `B = TrivSqZeroExt A V` and `L = ker (e · : B → B)` for
`e = TrivSqZeroExt.inr (Finsupp.single 0 1)`: the ring object `B_X` of `Sheaf (X_proét, Ab)`
is `Sheaf.constRingSheaf`, the sheafification of the constant ring presheaf
`Presheaf.constRingObj B` (objectwise unit `ℤ → B`, multiplication `B ⊗ B → B`); the
`B_X`-module `L_X` is the image under `(presheafToSheaf _ _).mapMod` of the constant presheaf
of `B`-modules `L` (`Presheaf.toMod`, objectwise action `B ⊗ L → L`). Their underlying
abelian sheaves are the constant sheaves of `B` and `L`
(`constantSheaf = Functor.const ⋙ presheafToSheaf`). If `L_X` is constructible over `B_X`,
then `L` is a finitely generated `B`-module.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
  sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.proof.md,
  Counterexample construction: reduction to finite type on the separably closed point.
(blueprint: lem-sfb-constant-kernel-constructibility-reflection)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Let `k` be separably closed, `X = Spec k`, `B = TrivSqZeroExt A (ℕ →₀ A)` with
`A = ULift (ZMod 2)`, and `L = ker (e · : B → B)` for `e = inr (single 0 1)`. Let `B_X` be the
commutative ring object of `Sheaf (X_proét, Ab)` obtained by sheafifying the constant ring
presheaf `B` (unit and multiplication the sheafified constant maps `ℤ → B`, `B ⊗ B → B`), and
`L_X` the `B_X`-module object obtained by sheafifying the constant presheaf of `B`-modules `L`
(action the sheafified constant action `B ⊗ L → L`). If `L_X` is constructible over `B_X`, then
`Module.Finite B L`.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
  sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.proof.md,
  Counterexample construction: reduction to finite type on the separably closed point.
(blueprint: lem-sfb-constant-kernel-constructibility-reflection)

Proof:
1. `X = Spec k` has one point [def-weil-affine-spectrum]; the empty family is not a pro-étale
   covering of `X` [def-weil-pbc-proetale-site], so the initial sheaf of sets has no section
   over the final object `X` while the terminal sheaf has one: the topos is nonempty in the
   sense of [lem-sfb-constant-module-finite-type-reflection].
2. A constructibility stratification [def-sfb-constructible-module,
   def-constructible-stratification] has a stratum equal to the point; its immersion `g_a` is
   an isomorphism (a closed subscheme `Spec (k/I)` with `I ≠ k`, so `I = 0`). Local finite
   presentation [def-sfb-locally-finitely-presented, def-sfb-finitely-presented-module] gives a
   pro-étale covering `{u_i}` and epimorphisms `(u_i^* g_a^* B_X)^{n_i} → mapMod(u_i^*)(M_a)`;
   `{g_a ∘ u_i}` covers `X`. By [lem-sfb-constant-module-object-local-generation] the
   sectionwise constant module sheaf `L^sec` [def-sf-site-constant-module-functor] is generated
   by `n_i` sections over each `U_i`, and pulling back along `V ×_X U_i → V`
   [def-weil-pbc-sites-and-cohomology, def-pur-localized-ringed-site] shows `L^sec` is of finite
   type.
3. Apply [lem-sfb-constant-module-finite-type-reflection]
   (`CategoryTheory.siteConstantModuleFunctorGeneral_isFiniteType_iff`) with Steps 1 and 2 to
   obtain `Module.Finite B L` [def-weil-finitely-generated-module].
-/
theorem constantKernelConstructibilityReflection
    (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u})
    (hX : X = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    (hconstructible : IsConstructibleModuleObject
      (Sheaf.constRingSheaf (Scheme.ProEt.topology X)
        (TrivSqZeroExt (ULift.{u + 1} (ZMod 2)) (ℕ →₀ ULift.{u + 1} (ZMod 2))))
      (((presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapMod
          (Presheaf.constRingObj (C := X.ProEt)
            (TrivSqZeroExt (ULift.{u + 1} (ZMod 2)) (ℕ →₀ ULift.{u + 1} (ZMod 2))))).obj
        (Presheaf.toMod
          (TrivSqZeroExt (ULift.{u + 1} (ZMod 2)) (ℕ →₀ ULift.{u + 1} (ZMod 2)))
          ((Functor.const X.ProEtᵒᵖ).obj
            (ModuleCat.of
              (TrivSqZeroExt (ULift.{u + 1} (ZMod 2)) (ℕ →₀ ULift.{u + 1} (ZMod 2)))
              (LinearMap.ker
                (LinearMap.mulLeft
                  (TrivSqZeroExt (ULift.{u + 1} (ZMod 2))
                    (ℕ →₀ ULift.{u + 1} (ZMod 2)))
                  (TrivSqZeroExt.inr (R := ULift.{u + 1} (ZMod 2))
                    (M := ℕ →₀ ULift.{u + 1} (ZMod 2))
                    (Finsupp.single (0 : ℕ) (1 : ULift.{u + 1} (ZMod 2))))))))))) :
    Module.Finite
      (TrivSqZeroExt (ULift.{u + 1} (ZMod 2)) (ℕ →₀ ULift.{u + 1} (ZMod 2)))
      (LinearMap.ker
        (LinearMap.mulLeft
          (TrivSqZeroExt (ULift.{u + 1} (ZMod 2))
            (ℕ →₀ ULift.{u + 1} (ZMod 2)))
          (TrivSqZeroExt.inr (R := ULift.{u + 1} (ZMod 2))
            (M := ℕ →₀ ULift.{u + 1} (ZMod 2))
            (Finsupp.single (0 : ℕ) (1 : ULift.{u + 1} (ZMod 2)))))) := by
  let B := TrivSqZeroExt (ULift.{u + 1} (ZMod 2))
    (ℕ →₀ ULift.{u + 1} (ZMod 2))
  let L := LinearMap.ker
    (LinearMap.mulLeft B
      (TrivSqZeroExt.inr (R := ULift.{u + 1} (ZMod 2))
        (M := ℕ →₀ ULift.{u + 1} (ZMod 2))
        (Finsupp.single (0 : ℕ) (1 : ULift.{u + 1} (ZMod 2)))))
  have : HasColimitsOfShape (Discrete PEmpty.{1}) (Type (u + 1)) :=
    CategoryTheory.Limits.Types.hasColimitsOfShape
  have : HasColimitsOfShape (Discrete PEmpty.{1})
      (Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  have hft : SheafOfModules.IsFiniteType.{u + 1, u, u + 1}
      ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) B).obj
        (ModuleCat.of B L)) :=
    constantKernel_sectionwiseFiniteType k X hX (B := B) (P := L) (by
      simpa [B, L] using hconstructible)
  exact (CategoryTheory.siteConstantModuleFunctorGeneral_isFiniteType_iff
    (Scheme.ProEt.topology X) B (ModuleCat.of B L) (proEtaleSpec_topos_nonempty k X hX)).mp hft

end AlgebraicGeometry.ProEtale
