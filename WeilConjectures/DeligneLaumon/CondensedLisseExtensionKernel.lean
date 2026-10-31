/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.DeligneLaumon.CondensedLisseExtensionKernelForward
import WeilConjectures.DeligneLaumon.CondensedLisseExtensionKernelReverse

/-! # Extending a condensed lisse module through the fundamental-group quotient

Source: rem-dl-a1-conventions; proof steps 2--5 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-condensed-lisse-extension-kernel).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- A condensed lisse module extends across a dense open exactly when its normalized
representation kills the kernel of the actual map on finite-etale fibre automorphisms.

Source: rem-dl-a1-conventions; condensed monodromy and Stacks 0BTD.
(blueprint: lem-dl-a1-condensed-lisse-extension-kernel).

Proof: the left-to-right implication is `condensed_lisse_extension_kernel_forward`
(an extended module has its normalized action composed with the actual map
`q = pullbackPathHom j b ∘ eG`, hence kills its kernel); the right-to-left implication
is `condensed_lisse_extension_kernel_reverse` (the action descends along the
continuous surjection `q` and is realized by a lisse module on `C` whose pullback
is `M`). No local boundary, inertia or Frobenius data is used.
-/
theorem condensed_lisse_extension_kernel
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G) :
    (∃ L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) C),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L ∧
        Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M)) ↔
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1 := by
  constructor
  · exact condensed_lisse_extension_kernel_forward D l U₀ C₀ _hl _hdense hUC U C eU eC
      j₀ _hj₀ j _hj M _hM Ω b _hb G eG _haction R
  · exact condensed_lisse_extension_kernel_reverse D l U₀ C₀ _hl _hdense hUC U C eU eC
      j₀ _hj₀ j _hj M _hM Ω b _hb G eG _haction R

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
