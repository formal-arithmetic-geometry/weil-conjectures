/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerRationalTraceDefs
import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerQbarTrace
import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerScalarExtension

/-! # Descent of the native rational-point trace identity
Source: the reviewed Euler-product proof Step 3.
(blueprint: lem-condensed-weil-euler-rational-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open NativeCondensedModule

private theorem subtype_map_finsum {ell : ℕ} [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {I : Type v} (f : I → E) :
    E.1.subtype (∑ᶠ i, f i) = ∑ᶠ i, E.1.subtype (f i) :=
  E.1.subtype.toAddMonoidHom.map_finsum_of_injective
    (by intro a b h; exact Subtype.ext h) f

/-- Descend the Qbar trace identity through an injective coefficient inclusion.
Source: Euler-product proof Step 3.
Proof: the Qbar case is the categorical trace input. For E, use the same extended
strict pair for every global and local operator. Injectivity of E into Qbar allows
checking equality after applying the inclusion, which preserves the degree sums
because it is injective and additive, and preserves all integer signs.
(blueprint: lem-condensed-weil-euler-rational-trace). -/
theorem eulerRationalTrace
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c : WeilCoefficient ell)
    (K : strictWeilComplexCategory D ell hEll X₀ c)
    (c₀ : Compactification (D.geometricFiber X₀).hom) (m : ℕ) (hm : 1 ≤ m) :
    ∃ hv : ∀ y : D.extensionPoints X₀ m hm,
        scalarLocalReturn D X₀ (eulerExtensionPoint D X₀ m hm y) m,
      (∑ᶠ j : ℤ, (j.negOnePow : ℤ) • eulerCompactTrace D X₀ ell hEll c K c₀ m j) =
        ∑ᶠ y : D.extensionPoints X₀ m hm, ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
          eulerPointTrace D X₀ ell hEll c K (eulerExtensionPoint D X₀ m hm y) m (hv y) j := by
  classical
  cases c with
  | qbar => exact eulerQbarRationalTrace D ell hEll X₀ K c₀ m hm
  | finite E =>
    obtain ⟨KΩ, hg, hl⟩ := eulerScalarExtensionTraces D ell hEll X₀ E K c₀
    obtain ⟨hv, htrace⟩ := eulerQbarRationalTrace D ell hEll X₀ KΩ c₀ m hm
    refine ⟨hv, ?_⟩
    apply (show Function.Injective E.1.subtype from fun _ _ h ↦ Subtype.ext h)
    rw [subtype_map_finsum E]
    simp_rw [subtype_map_finsum E, map_zsmul, hg, hl]
    exact htrace

end WeilConjectures.CondensedWeilEuler
