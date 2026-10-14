module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite selection over a Noetherian coefficient ring

Source: Stacks Project, Tag 09Z6 (3), partition alternative.
-/

@[expose] public section

universe u w

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A family containing an injective map at every geometric stalk of a constructible
module sheaf has a finite subfamily whose joint map is monomorphic.
Source: Stacks Project, Tag 09Z6 (3), partition alternative.
(blueprint: new-lem-weil-pbc-noetherian-module-finite-selection).

Proof: Apply the Noetherian-object finite-selection argument of Stacks Tag 09Z6
(3). For a finite family of the maps, take its joint kernel. If this kernel is
nonzero, choose a geometric stalk where it is nonzero and add a map that is
injective on that stalk; the joint kernel then strictly decreases. The
Noetherian-object argument for constructible subsheaves packages these successive
improvements into a finite family. At termination every geometric stalk of the
joint kernel is zero, so conservativity of geometric stalks makes the finite joint
map monomorphic. Reindex the selected family by `Fin n`; the empty scheme and zero
source are covered by the empty family. -/
theorem exists_mono_biproduct_of_constructible_module_stalk_injective_general
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l))) :
    ∃ (n : ℕ) (l : Fin n → L), Mono (biproduct.lift (fun i : Fin n ↦ φ (l i))) := by
  sorry

end AlgebraicGeometry.Scheme
