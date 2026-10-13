module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.Modules.PullbackSectionFactorization

/-! # Free coordinates under a factorization of scheme maps

Source: Stacks Project, Tag 01CA, functoriality and associativity of tensor products.
(blueprint: new-sbc-pullback-free-coordinates-naturality)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a section through a factorization commutes with any map into finite free.

Source: Stacks Project, Tag 01CA, tensor associativity and functoriality.
(blueprint: new-sbc-pullback-free-coordinates-naturality)

Proof: Unfold the constructed section transport. Naturality of the composition
comparison moves the pulled-back alpha past
pullbackCompOfEq. Naturality of the adjunction unit then moves alpha past pullbackΓ.
The free pullback comparison commutes with the same composition comparison: locally,
both send a pure tensor s tensor (t tensor e_i) to st e_i. Compose this equality with
the i-th free projection. The unit comparison on the structure sheaf is restriction
of scalars along the scheme map, hence is appTop on global sections. Applying the
resulting equality to x gives the formula. This is independent of any quasi-coherence,
affineness, or inverse construction. Rank zero has no coordinate to check, and the
same tensor identities hold over the zero ring and on the empty scheme. -/
theorem pullback_free_coordinates_naturality
    {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ X) (v : Z ⟶ Y)
    (hv : v ≫ g = h) (M : X.Modules) (r : ℕ)
    (α : M ⟶ free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
    (x : Γ((pullback g).obj M, ⊤)) (i : Fin r) :
    freeSectionsEquiv (ULift.{u} (Fin r))
      (((pullback h).map α ≫ (pullbackFreeIso h (ULift.{u} (Fin r))).hom).app ⊤
        (pullbackSectionFactorization g h v hv M x)) (ULift.up i) =
      v.appTop (freeSectionsEquiv (ULift.{u} (Fin r))
        (((pullback g).map α ≫ (pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤ x)
          (ULift.up i)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
