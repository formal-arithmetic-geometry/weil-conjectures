module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Core geometric construction of the patching embedding, omitting the generic
stalk bijectivity conclusion.  Source: Stacks Project, Tag 01YL, third paragraph.
(blueprint: lem-weil-pbc-coherent-ideal-patching-generic-embedding-core)
Proof: carry out the finite pushforward, ideal intersection, annihilator, and
factorization construction from Tag 01YL; generic stalk bijectivity is established
separately by `coherent_ideal_patching_generic_embedding_stalk_bijective`. -/
theorem coherent_ideal_patching_generic_embedding_core
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hsupport : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hkill : ∀ g : X.presheaf.stalk ξ,
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G,
        g ∈ IsLocalRing.maximalIdeal _ → g • m = 0)
    (I : Z.IdealSheafData) :
    ∃ (r : ℕ), 1 ≤ r ∧
      let M := @biproduct (Fin r) X.Modules _ _
        (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
      (IsZero M ∨
        ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
          Mono ι ∧ J.IsQuasicoherent ∧
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
          ∃ (τ : idealModuleProduct ι G ⟶ M), Mono τ ∧
            Function.Surjective
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom) := by sorry

end AlgebraicGeometry.Scheme.Modules
