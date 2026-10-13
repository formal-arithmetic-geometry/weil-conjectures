/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Tensor extension of a coherent local morphism

Source: Stacks Project, Tag 01YB, proof of lemma-homs-over-open, through the
internal Hom and tensor-Hom adjunction, before descent to the multiplication image.
(blueprint: lem-pc-coherent-open-map-tensor-extension)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A local morphism extends from an ideal-power tensor product.
Source: Stacks Project, Tag 01YB, proof of lemma-homs-over-open, the paragraphs
constructing a map from the ideal power into internal Hom and applying tensor-Hom.
(blueprint: lem-pc-coherent-open-map-tensor-extension)

Proof: Coherence of H on a Noetherian scheme implies finite presentation. Thus
E = internal Hom(H,F) is quasi-coherent, and its sections on U are morphisms
H|U -> F|U. For the structure-module case of 01YB, a section of E on U extends
from some I^n: reduce to a coherent submodule containing that section, stabilize
its I-power torsion, and apply Artin-Rees to remove the torsion. The sections
extension lemma for the resulting torsion-free module yields I^n -> E. Tensor-Hom
adjunction gives beta : I^n tensor H -> F. On U the ideal is the structure sheaf,
since its support is the complement of U; evaluation and the adjunction show
that beta restricts to multiplication followed by phi. The affine ideal-power
formula identifies the power with the ideal-sheaf-data power. The restriction
comparison overFunctorEquiv transports this equality to restrictFunctor.
For n=0 multiplication is the left unitor. The empty open, zero ideal, unit ideal,
and zero source or target are included. No factorization through I^n H is claimed. -/
theorem coherent_open_map_tensor_extension
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H F : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) [F.IsQuasicoherent]
    (U : X.Opens) (hI : (I.support : Set X) = (U : Set X)ᶜ)
    (φ : (restrictFunctor U.ι).obj H ⟶ (restrictFunctor U.ι).obj F) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∃ (n : ℕ) (β : (I ^ n).toModules ⊗ H ⟶ F),
      (restrictFunctor U.ι).map β =
        (restrictFunctor U.ι).map ((I ^ n).toModulesι ▷ H ≫ (λ_ H).hom) ≫ φ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
