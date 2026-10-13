/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Gluing torsion-controlled triples -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Local torsion-controlled triples glue to a global factorization whose actual
kernel and cokernel retain local annihilation bounds.

Source: Stacks Project, Tag 0889(1), uniqueness argument; Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-algebraization-descent-gluing).

Proof: Choose supplied triples on each open. On each overlap use the normalized
quotient comparisons to identify completions. Lift the comparison and its inverse
by torsion-controlled hom lifting. Completion extensionality, together with
compatibility with the map to H, shows that both composites are identities and
that the lifted comparison is unique. Uniqueness proves the cocycle equation.
Apply sheaf-of-modules descent to glue the sources and maps. Coherence is local.
Glue formal comparison maps and inverses levelwise; their transition equations
and factorization equations hold locally, hence globally. Exact restriction
identifies the restrictions of the global kernel and cokernel with the kernels
and cokernels of the local maps, and ideal products commute with restriction.
Transport the supplied bounds across these identifications. For the empty scheme
all these modules are zero; for the unit ideal uniqueness uses the torsion
hypothesis and makes no assertion about arbitrary algebraizations. -/
theorem torsionControlled_algebraization_descent_gluing
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (γ : ∀ i, ((completion X J).obj H).obj ⋙
      Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) (Hlocal i).obj)
    (hγ : ∀ (i : ι) (n : ℕ),
      (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n + 1) H.obj) ≫ (γ i).hom.app (op n) =
        eqToHom (hHlocal i).symm ≫
          formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Hlocal i).obj)
    (hlocal : ∀ i, ∃ (F : CoherentModules (U i).toScheme) (a : F ⟶ Hlocal i)
      (β : N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) F.obj),
      Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom =
        β.hom ≫ formalCompletionMap (J.comap (U i).ι) a.hom ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel a.hom)))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∀ i, ∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (kernel a.hom))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (cokernel a.hom)))) := by sorry

end AlgebraicGeometry
