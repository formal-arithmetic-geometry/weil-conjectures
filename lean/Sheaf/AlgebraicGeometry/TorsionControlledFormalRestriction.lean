/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # The restriction dictionary for torsion-controlled formal maps

Source: Stacks Project, Tags 087X, 0887 and Remark 0888; Modules, Tags 01AG and 01CB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical completion comparison on an open, with the original component
annihilation bound transported to the restricted map. The projection equations
specify the comparison, rather than allowing an arbitrary completion automorphism.

Source: Stacks Project, Tags 087X, 0887 and Remark 0888; Modules, Tags 01AG and 01CB.
(blueprint: lem-weil-pbc-torsion-controlled-formal-restriction).

Proof: Restriction to an open is exact and commutes with ideal products and powers.
For each n restrict the cokernel presentation H/J^(n+1)H. Identify the restricted
ideal-product inclusion with that for the comapped ideal. The two cokernel universal
properties give inverse comparison maps; cancelling the quotient epimorphisms
proves their inverse identities and the displayed projection equation. The same
cancellation with the transition maps proves naturality in n, yielding gamma.
Restriction preserves the component kernel and cokernel. Restrict the two zero
products, and use the ideal-power and kernel/cokernel comparisons to obtain their
zero products on U. Postcomposing with gamma at each level changes the kernel and
cokernel only by isomorphism, so the bound is unchanged. The equality hH identifies
the chosen coherent object with the actual restriction; eqToHom records this
identification in the quotient equation. All comparisons are defined by quotient
projections and are unique. Empty opens and zero or unit ideals satisfy the same
universal-property argument. No algebraization or choice of a local triple is used. -/
theorem torsionControlled_formal_restriction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) (U : X.Opens)
    (Hlocal : CoherentModules U.toScheme)
    (hH : Hlocal.obj = (Scheme.Modules.restrictFunctor U.ι).obj H.obj)
    (t : ℕ) (hbound : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op n))))) :
    ∃ γ : ((completion X J).obj H).obj ⋙ Scheme.Modules.restrictFunctor U.ι ≅
        formalCompletionSystem (J.comap U.ι) Hlocal.obj,
      (∀ n : ℕ,
        (Scheme.Modules.restrictFunctor U.ι).map
            (formalModuleQuotientπ J (n + 1) H.obj) ≫ γ.hom.app (op n) =
          eqToHom hH.symm ≫ formalModuleQuotientπ (J.comap U.ι) (n + 1) Hlocal.obj) ∧
      (∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
          (kernel ((Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor U.ι) ≫
            γ.hom).app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
          (cokernel ((Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor U.ι) ≫
            γ.hom).app (op n))))) := by sorry

end AlgebraicGeometry
