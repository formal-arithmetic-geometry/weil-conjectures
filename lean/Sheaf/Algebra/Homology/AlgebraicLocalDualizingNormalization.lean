/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! # Normalizing an algebraic dualizing complex over a local ring

Source: Stacks Project, dualizing.tex, Lemma 0A7L (lemma-find-function) and
Section 0A7M (section-dualizing-local), opening paragraph
(blueprint: lem-per-algebraic-local-dualizing-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace DerivedCategory

/-- An algebraic dualizing complex over a nonzero Noetherian local ring can be
normalized by a shift. The same integer specifies the residue-field derived Hom
and the inverse shift of the dualizing complex.
Source: Stacks Project, Lemma 0A7L and Section 0A7M, opening paragraph
(blueprint: lem-per-algebraic-local-dualizing-normalization).

Proof:
1. The quotient κ = A/m is a field, hence Noetherian, and is finite over A, generated
   by 1. By lem-trf-finite-map-dualizing-transfer, RHom_A(κ[0],Ω), with the natural
   κ-action, is an algebraic dualizing complex over κ. Its hypotheses are precisely
   the bounded injective representative, finite cohomology and scalar-action clauses
   of def-per-algebraic-normalized-dualizing.
2. By lem-per-algebraic-field-dualizing-shift this κ-complex is isomorphic to κ[s]
   for an integer s. Exact restriction of scalars preserves kernels, images and
   quasi-isomorphisms, so it gives the displayed isomorphism in D(A), using the
   localization of def-weil-abstract-derived-category.
3. For a bounded injective representative I of Ω, the theorem
   lem-weil-pbc-bounded-below-injectives-kinjective ensures that I and I[-s] are
   K-injective. The Hom-complex formula of def-pur-derived-internal-hom gives
   Hom(κ[0],I[-s]) = Hom(κ[0],I)[-s], hence RHom_A(κ[0],Ω[-s]) ≅ κ[0].
   Boundedness, injectivity and finite cohomology are preserved by shifting.
   Simultaneous shifting identifies Hom(I[t],I[t]) with Hom(I,I), by reindexing
   and multiplying degree-n cochains by (-1)^(t*n). The differential formula
   verifies this chain isomorphism; it preserves scalar multiplication in degree
   zero. Thus the scalar-action condition is preserved as well. Taking t = -s
   proves all dualizing conditions and the normalization clause. -/
theorem algebraic_local_dualizing_normalization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (Ω : DerivedCategory (RingSiteModules A)) (hΩ : IsAlgebraicDualizing A Ω) :
    ∃ s : ℤ,
      Nonempty
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf A)
          ((DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
            (algebraicDualizingModuleSheaf A
              (ModuleCat.of A (IsLocalRing.ResidueField A))))).obj Ω ≅
          ((DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
            (algebraicDualizingModuleSheaf A
              (ModuleCat.of A (IsLocalRing.ResidueField A))))⟦s⟧) ∧
      IsNormalizedAlgebraicDualizing A (Ω⟦-s⟧) := by
  sorry

end DerivedCategory
