/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.RelativeBidualTriangles
import Sheaf.Paper.FiniteExceptionalInternalHom

/-!
# Dualizing complexes on locally closed subschemes

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
proof of Proposition 7.6.9, p. 313, and proof of Proposition 7.6.3, p. 311
(blueprint: lem-per-dualizing-locally-closed-inheritance).

The dualizing condition is expanded in the statement. Its biduality morphism is the
transpose of evaluation after the canonical signed tensor symmetry. Coefficients are
ULift of the prime field, in the ordinary small-etale module derived category.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical biduality component for an arbitrary ordinary-etale module complex.
This is the transpose of evaluation after the descended signed symmetry. It is given
by actual adjunction and braiding data, without a preservation or invertibility assertion.
Source: ILO XVII, Definition 0.8 and proof of Proposition 7.6.9, p. 313
(blueprint: lem-per-dualizing-locally-closed-inheritance). -/
noncomputable def etaleEvaluationBiduality (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (Q M : DerivedCategoryModule R X) :
    M ⟶ ((derivedHom (ModuleCat.{u + 1} R) X).obj
      (op (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q))).obj Q :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} R)
    (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q)).homEquiv M Q
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app
        (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q)).app M ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) M).counit.app Q)

/-- Existence of a prime-field dualizing complex passes to every locally closed subscheme.
The auxiliary Noetherian algebra A is retained, although this assertion uses only the
prime-field coefficients. A dualizing object is bounded constructible, its internal-Hom
functor preserves bounded constructibility, and the canonical evaluation transpose is
invertible on every bounded constructible object.

Source: ILO, Expose XVII, proof of Proposition 7.6.9, p. 313; the open case is also in
proof of Proposition 7.6.3, p. 311
(blueprint: lem-per-dualizing-locally-closed-inheritance).

Proof:
1. For an open j, localized-site equivalence (lem-weil-pbc-etale-site-localization-open)
   and exact restriction/extension (lem-pur-site-restriction-module-adjunction-exact)
   give exact j^* and j_!. They commute with cohomology by
   lem-weil-pbc-exact-functor-derived-factorization. Restriction preserves constructibility
   by prop-constructible-pullback; extension preserves it by adjoining the closed complement
   with zero stalks (lem-weil-pbc-extension-by-zero-stalks). Thus j^*Q is bounded constructible.
2. Internal-Hom restriction (lem-weil-pbc-ringed-internal-hom-exact-restriction) identifies
   j^*D_X with D_U j^*. Apply this to j_!M and use j^*j_!M = M
   (def-weil-pbc-extension-by-zero) to prove preservation of bounded constructibility.
3. Restriction preserves evaluation and the signed symmetry, hence their transpose
   (def-pur-derived-internal-hom and lem-per-relative-bidual-triangles). Restrict the
   biduality isomorphism for j_!M to get the canonical biduality isomorphism for M.
4. For a closed i:Z -> X, quotient affine charts make Z Noetherian. The map i is finite
   (lem-weil-pbc-closed-immersion-finite). Exact i_* and i^*, with i^*i_* = id and supported
   essential image (prop-weil-pbc-inverse-image-modules-exact and lem-kun-04ca), show that
   i_* reflects isomorphisms and both functors preserve bounded constructibility. For i_*,
   append the open complement with zero sheaf to a stratification of Z.
5. Set Q_Z = i^!Q. The unit case of lem-per-finite-exceptional-internal-hom identifies
   i_*Q_Z with D_X(i_*Lambda_Z). The latter is bounded constructible; applying i^* gives
   bounded constructibility of Q_Z without a cohomological-dimension bound.
6. The same finite internal adjunction gives beta_M:i_*D_Z M = D_X(i_*M).
   Its right side is bounded constructible, so applying i^* proves this for D_Z M.
7. The evaluation-counit normalization of lem-per-finite-exceptional-internal-hom and
   the transpose description in lem-per-relative-bidual-triangles identify
   beta_(D_Z M) composed with i_*eta_M with D_X(beta_M) composed with eta_(i_*M).
   Transpose both sides: each is the evaluation pairing followed by the same counit,
   with the same signed swap. The right side and beta are invertible. Since i_* reflects
   isomorphisms, eta_M is invertible. Thus Q_Z is dualizing.
8. Factor an immersion as closed followed by open (def-weil-closed-immersion).
   The open is Noetherian (lem-weil-pbc-noetherian-open-subscheme-noetherian).
   Apply the open and closed cases to construct i^!j^*Q. The empty subscheme gives the
   zero category and zero dualizing object; identities recover Q. No reducedness,
   excellence, invertibility of ell, dimension or cohomological-dimension bound is used.
-/
theorem exists_dualizing_of_isImmersion
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type a) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod ℓ) A]
    (hX : ∃ Q : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X Q ∧
      ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X M →
          DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X
            (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) X).obj (op M)).obj Q) ∧
          IsIso (etaleEvaluationBiduality (ULift.{u + 1} (ZMod ℓ)) X Q M))
    (T : Scheme.{u}) (f : T ⟶ X) [IsImmersion f] :
    ∃ Q : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T,
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) T Q ∧
      ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T,
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) T M →
          DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) T
            (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op M)).obj Q) ∧
          IsIso (etaleEvaluationBiduality (ULift.{u + 1} (ZMod ℓ)) T Q M) := by
  sorry

end AlgebraicGeometry.Etale
