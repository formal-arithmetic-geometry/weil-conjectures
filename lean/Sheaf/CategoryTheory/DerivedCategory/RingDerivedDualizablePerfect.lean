/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex
import Sheaf.Algebra.Homology.BoundedProjectiveComplexDualPairing
import Sheaf.Algebra.Homology.SubcategoryLeftResolution

/-!
# Dualizable derived modules over an arbitrary commutative ring

Source: Stacks Project, More on Algebra, Tag 0FNS, `lemma-have-dual-derived`
(blueprint: lem-zl-ring-derived-dualizable-perfect).

The tensor is the existing K-flat derived monoidal tensor, obtained by deriving the
signed direct-sum total tensor `CochainComplex.mapBifunctor` of
`def-pc-tensor-complex-sheaves`. Its unit is canonically the degree-zero complex `A[0]`.
The localization universe is independent of the module universe.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory

namespace DerivedCategory

/-- An object has evaluation and coevaluation satisfying both triangle identities exactly
when it has a bounded finite-projective model. No Noetherianity or nonzero-ring assumption
is made. Source: Stacks Project, More on Algebra, Tag 0FNS, `lemma-have-dual-derived`
(blueprint: lem-zl-ring-derived-dualizable-perfect).

Proof:
1. For a perfect object choose a bounded finite-projective model P. The dual pairing of
   `lem-zl-bounded-projective-complex-dual-pairing` supplies a bounded dual D and the two
   chain maps with both triangle identities. Projective terms are flat by
   `lem-weil-pbc-projective-module-flat`; the bounded flat complexes are K-flat by
   `lem-pc-module-bounded-flat-kflat`. The comparisons of
   `lem-weil-pbc-site-derived-tensor-descent` identify their total tensors with derived
   tensors, naturally in the maps. Localize the chain identities and conjugate the maps
   by the model isomorphism; adjacent inverse isomorphisms cancel in each identity.
2. Conversely, represent Q by M and its given dual by a K-flat flat-term complex V using
   `lem-pc-kflat-resolution`. By symmetry and
   `lem-pc-derived-tensor-second-factor-functor`, Q tensor its dual is represented by
   Tot(M tensor V). The natural equivalence of `lem-pc-derived-free-module-hom-homology`
   represents coevaluation by a degree-zero cycle z in this total complex.
3. The direct-sum totalization of `def-pc-tensor-complex-sheaves` makes z a finite sum of
   pure tensors. Generate a subcomplex K of M by their first factors and their
   differentials. K has finite support. Tensoring its inclusions with the flat terms of
   V stays injective by the final clause of `lem-weil-pbc-flat-tensor-exact`. The lifted z
   is therefore still a cycle. The natural tensor computation gives a lifted
   coevaluation into K tensor the dual.
4. Compose this lift tensored with Q with evaluation to obtain r : Q to K. The first
   triangle identity and tensor naturality say that the inclusion i satisfies r then i
   equals the identity of Q. Cohomology, as in `def-weil-abstract-derived-category`,
   makes Q a retract of K on cohomology, so Q vanishes above the upper bound of K.
   The good truncation of M there is a bounded-above representative of Q: its cycles
   and boundaries agree below the bound, agree at the bound by taking the kernel,
   and both cohomologies vanish above it.
5. Apply `lem-sfb-subcategory-left-resolution` with free modules to obtain a
   bounded-above free representative F. Every module is a quotient of the free module
   on its underlying set, and zero is free, so the quotient condition holds. As in
   step 2 the coevaluation is represented by a finite-support cycle in Tot(F tensor V).
6. `lem-zl-bounded-free-finite-subcomplex` puts its first factors in a bounded finite-free
   subcomplex G. The final clause of `lem-weil-pbc-flat-tensor-exact` again makes the
   total inclusion injective, so the lifted element is a cycle and represents a lifted
   coevaluation. The same triangle calculation gives maps s : Q to G and j : G to Q
   with s then j the identity. Finite free terms are finite projective, so G is perfect.
7. Complete s to a distinguished triangle Q to G to C to Q[1], using
   `def-weil-triangulated-category` and `def-weil-abstract-derived-category`. The
   zero-composite clause of `lem-weil-pbc-hom-into-triangle-exact` after rotation,
   together with the shifted retraction, makes its third arrow zero. By
   `lem-pc-derived-zero-third-split`, G is isomorphic to Q direct-sum C. Perfectness is
   invariant under isomorphism directly from `def-pc-perfect-ring-complex`.
   `lem-sf-perfect-ring-summand` now makes Q perfect. None of these steps requires
   Noetherianity or a nonzero ring. -/
theorem dualizable_iff_isPerfectRingComplex {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Q : DerivedCategory (ModuleCat.{u} A)) :
    (∃ (D : DerivedCategory (ModuleCat.{u} A))
      (ev : D ⊗ Q ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
      (coev : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ Q ⊗ D),
      (λ_ Q).inv ≫ coev ▷ Q ≫ (α_ Q D Q).hom ≫ Q ◁ ev ≫ (ρ_ Q).hom = 𝟙 Q ∧
      (ρ_ D).inv ≫ D ◁ coev ≫ (α_ D Q D).inv ≫ ev ▷ D ≫ (λ_ D).hom = 𝟙 D) ↔
      IsPerfectRingComplex Q := by
  sorry

end DerivedCategory
