module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.RingTheory.RelativeMPseudoCoherent

/-! # Finite pushforward and relative degreewise pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 09UK,
lemma-finite-morphism-relative-pseudo-coherence
(blueprint: lem-sfb-finite-relative-pseudocoherent-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite morphism over a scheme preserves and reflects relative `m`-pseudo-coherence
of a complex with quasi-coherent cohomology, for each integer `m`. Both structural
morphisms are locally of finite type. No Noetherian or global boundedness assumption
is required.

Source: Stacks Project, More on Morphisms, Tag 09UK,
lemma-finite-morphism-relative-pseudo-coherence
(blueprint: lem-sfb-finite-relative-pseudocoherent-pushforward).

Proof:
1. Finiteness makes `π` affine, hence quasi-compact and quasi-separated by
   lem-weil-pbc-affine-morphism-permanence. Apply
   lem-pc-derived-direct-image-preserves-qcoh to see that `L = Rπ_*K` has
   quasi-coherent cohomology even for unbounded `K`.
2. Cover the base by affine opens `V = Spec R` and their inverse images in `Y`
   by affine opens `W = Spec A`. Since `π` is affine, `U = π⁻¹(W) = Spec B`
   is affine. By lem-weil-pbc-lft-affine-pairs, `A` and `B` are finite type
   `R`-algebras; finiteness of `π` makes `B` finite as an `A`-module.
   The equation expressing that `π` is over `S` gives the compatible ring tower.
3. Put `M = RΓ(U,K|U)` with its `B`-module structure, using
   lem-pc-affine-qcoh-derived-equivalence. By
   lem-pc-restrict-derived-direct-image-open and twice
   lem-pc-ringed-spaces-derived-direct-image-composition, identify
   `RΓ(W,L|W)` in `D(A)` with restriction of scalars of `M` along `A → B`.
   Indeed, the one-point ringed-space direct image of
   def-pc-ringed-spaces-derived-direct-image is exact scalar restriction:
   it leaves the underlying groups and differentials unchanged.
4. Apply clause (3) of lem-sfb-relative-m-pseudocoherence-derived-sections
   to the relative property on either side. Transfer it through the comparison
   of step 3 and lem-sfb-finite-algebra-relative-m-pseudocoherence in the
   corresponding direction. Clause (2) of the affine-section criterion on
   the chosen covers gives the relative property on the other side.
   The defining finite-free approximation of def-sfb-ring-relative-m-pseudocoherent
   is invariant under the comparison isomorphism by composition. The argument
   fixes arbitrary `m` and uses no global cohomological bound. -/
theorem isMPseudoCoherentRelativeTo_iff_finite_pushforward
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (π : X ⟶ Y) [IsFinite π] (hπ : π ≫ g = f)
    (m : ℤ) (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) :
    IsMPseudoCoherentRelativeTo f m K ↔
      IsMPseudoCoherentRelativeTo g m ((schemeDerivedDirectImage π).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
