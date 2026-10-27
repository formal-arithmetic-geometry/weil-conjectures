module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Sheaf.AlgebraicGeometry.AffineFinitePointScalarSeparation

/-! # A section nonvanishing on a finite subset of a quasi-affine scheme

Source: Stacks Project, Properties, Tag 0F20,
`properties-lemma-quasi-affine-invertible-nonvanishing-section`, with W = X and retaining
its nonvanishing conclusion; quasi-affineness is Definition 01P6.
(blueprint: lem-sfb-quasiaffine-invertible-finite-set-section)
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on a quasi-compact scheme admitting an open immersion into an
affine scheme has a global section nonvanishing at every point of a finite subset.
The points need not be closed. Nonzero image in L_x / m_x L_x is expressed by the germ
lying outside the submodule m_x L_x.

Source: Stacks Project, Properties, Tag 0F20,
`properties-lemma-quasi-affine-invertible-nonvanishing-section`, with W = X and retaining
its nonvanishing conclusion; Definition 01P6 gives the quasi-affine hypothesis.

Proof:
1. Fix the open immersion j into an affine scheme supplied by hX. Apply
   `lem-a1-quasi-affine-open-principal-comparison-cover` to the identity of X. Its
   basic-open cover and `lem-weil-pbc-basic-open-function` show that O_X is ample:
   it is invertible by its identity trivialization (`def-sc-invertible-module`), and
   exponent one gives the affine nonvanishing neighborhoods in
   `def-weil-pbc-ample-invertible-module`; quasi-compactness is assumed.
2. By `def-sc-invertible-module`, L is quasi-coherent and locally free of rank one,
   hence finite type (`pqf-def-coherent`). Apply
   `lem-weil-pbc-coherent-twist-global-generation` to ample O_X and L, choosing
   d at least max(1, d_0). The resulting finite generating family for
   L tensor O_X^{tensor d} transports to L: multiplication of the scalar factors
   and m maps to m tensor 1 tensor ... tensor 1 are inverse balanced maps, commute
   with restrictions, and induce inverse sheaf-tensor maps
   (`def-pur-sheaf-tensor-product`). Thus L is globally generated.
3. By `lem-sc-global-generation-nonvanishing-cover`, every point z admits a global
   section t whose residue-fibre value t(z) is nonzero.
4. Induct strongly on the cardinality of E. For E empty choose zero; this also
   covers empty X.
5. If distinct x, y in E satisfy y in closure {x}, apply induction to E minus {x}.
   The section is nonzero at y. Its nonvanishing locus is open by
   `lem-weil-pbc-nonvanishing-section-trivializes`, so it also contains x.
   It therefore suffices to treat pairwise incomparable points.
6. Choose z in E and F = E minus {z}. Induction gives s nonzero on F. If s(z) is
   nonzero, finish. Otherwise the open immersion j preserves the fact that z is
   not a specialization of any x in F: an open neighborhood of z missing x maps
   to such a neighborhood of j(z). Apply `lem-sfb-affine-finite-point-scalar-separation`
   on the ambient affine scheme to j(F) and j(z). Restrict its scalar a to a global
   function f on X. The local-ring isomorphisms of `def-weil-open-immersion` and their
   induced residue-field isomorphisms (`def-weil-residue-field`) show f(x) = 0 on F
   and f(z) nonzero.
7. Choose t with t(z) nonzero by step 3. The section s + f*t is still nonzero on F.
   At z it equals f(z)*t(z), which is nonzero since the nonzero scalar f(z) is
   invertible in the residue field (`def-weil-residue-field`). Germ and quotient
   maps respect addition and scalar multiplication. This completes the induction,
   including F empty.

(blueprint: lem-sfb-quasiaffine-invertible-finite-set-section) -/
theorem exists_section_nonvanishing_on_finite_set_of_quasiAffine (X : Scheme.{u})
    [CompactSpace X]
    (hX : ∃ (Y : Scheme.{u}) (j : X ⟶ Y), IsAffine Y ∧ IsOpenImmersion j)
    (L : X.Modules) [L.IsInvertible] (E : Set X) (hE : E.Finite) :
    ∃ s : Γ(L, ⊤), ∀ (x : X), x ∈ E →
      L.presheaf.germ ⊤ x trivial s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
