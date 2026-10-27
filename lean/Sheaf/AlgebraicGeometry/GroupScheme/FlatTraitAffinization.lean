module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree

/-! # Affinization of a flat separated finite-type group over a trait

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 3.1, printed p.5,
the paragraph on the natural group structure on the spectrum of global functions;
Stacks Project, Tags 02KH, 01I4, 01I1, 022S.
(blueprint: lem-sfb-flat-trait-group-affinization)

The product-of-sections comparison is expressed by its universal property in `CommRingCat`.
The two structure maps are the actual maps from `R`, and the two legs are pullback by the
projections. Thus `IsPushout` says exactly that the natural map
`Γ(G) ⊗[R] Γ(G) → Γ(G ×_R G)`, `a ⊗ b ↦ p₁*(a) * p₂*(b)`, is an isomorphism.
This uses the tensor-product pushout of commutative rings, not an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical affinization of a flat separated finite-type trait group is a group,
and global functions on its square are the tensor square over the base ring.

Source: Prasad--Yu, Proposition 3.1, printed p.5, natural-group-structure paragraph;
Stacks Project, Tags 02KH, 01I4, 01I1 and 022S.
(blueprint: lem-sfb-flat-trait-group-affinization)

Here `GrpObj` is the group-diagram structure in schemes over `Spec R`. The existential
over-arrow has underlying map exactly `G.left.toSpecΓ`, the morphism corresponding to
the identity of `Γ(G)`. `IsMonHom` gives its multiplication and identity equations;
`GrpObj.inv_hom` gives its inverse equation. On global functions these are precisely
`β₂ ∘ Δ = m*`, `ε = e*`, and `σ = i*`, since the pullback of `toSpecΓ` is the identity
under `ΓSpecIso`. Hence all three operations are induced by the specified pullbacks.

Proof:
1. Finite type and separatedness make `G` qcqs (lem-weil-pbc-qcqs-over-affine).
   The structure sheaf is invertible (def-sc-invertible-module). Flatness makes its
   sections torsion-free (lem-sc-flat-invertible-sections-torsion-free). A DVR is a PID
   (def-sc-discrete-valuation-ring), so its torsion-free modules are flat
   (lem-weil-pbc-pid-torsion-free-module-flat). The affine flatness criterion
   (lem-weil-pbc-flat-morphism-affine-criterion) therefore makes `Spec Γ(G)` flat.
2. On an affine open `U = Spec B` of the second factor, `B` is flat over `R`.
   Flat base change (lem-weil-pbc-flat-base-change-global-sections-qcqs) and the affine
   product formula (lem-weil-pbc-fibre-product-affine-spectra) identify pullback by
   `u × id` with the identity on `Γ(G) ⊗[R] B`. These are the actual restriction maps,
   so their local inverses agree and glue. Taking sections and then flat base change
   along `Spec Γ(G)` gives the asserted comparison `β₂`, with its pure-tensor formula.
3. Repeat this replacement on the first two factors of `G³`. The product affine charts
   are flat by base change and composition (lem-weil-pbc-flat-module-base-change,
   lem-weil-pbc-flat-ring-map-comp). Flat base change along the resulting affine square
   gives the analogous isomorphism `β₃`; in particular it is injective.
4. Define `Δ = β₂⁻¹ m*`, `ε = e*`, `σ = i*`. The affine product formula and `Spec`
   turn these `R`-algebra maps into the three operations on `Spec Γ(G)`. The affine-target
   correspondence (lem-weil-pbc-morphism-into-affine-scheme) gives their compatibility
   with `u`, which is exactly `IsMonHom` and its inverse equation.
5. Equality of maps from the first three fibre powers into an affine target can be
   checked after pullback by `u`, `u²`, `u³`, since `β₁ = id`, `β₂`, `β₃` are injective.
   Precomposing the associativity, both unit, and both inverse diagrams gives the
   corresponding group diagrams for `G`; descend these equalities to the affinization.
   Neither affineness of `G` nor finite generation of its section ring is used. -/
theorem exists_group_affinization_of_flat_trait
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (G : Over (Spec R)) [GrpObj G] [Flat G.hom] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ G.hom.appTop)
      ((Scheme.ΓSpecIso R).inv ≫ G.hom.appTop)
      (pullback.fst G.hom G.hom).appTop (pullback.snd G.hom G.hom).appTop ∧
    ∃ (_ : GrpObj (Over.mk (Spec.map ((Scheme.ΓSpecIso R).inv ≫ G.hom.appTop)))),
      ∃ u : G ⟶ Over.mk (Spec.map ((Scheme.ΓSpecIso R).inv ≫ G.hom.appTop)),
        u.left = G.left.toSpecΓ ∧ IsMonHom u := by
  sorry

end AlgebraicGeometry
