/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn

/-! # Etale points over geometrically unibranch integral schemes have integral affine neighbourhoods

Source: Stacks Project, literature/stacks-project/more-morphisms.tex, Tag 0GS9 proof,
the assertion that an etale source over a geometrically unibranch integral target is
geometrically unibranch, with the affine-local reduction of More on Algebra, Tag 0GSC
(blueprint: lem-dl-a1-etale-unibranch-local-domain).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point of an etale scheme over an integral geometrically unibranch scheme has an
affine open neighbourhood whose ring of sections is an integral domain.

Source: Stacks Project, More on Morphisms, Tag 0GS9 proof, the assertion that an etale source
over a geometrically unibranch target is geometrically unibranch; More on Algebra, Tag 0GSC,
affine-local reduction to a principal open with domain coordinate ring
(blueprint: lem-dl-a1-etale-unibranch-local-domain).

Proof:
1. For `u : U`, put `x = g u`, choose affine opens `W = Spec A` around `x` and
   `V₀ = Spec C₀` around `u` inside `g ⁻¹ W`. Integrality makes `A` a domain, and the
   restriction is an etale ring map. The stalk identification with `Aₚ` transfers the
   geometrically-unibranch hypothesis, so the affine-local hypotheses of
   `lem-dl-a1-etale-unibranch-domain-neighbourhood` hold.
2. Apply that lemma to obtain `h ∉ Q` with `C₀[1/h]` a domain. The principal open `D(h)`
   contains `u`, is affine, and has this localization as its coordinate ring.
-/
theorem etale_unibranch_local_domain
    {X U : Scheme.{u}} [IsIntegral X]
    (hgeom : ∀ (x : X) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [Algebra (X.presheaf.stalk x) K]
      [IsScalarTower (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [CommRing H] [Algebra (X.presheaf.stalk x) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (X.presheaf.stalk x) K H →
        IrreducibleSpace (PrimeSpectrum H))
    (g : U ⟶ X) [Etale g] (u : U) :
    ∃ V : U.Opens, IsAffineOpen V ∧ u ∈ V ∧ IsDomain Γ(U, V) := by
  sorry

end AlgebraicGeometry
