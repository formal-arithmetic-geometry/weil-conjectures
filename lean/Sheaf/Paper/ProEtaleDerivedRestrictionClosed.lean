/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.NativeDerivedRestrictionData

/-! # The canonical closed comparison of derived pro-etale restriction

Source: Stacks Project, Tag 08JB, restriction of derived internal Hom to a slice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 50000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native K-flat tensorator preserves the Koszul symmetry, and its canonical
internal-Hom mate is invertible for exact weakly-etale restriction.

Source: Stacks Project, Tag 08JB, lemma-restriction-RHom-to-U; blueprint first
paragraph of `det-lem-int-tensor-product.proof.md`.
(blueprint: lem-sfb-proetale-derived-restriction-closed).

Proof: identify the chart site with the slice site by weakly-etale localization.
Transport module actions along the canonical coefficient isomorphism. Slice
restriction is exact and preserves K-flat tensor models and K-injective Hom
models; its evaluation-normalized Hom comparison is therefore invertible for
arbitrary unbounded complexes. On K-flat representatives the tensorator below
is the restriction comparison by its derived counit equation. The signed
interchange of total-complex summands commutes with restriction, proving the
braiding equation. Uncurrying identifies the canonical internal-Hom mate with
the slice comparison, so invertibility holds for that actual mate. -/
theorem proetale_derived_restriction_closed
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    [IsIso (condensedPullbackHom Λ.X f)] :
    let d := nativeDerivedRestrictionData Λ f
    let F := d.functor
    letI := d.monoidal
    (∀ K N : DerivedCategory (Internal Λ.X X),
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app N)) ∧
    (∀ K N : DerivedCategory (Internal Λ.X X),
      Functor.LaxMonoidal.μ F K N ≫ F.map (β_ K N).hom =
        (β_ (F.obj K) (F.obj N)).hom ≫ Functor.LaxMonoidal.μ F N K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
