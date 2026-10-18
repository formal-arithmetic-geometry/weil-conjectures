/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Data.ZMod.Basic
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget

/-!
# Cohomology of affine opens of an excellent strictly local scheme

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XV, Corollary 1.2.2,
printed p. 219, and Corollary 1.2.4, printed p. 220; Stacks Project, Tags 03SA,
03Q5 and 03FD (blueprint: lem-per-affine-open-strict-local-cd).

A strictly local scheme is affine with strictly henselian ring of global sections.
The coefficient ring is the universe lift of `ZMod (ℓ ^ n)`. Cohomology is the
right-derived global sections of the underlying abelian sheaf placed in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every sheaf of prime-power torsion modules on an affine open of an excellent
strictly local scheme of dimension `d` has zero cohomology in degrees above `d`.
No constructibility hypothesis is imposed on the sheaf.

Source: ILO, Travaux de Gabber, Expose XV, Corollary 1.2.2, printed p. 219,
specialized to an affine open immersion, followed by filtered-colimit extension;
Stacks Project, Tags 03SA(3), 03Q5 and 03FD
(blueprint: lem-per-affine-open-strict-local-cd).

Proof:
1. For a constructible module sheaf, apply Gabber's affine Lefschetz corollary
   to the open immersion `j`. Its dimension function is the dimension of the
   closure of a point, bounded above by `d`. This is
   lem-per-affine-open-strict-local-cd-constructible.
2. The affine scheme `V` is quasi-compact and quasi-separated by
   lem-weil-pbc-affine-scheme-qcqs. Express `M` as a filtered colimit of
   constructible module sheaves by lem-weil-pbc-module-sheaf-colimit-constructible.
3. Etale cohomology commutes with this filtered colimit by
   lem-weil-pbc-cohomology-filtered-colimit. The module and underlying abelian
   formulations agree by lem-weil-pbc-etale-module-cohomology-forget.
4. In every degree `q > d`, all terms of the resulting filtered colimit of
   cohomology groups vanish by step 1, so the colimit and `H^q(V, M)` vanish. -/
theorem isZero_cohomology_affineOpen_of_strictlyHenselian
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    [IsStrictlyHenselianLocalRing Γ(X, ⊤)] (hX : IsExcellent Γ(X, ⊤))
    (ℓ n d : ℕ) (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hunit : IsUnit (ℓ : Γ(X, ⊤))) (hd : ringKrullDim Γ(X, ⊤) = (d : WithBot ℕ∞))
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ X) [IsOpenImmersion j]
    (M : Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))) (q : ℕ) (hq : d < q) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((sheafCompose V.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
            AddCommGrpCat.{u + 1})).obj M))) := by
  sorry

end AlgebraicGeometry.Etale
