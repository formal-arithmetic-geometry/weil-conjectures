/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import WeilConjectures.AlgebraicGeometry.GabberQuotientPrincipalH1
import WeilConjectures.AlgebraicGeometry.ConstantEtaleCohomologyIsoComparison
import WeilConjectures.AlgebraicGeometry.GabberCriterion

/-! # Gabber vanishing for absolutely algebraically closed normal domains

## References

* Stacks Project, Étale Cohomology, Lemma 09ZC.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `R` be a normal domain with separably closed fraction field.  For every closed
subscheme `Z` of `Spec R`, the positive-degree étale cohomology of every finite constant
abelian sheaf vanishes. (Stacks, Lemma 09ZC) -/
theorem gabber_absolutely_algebraically_closed
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hsep : IsSepClosed (FractionRing R))
    (Z : Scheme.{u}) (i : Z ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((Etale.cohomology (AddCommGrpCat.{u + 1}) Z q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) := by
  obtain ⟨I, e, _⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i)
  let F := (constantSheaf (Spec (CommRingCat.of (R ⧸ I))).smallEtaleTopology
    AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)
  have hR := gabber_quotient_localizations R hsep I
  have hfg : ∀ (f g : R ⧸ I) (x : Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1}
        (Scheme.Opens.ι (X := Spec (CommRingCat.of (R ⧸ I)))
          (PrimeSpectrum.basicOpen (f + g)))).obj F) 1),
      x = 0 := by
    intro f g x
    have := Etale.gabber_quotient_principal_h1 R hsep I M (f + g)
    exact Subsingleton.elim _ _
  have hvan := Etale.gabberCriterion_degree (R ⧸ I) hR F
    (fun f g x _ _ ↦ hfg f g x)
  have hqnonneg : 0 ≤ q := by omega
  have hqnat : 0 < q.toNat := by omega
  have hz := (Etale.isZero_constant_cohomology_iff_subsingleton_H_of_iso
    Z (Spec (CommRingCat.of (R ⧸ I))) e M q.toNat).mpr (hvan q.toNat hqnat)
  simpa only [Int.toNat_of_nonneg hqnonneg] using hz

end AlgebraicGeometry
