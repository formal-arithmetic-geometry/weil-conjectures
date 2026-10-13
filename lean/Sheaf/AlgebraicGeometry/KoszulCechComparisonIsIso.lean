module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
import Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech

/-! # Invertibility of the specified Koszul-to-Čech chain map

Source: Stacks, Tag 08D1 (blueprint: lem-sc-koszul-cech-comparison-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The explicit localization cocone induces an isomorphism of A-module complexes.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-koszul-cech-comparison-is-iso).

Proof:
1. Put M = Γ(Spec(A), F) degreewise. Affine quasi-coherence identifies the sections
of F.X q on D(g) with M.X q localized at g, naturally in q and restriction maps.
2. In Čech row p, the Koszul tail is finite free on the subsets J of size p+1.
Its Hom complex is a finite product of copies of M.X q. A transition multiplies
that coordinate by g_J = product of f_j over J. The colimit of this repeated
multiplication system is M.X q localized at g_J, by the fraction map m/g_J^(e+1).
There are finitely many rows and subsets, so these identifications commute with
formation of each total degree. This is the identification in
lem-sc-affine-koszul-hom-alternating-cech, for the specified transition system.
3. The formula defining koszulCechCocone gives precisely these fractions times
(-1)^(pq+p(p-1)/2). This sign converts the signed Hom differential into the
horizontal Čech differential plus (-1)^p times the vertical differential.
Thus the degreewise bijections are the components of koszulCechComparison.
Their inverses form a chain map, proving it is an isomorphism of complexes.
For r=0 there are no nonempty subsets and both complexes are zero. For r=1
this is the usual localization map from the multiplication colimit, and for
F=0 it is the unique isomorphism between zero complexes. -/
theorem koszulCechComparison_isIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    IsIso (koszulCechComparison A r f F) := by
  sorry

end AlgebraicGeometry
