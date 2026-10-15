module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# From affine to global torsion cohomological dimension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-sc-finite-type-torsion-cd`, Leray comparison step (blueprint:
thm-sc-finite-type-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The comparison and Leray step turns the affine bound into the bound for a
finite-type scheme.

Source: the comparison-site proof of `thm-sc-finite-type-torsion-cd` in the
blueprint subsection `sec-smooth-purity/sk-prop-sf-cbc`.

Proof: X is Noetherian: it is locally Noetherian by local finite type over a
field and quasi-compact by quasi-compactness of its structure morphism. Let
ε be the morphism from the small etale site to the Zariski site, whose direct
image evaluates F on open subschemes. Its inverse image is exact, so its right
adjoint preserves injectives. Abelian sheaves on either site form Grothendieck
abelian categories (equivalently modules over the constant integer sheaf), and
Zariski sections are left exact. The Grothendieck spectral sequence therefore
has E₂^{p,r} = H^p(X_Zar, R^r ε_*F). Evaluation at the terminal open identifies
Γ_Zar ε_* with Γ_et, so its abutment is H^{p+r}(X_et,F).

For each point x the stalk of R^r ε_*F is the filtered colimit over open
neighbourhoods V of H^r(V_et,F|V). Indeed apply ε_* to an injective resolution;
open restriction preserves injectives and filtered colimits of abelian groups
are exact, so cohomology commutes with that colimit. Affine neighbourhoods are
cofinal: refine an intersection of two neighbourhoods to a smaller affine
neighbourhood, without asserting that the intersection is affine. Such a V
is affine and finite type over K, and its dimension is at most d since closure
in X preserves strict chains of irreducible closed subsets of V. Restricting
F preserves the locally torsion condition: each local annihilating cover over
V is the same cover in the localized etale site. Thus hAffine makes the
colimit zero for r > d + c. Stalks detect zero Zariski sheaves, so R^r ε_*F = 0
in those degrees. Grothendieck vanishing on the Noetherian space X kills the
E₂ terms for p > d, for every abelian Zariski sheaf, without a torsion condition.
If p + r = q > 2 * d + c, either p > d or r > d + c. Thus all E₂ terms of
total degree q are zero, as are their later pages. First-quadrant convergence
gives a finite filtration of H^q with zero graded pieces, and therefore H^q = 0.
The same argument covers the empty scheme and d = 0; no separatedness of X is
used. The field cohomological-dimension hypothesis is unnecessary here: it is
used only to supply hAffine in the parent theorem.
(blueprint: new-thm-sc-finite-type-torsion-cd-affine-reduction)
-/
theorem subsingleton_H_of_two_mul_add_lt_of_affine_bound
    {K : Type u} [Field K] (c d : ℕ)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hAffine : ∀ {Y : Scheme.{u}} (b : Y ⟶ Spec (.of K)) [LocallyOfFiniteType b]
      [QuasiCompact b] [IsAffine Y] (hY : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
      (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) (n : ℕ),
      d + c < n → Subsingleton (Sheaf.H G n))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d + c < q) : Subsingleton (Sheaf.H F q) := by
  sorry

end AlgebraicGeometry.Scheme
