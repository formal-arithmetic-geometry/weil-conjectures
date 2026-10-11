import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.DerivedCategories

/-!
# K-injective resolutions

Source: literature/stacks-project/derived.tex, Definition 070H and Lemma 070K
(blueprint: def-weil-pbc-kinjective-resolutions).

K-injectivity is Mathlib's `CochainComplex.IsKInjective` (Stacks 070H: every morphism from an
acyclic complex is homotopic to zero); the node's Hom-complex formulation is the equivalent
Spaltenstein form recorded in Mathlib's source (`H^n Hom^•(A, I) = Hom_K(A, I[n])`, and acyclic
complexes are closed under shifts). Quasi-isomorphisms are Mathlib's `QuasiIso`.

## Main definitions

* `CochainComplex.IsKInjectiveResolution`: a quasi-isomorphism into a K-injective complex of
  sheaves of `R`-modules on the small étale site.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace CochainComplex

/-- A K-injective resolution of a complex `K` of sheaves of `R`-modules on the small étale site
of `T` is a quasi-isomorphism `f : K ⟶ I` whose target is K-injective (Mathlib's
`CochainComplex.IsKInjective`). For étale abelian sheaves take `R = ℤ`.
Source: Stacks Project, Definition 070H and Lemma 070K;
(blueprint: def-weil-pbc-kinjective-resolutions). -/
abbrev IsKInjectiveResolution (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    {K I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ}
    (f : K ⟶ I) : Prop :=
  QuasiIso f ∧ I.IsKInjective

end CochainComplex
