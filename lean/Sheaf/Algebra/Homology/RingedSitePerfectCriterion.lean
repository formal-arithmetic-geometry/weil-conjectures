module

public import Sheaf.Algebra.Homology.RingedSitePseudoCoherent
public import Sheaf.Algebra.Homology.RingedSiteLocallyFiniteTor
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.SiteTorIntervalRestriction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract

/-! # Perfectness criterion on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08G8, using Tags 08FT, 08FZ,
08G5 and 08G7 (blueprint: lem-sfb-ringed-site-perfect-criterion).
-/

@[expose] public section
set_option autoImplicit false

universe u v r w w'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A derived object on an arbitrary ringed site is perfect exactly when it is
pseudo-coherent and locally has finite Tor dimension. No global bounds or coherence
hypotheses are imposed.
Source: Stacks Project, Tag 08G8, with Tags 08FT, 08FZ, 08G5 and 08G7
(blueprint: lem-sfb-ringed-site-perfect-criterion).

Proof:
1. For a perfect object choose bounded finite-free-retract representatives on a cover
of each site object. Their derived identifications give every m-approximation. A retract
of a finite free module is flat: tensoring its splitting exhibits its tensor functor as
a retract of a finite direct sum of identity functors (tensor-closed lemma). The bounded
flat model equivalence gives a Tor interval on each covering member. For a zero complex
use [0,0]. Thus perfectness implies both predicates.
2. Conversely fix U and cover it by charts with Tor intervals [a,b]. Pseudo-coherence
restricts to each slice by exact restriction and relocalization. Choose a strictly perfect
(a-1)-approximation P₀ → K there. Its brutal truncation P in degrees ≥ a-1 still gives
cohomology isomorphisms in every degree ≥ a, and has flat finite-free-retract terms.
The Tor interval remains valid after further localization (site Tor restriction lemma).
3. The flat-approximation-opcycle lemma gives flatness of Q = coker(P^(a-1) → P^a).
For finite-free splittings i₁,p₁ and i₀,p₀ of these two terms, set e = i₀p₀.
The map O^(r+s) → O^s, (x,y) ↦ i₀ d p₁(x) + (1-e)y, has cokernel Q:
the second summand kills the complement of P^a and the first kills the image of d.
Thus Q is finitely presented, also on every slice.
4. Form the good lower truncation T = τ≥a P, with Q in degree a, the old terms above a,
and zero below a. Testing the Tor condition on O gives K ∈ D≥a. The left adjoint
property of lower truncation factors P → K through T → K. It induces the same
cohomology isomorphisms in degrees ≥ a; below a both sides vanish. The cohomology
criterion for bounded-below derived objects makes T → K an isomorphism.
5. A flat locally finitely presented module is locally a finite-free retract. Apply
this to Q, then restrict T to that cover. Exact restriction preserves the cokernel and
derived isomorphism, and the higher terms retain their splittings. T is bounded and
strictly perfect; its existing upper bound suffices, so do not brutally truncate at b.
Compose the covers and identify iterated slices by relocalization. Since U was arbitrary,
this is perfectness.
-/
theorem isPerfectOnRingedSite_iff_pseudoCoherent_locallyFiniteTor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))]
    [∀ U : C, HasDerivedCategory.{w'} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))) :
    IsPerfectOnRingedSiteOfUniverses.{u, v, r} R K ↔
      IsPseudoCoherentOnRingedSite.{u, v, r, w, w'} R K ∧
        HasLocallyFiniteTorDimensionOnRingedSite.{u, v, r, w, w'} R K := by
  sorry

end SheafOfModules
