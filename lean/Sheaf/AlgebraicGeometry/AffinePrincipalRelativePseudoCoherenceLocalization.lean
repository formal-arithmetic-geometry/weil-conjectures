module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.AffineQuotientResolutionSheafification
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.Topology.ClosedImmersionPushforwardExact

/-! # Principal localization of a relative pseudo-coherent polynomial chart

Source: Stacks Project, More on Morphisms, Tag 09VD,
`lemma-localize-relative-pseudo-coherent`, principal-source-open case
(blueprint: lem-sfb-affine-principal-relative-pseudocoherence-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- A polynomial chart with `m`-pseudo-coherent derived direct image over a principal
open of an affine base gives such a chart over the whole base after restricting the
source to a principal open. No quasi-coherence of the derived object is required.
Source: Stacks Project, More on Morphisms, Tag 09VD,
`lemma-localize-relative-pseudo-coherent`
(blueprint: lem-sfb-affine-principal-relative-pseudocoherence-localization).

Proof:
1. Write the affine base as Spec R, its open as Spec R_a, and X as Spec A.
   The given chart gives a surjection B = R_a[x_1,...,x_n] onto A. Adjoin an
   inverse of a: C = R[t,x_1,...,x_n] surjects onto B with kernel (at-1).
   This uses lem-weil-pbc-localization-away-polynomial-quotient and
   lem-weil-pbc-principal-localization-open-immersion and gives a closed immersion
   k from the original affine space into P = affine (n+1)-space over the base.
2. Multiplication by at-1 on C is injective: in a polynomial in t, the constant
   coefficient first vanishes, and then each successive coefficient vanishes.
   Thus 0 -> C -> C -> B -> 0 is an exact finite free resolution, without any
   nonzerodivisor assumption on a.
3. Apply lem-sc-affine-quotient-resolution-sheafification to this resolution.
   By lem-weil-pbc-spec-module-tilde-sections its two terms sheafify to the
   structure module of P. Hence (k_* O)[0] is pseudo-coherent by
   def-pur-pseudo-coherent-complex.
4. Closed-immersion pushforward is exact on arbitrary module sheaves, by
   lem-sc-closed-immersion-pushforward-exact on underlying abelian sheaves.
   Termwise direct images therefore compute derived direct images and their
   compositions (def-pc-derived-direct-image).
5. Apply lem-sfb-closed-pushforward-pseudocoherence to k and the given Ri_* E.
   Together with lem-weil-pbc-closed-immersion-comp and step 4 this shows that
   E' = R(ki)_* E is m-pseudo-coherent on P.
6. Lift b to h in C. The localization C_h surjects onto A_b, so U embeds as
   a closed subscheme of W = D_P(h). Adjoining an inverse of h embeds W into
   Q = affine (n+2)-space over the base. Their composite j is a closed immersion
   over the base, using the two localization lemmas of step 1 and composition.
7. Restriction preserves the strictly perfect approximations and their stalkwise
   cohomology conditions (def-sfb-m-pseudo-coherent-complex). The sectionwise
   formula of lem-weil-pbc-module-restriction-open-immersion-colimits identifies
   E' restricted to W with Ri'_* (E restricted to U), using step 4 and
   def-pc-derived-pullback. This holds for arbitrary module complexes.
8. Repeat steps 2 and 3 for hz-1 in C[z]; the structure module pushed forward
   from W to Q is pseudo-coherent. Apply the closed-pushforward equivalence
   again to the m-pseudo-coherent restriction of E'. Step 4 identifies the result
   with Rj_* (E restricted to U). Take r = n+2, with the same integer m.
-/
theorem affine_principal_relative_pseudoCoherence_localization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u}) [IsAffine S] (a : Γ(S, ⊤))
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ (S.basicOpen a).toScheme)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (b : Γ(X, ⊤)) (E : schemeDerivedCategory X) (m : ℤ)
    (h : ∃ n : ℕ, ∃ i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (S.basicOpen a).toScheme,
      IsClosedImmersion i ∧
      i ≫ (AffineSpace (ULift.{u} (Fin n)) (S.basicOpen a).toScheme ↘
        (S.basicOpen a).toScheme) = f ∧
      Scheme.IsMPseudoCoherent
        (AffineSpace (ULift.{u} (Fin n)) (S.basicOpen a).toScheme) m
        ((schemeDerivedDirectImage i).obj E)) :
    ∃ r : ℕ, ∃ j : (X.basicOpen b).toScheme ⟶ AffineSpace (ULift.{u} (Fin r)) S,
      IsClosedImmersion j ∧
      j ≫ (AffineSpace (ULift.{u} (Fin r)) S ↘ S) =
        (X.basicOpen b).ι ≫ f ≫ (S.basicOpen a).ι ∧
      Scheme.IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin r)) S) m
        ((schemeDerivedDirectImage j).obj ((derivedPullback (X.basicOpen b).ι).obj E)) := by
  sorry

end AlgebraicGeometry
