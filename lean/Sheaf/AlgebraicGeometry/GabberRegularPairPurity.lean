/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.TraitPrimeToEllLogAlteration
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Gabber purity for a regular Noetherian closed pair

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI,
Theorem 3.1.1 and Definition 2.3.1 (blueprint: lem-per-gabber-regular-pair-purity).

The supported class is the recorded normalized Kummer class, transposed through
ordinary etale derived direct image. The right adjoint and its adjunction are explicit:
changing their presentation transports this same class by the unique adjunction comparison.
Codimension is taken componentwise. No excellence or field hypothesis is present.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The normalized Kummer-supported fundamental class of a regular Noetherian closed
pair is an isomorphism, with the equivalent untwisted cohomology description.
The family `g` and its laws are those supplied by `regular_immersion_class_calculus`;
no arbitrary supported arrow is substituted. The actual eta is its supported realization
under the Hom bijection of `adj`. The resulting degree-`2c` identification with the
negative Tate line is the one induced by this eta, inverse Tate evaluation and shift.
We state the cohomology isomorphism's existence as a proposition, and retain the
specified eta's invertibility, which gives its canonical normalization.

Source: ILO, Expose XVI, Theorem 3.1.1, Definition 2.3.1 and section 3.7, pp.254--255
(blueprint: lem-per-gabber-regular-pair-purity).

Proof:
1. At level one, apply [lem-per-trait-prime-to-ell-log-alteration] to each integral regular
   flat quasi-projective scheme over a complete strictly henselian mixed-characteristic
   trait. The alteration's source is log smooth over a finite trait extension and has
   degree prime to ell. Finite type over a Noetherian trait gives Noetherianity by
   [lem-weil-pbc-finite-type-over-noetherian]. Apply
   [lem-per-log-smooth-trait-punctual-purity] to the source. Projectivity implies properness
   by [lem-kun-projective-implies-proper], so
   [lem-per-punctual-purity-proper-degree-descent] gives punctual purity of the target
   over the original trait. The degree is invertible in F_ell; no flatness of the
   alteration is assumed.
2. Apply [lem-per-punctual-purity-trait-test] to conclude punctual purity of every regular
   Noetherian scheme with ell invertible, including X and Z, without excellence.
3. Apply (b) and (c) of [lem-per-punctual-purity-two-of-three] to the pair. This proves
   invertibility of its actual normalized Kummer eta at level one, componentwise.
4. By [lem-per-gysin-coefficient-cone-triangles], the cones C_r of the actual coefficient
   classes fit into C_r -> C_(r+1) -> C_1 -> C_r[1]. Since C_1=0, induction gives C_r=0:
   [lem-sf-derived-homology-long-exact] gives vanishing in every degree, and
   [lem-weil-pbc-unbounded-derived-iso-cohomology] detects the zero derived object.
   Thus the specified eta at every positive level is invertible.
5. A closed immersion is proper by [lem-kun-projective-implies-proper]. Its trivial
   compactification gives Ri_!=Ri_* by [def-amb-etale-compact-support]; its right adjoint
   exists by [thm-amb-etale-exceptional-adjoint]. The Tate lines and their inverse lines
   have canonical pullbacks and evaluation isomorphisms by
   [lem-asd-etale-finite-twist-pullback]. Adjunction and
   [lem-amb-proper-coproducts-projection] identify, naturally in M,
   Hom(M,i^!(K tensor L)) with Hom(Ri_*M,K tensor L), then
   Hom(Ri_*M tensor L^(-1),K), then Hom(Ri_*(M tensor i^*L^(-1)),K), then
   Hom(M tensor i^*L^(-1),i^!K), then Hom(M,i^!K tensor i^*L).
   Yoneda therefore commutes i^! with the Tate line. Apply inverse Tate evaluation and
   shift [-2c] to eta to get i^!Lambda_X = Lambda_Z(-c)[-2c]. Exactness of tensoring
   by a locally free line gives the stated cohomology. For empty Z every object is zero;
   in codimension zero [lem-per-regular-immersion-class-calculus] normalizes the class
   to open-and-closed restriction, and to the identity for the identity immersion.
-/
theorem gabber_regular_pair_purity (ell : ℕ) (h : ell.Prime)
    (g : RegularClassFamily.{u} ell) (hg : IsRegularImmersionClassSystem ell h g)
    (n : ℕ) (hn : 0 < n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (hZ : IsRegularScheme Z) (hX : IsRegularScheme X)
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hi : IsStalkRegularClosedImmersion i c) (hell : IsUnit (ell : Γ(X, ⊤)))
    (G : DerivedCategoryModule (regularClassCoefficient ell n) X ⥤
      DerivedCategoryModule (regularClassCoefficient ell n) Z)
    (adj : ordinaryFinitePushforward (regularClassCoefficient ell n) i ⊣ G) :
    IsIso ((adj.homEquiv (ordinaryFiniteUnit (regularClassCoefficient ell n) Z) _)
      (regularClassRealization (regularClassCoefficient ell n) (ell ^ n)
        (regularClassAnnihilator ell n) i c (g n hn i c hi hell))) ∧
    Nonempty (((_root_.DerivedCategory.homologyFunctor _ ((2 * c : ℕ) : ℤ)).obj
        (G.obj (ordinaryFiniteUnit (regularClassCoefficient ell n) X))) ≅
      Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell n) (ell ^ n) Z
        (regularClassAnnihilator ell n) (-(c : ℤ))) ∧
    ∀ q : ℤ, q ≠ ((2 * c : ℕ) : ℤ) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (G.obj (ordinaryFiniteUnit (regularClassCoefficient ell n) X))) := by
  sorry

end AlgebraicGeometry.Etale
