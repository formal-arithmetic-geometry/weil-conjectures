/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.ProjGradedSheafificationExact
import WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial
import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart
import Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The structure-sheaf sequence of a projective hypersurface

Source: Stacks Project, curves.tex, Tag 0BYD, proof of lemma-genus-plane-curve;
constructions.tex, Tags 01M7, 01MN, 01MS, 01MY and 01N1.
(blueprint: lem-sfb-projective-hypersurface-structure-sequence)

The quotient ring is literally S/(F). Its grading and graded quotient homomorphism
are existential witnesses whose components and underlying map are fixed explicitly.
No hypersurface, ideal, morphism or associated sheaf is selected from an existence proof.
The first arrow is the existing twist multiplication, followed by O(0) = O.
The second is the actual structure-sheaf map of the induced Proj morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- Enable the existing total-degree grading for the finite polynomial rings used here.
This is exactly Mathlib's `MvPolynomial.gradedAlgebra`, with no new grading data.
Source: Stacks 0BYD, the graded polynomial ring S.
(blueprint: lem-sfb-projective-hypersurface-structure-sequence) -/
noncomputable instance hypersurfacePolynomialGrading (k : Type u) [Field k] (n : ℕ) :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
  MvPolynomial.gradedAlgebra

/-- The specified arrow O(-d) -> O is multiplication by F, with the canonical O(0) = O.
Source: Stacks 0BYD, first and second displayed exact sequences; 01MN.
(blueprint: lem-sfb-projective-hypersurface-structure-sequence) -/
noncomputable def hypersurfaceMultiplication {S : Type u} [CommRing S]
    {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {F : S} (hF : F ∈ 𝒜 d) :
    twist 𝒜 (-(d : ℤ)) ⟶ Scheme.Modules.unit (Proj 𝒜) :=
  twistMul (-(d : ℤ)) hF ≫
    eqToHom (congrArg (twist 𝒜) (neg_add_cancel (d : ℤ))) ≫
    (unitIsoTwistZero (𝒜 := 𝒜)).inv

/-- The hypersurface structure-sheaf sequence, with its associated-sheaf identifications,
all chart maps, and compatibility with every restriction between standard opens.
Source: Stacks 0BYD, proof of lemma-genus-plane-curve; Constructions 01M7, 01MN,
01MS, 01MY, 01N1, with the same argument in n+1 variables.
(blueprint: lem-sfb-projective-hypersurface-structure-sequence)

Proof, following the six DAG steps:
1. The polynomial ring over k is a domain: the leading monomial of a product of
   nonzero polynomials has the product of their nonzero leading coefficients.
   Multiplication by F is injective, has image (F), and shifts degree by d.
   Thus 0 -> S(-d) -> S -> S/(F) -> 0 is an exact graded sequence. The ideal
   (F) is homogeneous, since multiplication by F shifts each homogeneous component.
2. Apply lem-sfb-proj-graded-sheafification-exact and the fraction formulas of
   lem-sc-p1-proj-tilde-functorial. The resulting arrows send a/g^m to Fa/g^m
   and a/g^m to the quotient fraction, respectively.
3. The twist is the associated sheaf of S(-d), by def-weil-pbc-proj-twisting-sheaf.
   On D_+(X_j) its frame is X_j^(-d). These frames have exactly the transition
   ratios of def-pc-projective-space-twist, and cover by
   lem-weil-pbc-proj-polynomial-twist-chart. The map sends this frame to F/X_j^d.
   Use lem-weil-pbc-proj-standard-open-inclusion and
   lem-weil-pbc-sheaf-morphism-on-basis for the frame identifications and gluing.
4. By lem-sfb-graded-proj-quotient-twist-comparison, the quotient induces the actual
   closed immersion, with inverse-image chart D_+(q(g)) and ring map a/g^m ->
   q(a)/q(g)^m. Its chart structure sheaf is (C_(q(g)))_0 by def-pc-proj.
   This is the same as localizing C as an S-module at g and taking degree zero,
   so lem-weil-pbc-proj-graded-module-sheaf-exists identifies it with tilde C.
5. For h^t = b*g, restriction of c/g^m is b^m*c/h^(t*m), in both the module
   localization and the quotient ring localization. These formulas agree after q,
   commute with scalar multiplication, and glue on the standard-open basis.
   Thus the final arrow is the actual structure-sheaf restriction, not a chosen map.
6. Transport the exact sequence from step 2 along these compatible identifications.
   Every construction uses (F), never its radical. For F=X_0^d the nilpotents remain;
   if q(g) is nilpotent, the chart ring is zero and its open is empty. No condition
   on characteristic, smoothness, reducedness or irreducibility is used.

The additive chart embeddings alpha have precisely the fractions of degree -d as
range, hence identify O(-d) with tilde S(-d). Their scalar and restriction clauses
make these identifications module-linear and compatible. The ring equivalences beta
identify i_*O_Z with tilde(S/(F)); their scalar, quotient, and restriction clauses
record the full associated-sheaf and actual-arrow assertions.
-/
theorem projective_hypersurface_structure_sequence {k : Type u} [Field k]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    ∃ (ℬ : ℕ → AddSubgroup (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {F}))
      (_inst : GradedRing ℬ)
      (q : (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) →+*ᵍ ℬ) (hq : Function.Surjective q),
      (∀ a : MvPolynomial (Fin (n + 1)) k, q a = Ideal.Quotient.mk (Ideal.span {F}) a) ∧
      (∀ e : ℕ, (ℬ e : Set (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {F})) =
        Ideal.Quotient.mk (Ideal.span {F}) '' ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          e : Set (MvPolynomial (Fin (n + 1)) k))) ∧
      IsClosedImmersion (map q (GradedRingHom.irrelevant_le_map_of_surjective hq)) ∧
      (∃ hz : (hypersurfaceMultiplication hF) ≫ SheafOfModules.unitToPushforwardObjUnit
          (map q (GradedRingHom.irrelevant_le_map_of_surjective hq)).toRingCatSheafHom = 0,
        (ShortComplex.mk (hypersurfaceMultiplication hF) (SheafOfModules.unitToPushforwardObjUnit
          (map q (GradedRingHom.irrelevant_le_map_of_surjective hq)).toRingCatSheafHom)
          hz).ShortExact) ∧
      (∀ j : Fin (n + 1),
        (hypersurfaceMultiplication hF).app (basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n
          + 1)) k) (MvPolynomial.X j))
          (twistPowSection (-(d : ℤ)) (MvPolynomial.isHomogeneous_X k j)) =
        awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j)
          (Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
            (MvPolynomial.isHomogeneous_X k j) d F
            (by simpa using hF))) ∧
      (∃ alpha : ∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ), 0 < e → g.IsHomogeneous e →
          Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (-(d : ℤ)), basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g) →+ Localization.Away g,
        (∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e),
          Function.Injective (alpha g e he hg) ∧
          Set.range (alpha g e he hg) =
            {z | ∃ (m r : ℕ) (a : MvPolynomial (Fin (n + 1)) k), a.IsHomogeneous r ∧
              (r : ℤ) = (m : ℤ) * e - d ∧
              Localization.mk a (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) = z}) ∧
        (∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e)
          (c : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)
          (s : Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (-(d : ℤ)), basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)),
          alpha g e he hg (awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g c •
            s) =
            c.val * alpha g e he hg s) ∧
        (∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e)
          (s : Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (-(d : ℤ)), basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)),
          ((basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g hg he).inv.hom
            ((hypersurfaceMultiplication hF).app (basicOpen (MvPolynomial.homogeneousSubmodule
              (Fin (n + 1)) k) g) s)).val =
          alpha g e he hg s * algebraMap (MvPolynomial (Fin (n + 1)) k) (Localization.Away g) F) ∧
        (∀ (g h : MvPolynomial (Fin (n + 1)) k) (e l : ℕ) (he : 0 < e) (hl : 0 < l)
          (hg : g.IsHomogeneous e) (hh : h.IsHomogeneous l)
          (inc : basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) h ≤ basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)
          (t m : ℕ) (b a : MvPolynomial (Fin (n + 1)) k), 0 < t → h ^ t = b * g →
          ∀ s : Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (-(d : ℤ)), basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g),
          alpha g e he hg s =
            Localization.mk a (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) →
          alpha h l hl hh ((twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (-(d :
            ℤ))).presheaf.map (homOfLE inc).op s) =
            Localization.mk (b ^ m * a)
              (⟨h ^ (t * m), ⟨t * m, rfl⟩⟩ : Submonoid.powers h))) ∧
      ∃ beta : ∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ), 0 < e → g.IsHomogeneous e →
          Γ(Proj ℬ, map q (GradedRingHom.irrelevant_le_map_of_surjective hq) ⁻¹ᵁ
            basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g) ≃+* Away ℬ (q g),
        (∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e)
          (c : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)
          (s : Γ(Proj ℬ, map q (GradedRingHom.irrelevant_le_map_of_surjective hq) ⁻¹ᵁ
            basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)),
          beta g e he hg (((map q
            (GradedRingHom.irrelevant_le_map_of_surjective hq)).app
            (basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g) (awayToSection
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g c)) * s) =
            Away.map q g c * beta g e he hg s) ∧
        (∀ (g : MvPolynomial (Fin (n + 1)) k) (e : ℕ) (he : 0 < e) (hg : g.IsHomogeneous e)
          (m : ℕ) (a : MvPolynomial (Fin (n + 1)) k) (ha : a.IsHomogeneous (m • e)),
          beta g e he hg ((map q (GradedRingHom.irrelevant_le_map_of_surjective hq)).app
            (basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g) (awayToSection
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g (Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) hg m a ha))) =
          Away.mk ℬ (q.map_mem hg) m (q a) (q.map_mem ha)) ∧
        (∀ (g h : MvPolynomial (Fin (n + 1)) k) (e l : ℕ) (he : 0 < e) (hl : 0 < l)
          (hg : g.IsHomogeneous e) (hh : h.IsHomogeneous l)
          (inc : basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) h ≤ basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g)
          (t m : ℕ) (b : MvPolynomial (Fin (n + 1)) k) (c : MvPolynomial (Fin (n + 1)) k ⧸
            Ideal.span {F}),
          0 < t → h ^ t = b * g →
          ∀ s : Γ(Proj ℬ, map q (GradedRingHom.irrelevant_le_map_of_surjective hq) ⁻¹ᵁ
            basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) g),
          (beta g e he hg s).val =
            Localization.mk c (⟨q g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers (q g)) →
          (beta h l hl hh ((Proj ℬ).presheaf.map
            ((Opens.map (map q (GradedRingHom.irrelevant_le_map_of_surjective hq)).base).map
              (homOfLE inc)).op s)).val =
            Localization.mk (q b ^ m * c)
              (⟨q h ^ (t * m), ⟨t * m, rfl⟩⟩ : Submonoid.powers (q h))) := by
  sorry

end AlgebraicGeometry.Proj
