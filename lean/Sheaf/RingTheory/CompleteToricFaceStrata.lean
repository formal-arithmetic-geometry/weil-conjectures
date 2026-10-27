/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.RingTheory.CompleteToricModel
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import WeilConjectures.RingTheory.CohenRing
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.TraceFormula.FsFaceSharpening
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.FormalMonoidRingDimension
import Sheaf.RingTheory.LogRegularSaturationNormality
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.CompleteLocalExcellence
import Sheaf.RingTheory.ExcellentRing
import Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization
import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.RingTheory.FormalMonoidExtensionModel
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule

/-!
# Face strata of complete toric local models

Source: ILO, Travaux de Gabber, Exposé VI 1.3 and 1.6(i)--(ii), printed pp. 69--70;
the agent-formulated complete-model algebra interface
(blueprint: lem-per-complete-toric-face-strata).

The complete models, face localization, sharpening and group completion are the
published constructions. The existential face and ideal are fixed by explicit
membership and generator formulas, rather than supplied as extra hypotheses.
-/

set_option autoImplicit false

universe u v w

namespace ToricMonoid

/-- Face strata of either complete toric model are regular local, with codimension
the rank of the sharp localized monoid. `F` is the face of monomials outside `Q`;
`Associates (Algebra.faceLocalization (Multiplicative P) F)` is `T`, in
multiplicative notation. Its units are exactly `F^gp`, by face sharpening, so this
is the specified quotient `P_F/F^gp`. The ideal `J` is fixed by its displayed span.
Source: ILO VI 1.3 and 1.6(i)--(ii), printed pp. 69--70; agent-formulated local
algebra interface (blueprint: lem-per-complete-toric-face-strata).

Proof plan (the nine steps of the node):
1. For any sharp fs `H`, apply the power-series coefficient theorem and formal
monoid dimension theorem to `H ⊕ ℕ^n`. The field and Cohen hypersurface models
are nonzero Noetherian local of dimension `rank H^gp + n`; normality is
`lem-trf-log-regular-saturation-normality`.
2. The completion ideal is finitely generated and its residue is the coefficient
residue field, by completion modulo an ideal. Quotient-completion compatibility
makes the hypersurface complete as well. Complete-local excellence gives universal
catenarity and openness of the regular locus for finite type algebras.
3. Sharp saturation makes `H^gp` torsion free. Normalize a toric desingularization
over the rationals and descend its centers to a monoid tower. Realize that tower
over the integers and base change to the model, using
`lem-per-integral-toric-tower-proper`: the result is proper and is an isomorphism
after inverting the chart monomials.
4. Refine its last charts to smooth charts `ℕ^a ⊕ ℤ^b`. At a point above the
closed base point, apply `lem-trf-formal-monoid-extension-model`, with base chart
`H`, trivial unit character and zero group factor, to identify the local completion
with a formal monoid ring or a parameter hypersurface over a complete regular base.
5. The sharp monoid there is free. The residue-domain and dimension theorems give
regularity of its formal ring by counting generators of the maximal ideal. In the
hypersurface case augmentation detects that the equation is outside its square;
the regular hypersurface criterion applies. The chart local ring is Noetherian
by finite type and localization, so regularity descends from its completion.
6. The nonregular locus is closed by excellence. Its image is closed by properness
and misses the closed base point. Every nonempty closed subset of a local spectrum
contains that point, so the image is empty. The monomial-invertible open is regular.
7. Primality makes `F` a face. Face sharpening identifies `T^gp` with `P^gp/F^gp`;
its rank is the difference of the two ranks. Complete-model face quotients identify
the quotient by the complementary monomials with the complete model of `(F,n)`.
Localization then identifies `E/J` with the corresponding localized face model.
8. Its prime avoids every surviving monomial. Step 6 for the face model makes
`E/J` regular local. The original model and its prime localization are nonzero
Noetherian local rings.
9. Catenarity concatenates saturated prime chains in the local domain. Thus the
height of the face prime is `dim R - dim (R/p_F)` and
`dim E = height p_F + dim (E/J)`. Step 1 for `P` and `F`, followed by the rank
identity of step 7, gives the displayed equality. Zero-length chains, the zero
monoid, zero variables, both extreme faces and the zero prime are included.
-/
theorem complete_toric_face_strata
    (P : Type u) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ a b : P, a + b = 0 → a = 0 ∧ b = 0) (n : ℕ)
    (R : Type w) [CommRing R] (z : P → R)
    (hmodel : IsCompleteModel.{u, v, w} P n R z)
    (Q : Ideal R) [Q.IsPrime] :
    Nontrivial R ∧ IsNoetherianRing R ∧ IsLocalRing R ∧
      Nontrivial (Localization.AtPrime Q) ∧
      IsNoetherianRing (Localization.AtPrime Q) ∧ IsLocalRing (Localization.AtPrime Q) ∧
      ∃ F : Submonoid (Multiplicative P),
        (∀ q : P, Multiplicative.ofAdd q ∈ F ↔ z q ∉ Q) ∧
        (∀ a b : Multiplicative P, a * b ∈ F → a ∈ F ∧ b ∈ F) ∧
        AlgebraicGeometry.IsFineSaturatedMonoid
          (Associates (Algebra.faceLocalization (Multiplicative P) F)) ∧
        (∀ t : Associates (Algebra.faceLocalization (Multiplicative P) F),
          IsUnit t → t = 1) ∧
        ∃ J : Ideal (Localization.AtPrime Q),
          J = Ideal.span {x | ∃ q : P, Multiplicative.ofAdd q ∉ F ∧
            x = algebraMap R (Localization.AtPrime Q) (z q)} ∧
          IsRegularLocalRing (Localization.AtPrime Q ⧸ J) ∧
          ringKrullDim (Localization.AtPrime Q) =
            ringKrullDim (Localization.AtPrime Q ⧸ J) +
              (Cardinal.toENat (Module.rank ℚ
                (TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup
                  (Associates (Algebra.faceLocalization (Multiplicative P) F)))))) :
                WithBot ℕ∞) := by
  sorry

end ToricMonoid
