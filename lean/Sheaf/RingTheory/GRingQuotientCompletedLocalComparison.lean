module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.GRingCompletionRegular
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.RegularLocalMaximal
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.Quotient
import Sheaf.RingTheory.GeometricallyRegularLocalFieldAdicSmooth
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.FormallySmoothAdicCompleteSourceTarget
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Regular completed-local comparison above a G-ring quotient

Source: Rotthaus (1979), Lemma 4 and Corollaries 4.1--4.2, pp. 175--176;
Stacks Project, More on Algebra, Tags 0AH2, 07C0, 07EL, 07NQ, 07ED and 07PM.
(blueprint: lem-per-g-quotient-completed-local-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- The canonical completed-local comparison for the Jacobson-adic completion of `B`.
The chosen map is uniquely determined: its `n`-th quotient coordinate sends the class of
`a` to the class of the localized image of `a`, by the specification of
`RingHom.exists_adicCompletion_map_of_local`. Equality of all coordinates is equality in
`AdicCompletion`, so the choice carries no unspecified data.
Source: Stacks Project, More on Algebra, Tag 07ED, the induced map of completions.
(blueprint: lem-per-g-quotient-completed-local-comparison) -/
noncomputable def jacobsonCompletedLocalComparison
    (B : Type u) [CommRing B]
    (Q : Ideal (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) [Q.IsPrime] :
    AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime
          (Q.comap (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)))))
        (Localization.AtPrime
          (Q.comap (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B))))
      →+* AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) :=
  (RingHom.exists_adicCompletion_map_of_local
    (Localization.localRingHom
      (Q.comap (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B))) Q
      (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) rfl)).choose

/-- Above a nonmaximal prime containing the extended ideal `J`, the canonical map between
completed prime localizations is regular, local and faithfully flat. The completion of `B`
is taken at its Jacobson radical, the intersection of its finitely many maximal ideals.
The chosen completion map is uniquely fixed by every quotient coordinate in
`RingHom.exists_adicCompletion_map_of_local`; it is not an arbitrary ring homomorphism.
No completeness or G-ring assumption is imposed on `B`.

Source: Rotthaus (1979), Lemma 4 and Corollaries 4.1--4.2, pp. 175--176;
Stacks Project, Tags 0AH2, 07C0, 07EL, 07NQ, 07ED and 07PM.
(blueprint: lem-per-g-quotient-completed-local-comparison)

Proof:
1. Put `C = AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B`, `p = Q ∩ B`, `A = B_p`
   and `D = C_Q`. Completion is Noetherian (0316) and flat (00MB), so the
   localized map `A → D` is flat and local (00HT). The containment `JC ≤ Q`
   implies `J ≤ p`.
2. For `E = B/J`, the finite-module completion/tensor isomorphism (00MA) gives
   `C/JC ≅ completion(E)` as rings, compatibly with `E`. The G-ring hypothesis
   on `E` makes `E → C/JC` regular (0AH2). Localizing gives the regular local
   map `E_(p/J) → (C/JC)_(Q/JC)` (07C0).
3. Localization of quotients (00CT) identifies this map with `A/JA → D/JD`.
   Since `JD ≤ pD`, its closed fibre is `D/pD`, with the original residue-field
   algebra structure. Regularity gives geometric regularity of this closed fibre.
4. This Noetherian local closed fibre is adically formally smooth over its field
   (07EL). Together with flatness, 07NQ gives formal smoothness of `D` over `A`
   for the maximal-ideal topology of `D`.
5. Their maximal-ideal completions `U` and `T` are Noetherian, local and complete
   (0316, 05GI, 05GG). Tag 07ED gives adic formal smoothness of the induced map
   `U → T`. Its quotient coordinates are induced by `A → D`, precisely as in
   `exists_adicCompletion_map_of_local`; these coordinates also show locality.
6. Tag 07PM, implication (4) to (1), proves this complete-local map regular.
   It is therefore flat; flat local maps are faithfully flat (00HR).
-/
theorem isRegular_completedLocalComparison_of_quotient_isGRing
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Finite (MaximalSpectrum B)]
    (J : Ideal B) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal B)) (hG : IsGRing (B ⧸ J))
    (Q : Ideal (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) [Q.IsPrime]
    (hQ : ¬ Q.IsMaximal)
    (hJQ : J.map (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) ≤ Q) :
    (jacobsonCompletedLocalComparison B Q).IsRegular ∧
    IsLocalHom (jacobsonCompletedLocalComparison B Q) ∧
    (jacobsonCompletedLocalComparison B Q).FaithfullyFlat := by
  sorry

end AdicCompletion
