module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.NormalOfFlatNormalFibers
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Normal local completions over a quasi-excellent closed fibre

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 1 (1-4), printed p. 8, and (5.3), printed p. 9
(blueprint: lem-per-adic-normal-completion-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- If a Noetherian normal domain is complete along an ideal with quasi-excellent
quotient, the maximal-ideal completion of each prime localization is a normal local domain.
Source: Kurano–Shimomoto, Theorem 5.1, Step 1 (1-4), printed p. 8, and (5.3), printed p. 9
(blueprint: lem-per-adic-normal-completion-lifting).

Proof:
1. Put `Q = A / I`. Quasi-excellence makes `Q` Nagata
   (`lem-exc-quasi-excellent-nagata`) and a G-ring (`def-exc-excellent-ring`). Its formal
   fibres become regular after finite purely inseparable residue-field extensions
   (`def-weil-pbc-g-ring`), hence normal (`lem-weil-pbc-regular-ring-normal`). Thus `Q`
   satisfies the condition `N(Q)` of `lem-per-nagata-normal-formal-fibres-lifting`.
2. Apply that lifting theorem to the original complete pair `(A, I)` to obtain `N(A)`.
   Taking the identity residue-field extension gives normal fibres of every local
   completion map. No completeness of a localization is assumed.
3. Fix `p`, put `B = A_p`, and let `C` be its maximal-ideal completion. Localization
   preserves Noetherianity and normal domains (`lem-weil-pbc-localization-noetherian`,
   `lem-weil-pbc-localization-normal-domain`); further localization makes `B` a normal
   ring. Completion is Noetherian (`lem-weil-pbc-adic-completion-noetherian`), local
   with the same nonzero residue field (`lem-weil-pbc-local-completion-local-ring`),
   and faithfully flat over `B` (`lem-weil-pbc-local-completion-faithfully-flat`).
4. Apply `lem-weil-pbc-flat-normal-fibres-noetherian-normal` to `B → C`: both rings
   are Noetherian, the map is flat, and its base and every fibre are normal. Hence
   `C` is a normal ring.
5. Localize `C` at its maximal ideal. Normality says that this localization is a
   normal domain (`def-weil-pbc-normal-ring`). All denominators are already units,
   so the localization map is an isomorphism. Thus `C` itself is a normal local domain.
-/
theorem normal_atPrime_of_isQuasiExcellent_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (I : Ideal A) [IsAdicComplete I A] (hquot : IsQuasiExcellent (A ⧸ I))
    (p : Ideal A) [p.IsPrime] :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) ∧
    IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) := by
  sorry

end AdicCompletion
