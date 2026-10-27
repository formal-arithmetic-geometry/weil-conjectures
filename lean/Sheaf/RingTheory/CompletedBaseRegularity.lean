/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularLocalMaximal

/-!
# Regularity after completing the base of a continuous adic map

Source: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero:
the non-embedded case, arXiv:0904.1592v2, Lemma 2.4.4, printed p.16, with the explicit ideal
of definition used in Corollary 2.4.5 (blueprint: lem-per-completed-base-regularity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- A continuous map from the completion of a quasi-excellent ring to a complete Noetherian
adic ring is regular exactly when its composite with the completion map is regular.
Completeness is for `J`; the image of the extended ideal `I` is only required to lie in `J`.

Source: Temkin, arXiv:0904.1592v2, Lemma 2.4.4 and Corollary 2.4.5, printed p.16
(blueprint: lem-per-completed-base-regularity).

Proof:
1. Suppose `f` is regular. Quasi-excellence makes `A` a G-ring
   (`def-exc-excellent-ring`), so its completion map is regular by
   `lem-weil-pbc-g-ring-completion-regular`. Every fibre of the composite is a quotient
   of a localization of the Noetherian ring `B`; it is therefore Noetherian by
   `lem-weil-pbc-localization-noetherian` and finite generation of ideals in quotients.
   Apply `lem-weil-pbc-regular-composition`.
2. Conversely suppose the composite is regular, and write `C` for the completion of `A`.
   By `lem-per-quasi-excellent-formal-affines`, `C` is Noetherian and quasi-excellent,
   hence a G-ring (`def-exc-excellent-ring`, `def-weil-pbc-g-ring`). By
   `lem-weil-pbc-regular-local-maximal`, it suffices to treat the local map at every
   maximal ideal `q` of `B`, with inverse images `p` in `C` and `r` in `A`. If `B` is
   zero there are no maximal ideals, so this criterion already concludes.
3. Completeness for `J` makes each `1 - b*x`, for `x` in `J`, invertible: the compatible
   finite geometric sums modulo the powers of `J` supply its inverse. Thus `J` lies in
   every maximal ideal, and continuity gives `I*C` contained in `p`. By
   `lem-weil-pbc-adic-completion-mod-ideal`, `A/I` is canonically isomorphic to `C/(I*C)`.
   Hence `p = r*C`, `A/r` is canonically isomorphic to `C/p`, and their fraction fields
   give the same residue field, with its canonical action.
4. Put `R = A_r`, `D = C_p`, `T = B_q`, and let `a : R → D`, `g : R → T`, `h : D → T`
   be the induced local maps, so `g = h*a`. The map `a` is flat by
   `lem-weil-pbc-noetherian-completion-flat` and `lem-weil-pbc-flat-local-ring-maps`.
   The local rings are Noetherian by `lem-weil-pbc-localization-noetherian`. Step 3
   identifies maximal ideals and residue fields, so `lem-weil-pbc-flat-local-completion-iso`
   makes the canonical completed map of `a` an isomorphism. The local map `g` is regular
   by `lem-weil-pbc-regular-local-maximal`.
5. On every quotient level the completed maps respect composition. Since `g` is flat,
   its completed map is flat by `lem-weil-pbc-flat-completion`; the completion of `h`
   is flat after the isomorphism from step 4. Compose with the flat completion map of
   `D`, using `lem-weil-pbc-noetherian-completion-flat` and
   `lem-weil-pbc-flat-ring-map-comp`. The result is `D → T → completion(T)`.
   The last map is faithfully flat by `lem-weil-pbc-local-completion-faithfully-flat`;
   `lem-weil-pbc-flat-algebra-faithfully-flat-descent` shows that `h` is flat.
6. Step 3 identifies the closed fibre of `h` with that of `g`, including its residue-field
   action, so it is geometrically regular. The completion map of `D` is regular by
   step 2 and `def-weil-pbc-g-ring`. Apply `lem-per-g-ring-local-closed-fibre-criterion`
   to obtain regularity of `h`, and `lem-weil-pbc-regular-local-maximal` to conclude.
-/
theorem isRegular_iff_comp_adicCompletion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (hA : IsQuasiExcellent A) (I : Ideal A) [IsNoetherianRing B]
    (J : Ideal B) [IsAdicComplete J B] (f : AdicCompletion I A →+* B)
    (hcont : Ideal.map f (Ideal.map (algebraMap A (AdicCompletion I A)) I) ≤ J) :
    f.IsRegular ↔ (f.comp (algebraMap A (AdicCompletion I A))).IsRegular := by
  sorry

end RingHom
