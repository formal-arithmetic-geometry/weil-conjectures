/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization

/-!
# Excellence of strict local rings of finite-type field algebras

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-dimension-general.md`, proof, second paragraph;
supporting Stacks Project Tags 07QT, 07QU, and 07QW
(blueprint: lem-exc-field-algebra-strict-henselization-excellent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

/--
If `B` is a finitely generated algebra over a field, then the localization at a
prime and any strict henselization of that local ring are excellent, as are all
quotients of the strict henselization.  In particular the strict henselization
and its reduced quotient are Noetherian.

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-dimension-general.md`, proof, second paragraph;
Stacks Project Tags 07QT, 07QU, 07QW, 06LJ, 04GW, and 092N;
Greco, *Two theorems on excellent rings*, Theorem 5.3(iv), pp. 146–147,
with Remark 5.2
(blueprint: lem-exc-field-algebra-strict-henselization-excellent).

Proof:
1. `lem-exc-fields-excellent` gives excellence of `k`, in every characteristic,
   without a perfectness assumption.
2. Apply `lem-exc-finite-type-localization-excellent` to `B` and the
   multiplicative complement of `p`. This gives excellence of
   `Localization.AtPrime p`, which is a local ring by
   `def-weil-pbc-localization-at-prime`.
3. Excellence includes Noetherianity by `def-exc-excellent-ring`.
   The forward implication of `lem-sc-strict-henselization-noetherian`,
   applied to `hC`, therefore makes `C` Noetherian.
4. By `def-sc-ring-strict-henselization`, `hC` identifies `C` with the colimit
   of etale algebras pointed in `K`. The category is essentially small and
   filtered by `lem-sc-pointed-etale-small-filtered`. Choose a small full
   skeleton and isomorphisms from representatives to all objects, identity
   on representatives. Transporting cocones along these isomorphisms proves
   filteredness of the skeleton. A cocone on it extends to an object `X`
   by composing its representative's leg with the inverse isomorphism to
   `X`. Naturality follows from the morphism between representatives obtained
   by conjugating a morphism `X → Y` by the chosen isomorphisms. Restriction
   and extension are inverse, so the restricted diagram still has colimit
   `C`. Its etale stages have finite presentation by
   `lem-weil-pbc-etale-algebra-finite-presentation-localization`. This is
   precisely an ind-etale presentation under `def-weil-pbc-ind-etale-algebra`.
5. `lem-weil-pbc-ind-etale-stability` makes the map to `C` weakly etale.
   Apply `lem-exc-weakly-etale-excellent` (Greco's theorem): the source is
   excellent by step 2 and the target Noetherian by step 3, so `C` is excellent.
6. For every ideal `I`, the quotient map to `C ⧸ I` is surjective, so the
   empty list generates the quotient as a `C`-algebra. The finite-type clause
   of `lem-exc-finite-type-localization-excellent` makes it excellent.
   This includes the zero ideal and the whole ring, with no properness
   or finite-generation assumption on `I`.
7. The nilpotent elements form the ideal `nilradical C`: if `x^a = y^b = 0`,
   binomial expansion gives `(x + y)^(a + b) = 0`, and additive inverses and
   scalar multiples remain nilpotent. Apply step 6 to this ideal, then use
   `def-exc-excellent-ring` to read off Noetherianity of `C` and its reduction.
-/
theorem isExcellent_localizationAtPrime_strictHenselization
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (p : Ideal B) [p.IsPrime]
    (K C : Type v) [Field K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
    [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
    [Algebra (Localization.AtPrime p) K]
    [IsScalarTower (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
    [CommRing C] [Algebra (Localization.AtPrime p) C]
    (hC : Algebra.IsStrictHenselization (Localization.AtPrime p) K C) :
    IsExcellent (Localization.AtPrime p) ∧ IsExcellent C ∧
      (∀ I : Ideal C, IsExcellent (C ⧸ I)) ∧ IsNoetherianRing C ∧
        IsNoetherianRing (C ⧸ nilradical C) := by
  classical
  have hL : IsExcellent (Localization.AtPrime p) :=
    (isExcellent_finiteType_localization (R := k) (A := B)
      (isExcellent_of_field k) p.primeCompl).1
  have : IsNoetherianRing (Localization.AtPrime p) := hL.1.1
  have hnoeth : IsNoetherianRing C :=
    (Algebra.isNoetherianRing_iff_isStrictHenselization
      (Localization.AtPrime p) K C hC).mp inferInstance
  have hind : Algebra.IndEtale (Localization.AtPrime p) C := by
    let P : CategoryTheory.ObjectProperty
        (CategoryTheory.Over (CommAlgCat.of (Localization.AtPrime p) K)) :=
      fun X ↦ Algebra.Etale (Localization.AtPrime p) X.left
    obtain ⟨c, ⟨hc⟩, ⟨e⟩⟩ := hC
    obtain ⟨hsmall, hfiltered⟩ :=
      Algebra.pointedEtale_small_filtered (Localization.AtPrime p) K
    let : CategoryTheory.EssentiallySmall.{v} P.FullSubcategory := hsmall
    let : CategoryTheory.IsFiltered P.FullSubcategory := hfiltered
    let E := CategoryTheory.equivSmallModel.{v} P.FullSubcategory
    let : CategoryTheory.IsFiltered (CategoryTheory.SmallModel.{v} P.FullSubcategory) :=
      CategoryTheory.IsFiltered.of_equivalence E
    let pres : CategoryTheory.Limits.ColimitPresentation P.FullSubcategory c.pt :=
      ⟨_, c.ι, hc⟩
    refine ⟨CategoryTheory.SmallModel.{v} P.FullSubcategory, inferInstance, inferInstance,
      (pres.reindex E.inverse).ofIso e, ?_⟩
    intro i
    exact (E.inverse.obj i).property
  have hweak : (algebraMap (Localization.AtPrime p) C).WeaklyEtale :=
    RingHom.indEtale_principalZariski_stability.2.2.2.2.2.2.1
      (Localization.AtPrime p) C _
      ((RingHom.IndEtale.algebraMap_iff (Localization.AtPrime p) C).mpr hind)
  have hexc : IsExcellent C :=
    RingHom.isExcellent_of_weaklyEtale (algebraMap (Localization.AtPrime p) C) hL hweak
  have hquot (I : Ideal C) : IsExcellent (C ⧸ I) :=
    (isExcellent_finiteType_localization (R := C) (A := C ⧸ I) hexc ⊥).2
  exact ⟨hL, hexc, hquot, hnoeth, (hquot (nilradical C)).1.1⟩

end
