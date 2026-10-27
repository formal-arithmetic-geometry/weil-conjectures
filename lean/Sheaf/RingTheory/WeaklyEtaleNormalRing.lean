/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Sheaf.RingTheory.FaithfullyFlatNormalRingDescent
import all Sheaf.RingTheory.GeometricallyNormalTensorNormal

/-!
# Normality ascends along weakly etale ring maps

Source: Stacks Project, More on Morphisms, Tag 0950 (lemma-normal-goes-up), affine case.
The proof follows the refinement route through Tags 097Z, 033C, 037D and 033G
(blueprint: lem-sfb-weakly-etale-normal-ring-ascent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

private theorem indEtale_normal {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨I, cI, hI, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  let U := CategoryTheory.forget₂ (CommAlgCat R) CommRingCat
  have : CategoryTheory.Limits.PreservesColimitsOfShape I U := by
    change CategoryTheory.Limits.PreservesColimitsOfShape I
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor.comp
        (CategoryTheory.Under.forget _))
    infer_instance
  let Q := P.map U
  have hstage (i : I) : ∀ (p : Ideal (P.diag.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    RingHom.Etale.isNormalRing
      (etale_algebraMap.mpr (hP i) : (algebraMap R (P.diag.obj i)).Etale) hR
  have hn := CommRingCat.isNormal_of_filtered_colimit Q.diag (fun i ↦ by
    change ∀ (p : Ideal (P.diag.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)
    exact hstage i)
  let e := (CategoryTheory.Limits.colimit.isColimit Q.diag).coconePointUniqueUpToIso Q.isColimit
  exact Algebra.normal_equiv e.commRingCatIsoToRingEquiv hn

private theorem weaklyEtale_normal_same {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.WeaklyEtale)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨T, hT, g, _, hg, hgf⟩ := hf.exists_indEtale_comp
  let : Algebra R T := (g.comp f).toAlgebra
  let : Algebra.IndEtale R T := hgf
  have hn := indEtale_normal (R := R) (S := T) hR
  let : Algebra S T := g.toAlgebra
  let : Module.FaithfullyFlat S T := hg
  exact Algebra.normal_ring_of_faithfullyFlat S T hn

/-- A weakly etale map from a normal commutative ring has normal target, without
Noetherian, domain, locality, finite-presentation or faithful-flatness assumptions.
The two rings may belong to different universes, and zero rings are allowed.

Source: Stacks Project, More on Morphisms, Tag 0950 (lemma-normal-goes-up), affine case;
refinement proof using Tags 097Z, 033C, 037D and 033G
(blueprint: lem-sfb-weakly-etale-normal-ring-ascent).

Proof:
1. Place both rings in a common universe by canonical universe lifts. Ring isomorphisms
   preserve prime localizations, monic equations and flatness of tensor multiplication,
   hence normality and weak etaleness. Apply
   lem-weil-pbc-existing-weakly-etale-indetale-refinement (097Z) to obtain a faithfully
   flat ind-etale map B -> C with ind-etale composite A -> C. Only the refinement map
   is required to be faithfully flat.
2. By def-weil-pbc-ind-etale-algebra, express C as a small filtered colimit of finitely
   presented etale A-algebras C_i. Their spectrum maps are etale (02GI). Apply
   lem-weil-pbc-etale-over-normal-ring-normal (033C) to each stage and the normal base A.
   Every C_i is normal, without requiring A to be a domain.
3. The forgetful functor from A-algebras to rings preserves filtered colimits: the ring
   colimit receives the common A-map through any stage, independent of the stage by
   filteredness, and satisfies the algebra-colimit universal property. Thus
   lem-weil-pbc-filtered-colimit-normal-ring (037D) makes C normal. Transition maps need
   not be injective, and no Noetherian condition is used.
4. Apply lem-sfb-faithfully-flat-normal-ring-descent (033G) to B -> C. Every prime
   localization of B is therefore an integrally closed domain. Transport back across
   any universe lifts. When B is zero there are no primes; if A is zero, unitality
   forces B to be zero as well. -/
theorem WeaklyEtale.isNormalRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.WeaklyEtale)
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' _ _
  have hf' : Algebra.WeaklyEtale (ULift.{v} A) (ULift.{u} B) :=
    Algebra.WeaklyEtale.ulift_iff.mpr hf
  have hn := weaklyEtale_normal_same
    (weaklyEtale_algebraMap_iff.mpr hf')
    (Algebra.normal_equiv ULift.ringEquiv.symm hA)
  exact Algebra.normal_equiv ULift.ringEquiv hn

end RingHom
