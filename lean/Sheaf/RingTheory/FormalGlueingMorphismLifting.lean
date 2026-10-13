/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.FormalGlueingComplexExact
import Sheaf.Paper.FormalGlueingCanonicalMaps

/-!
# Lifting morphisms of canonical formal glueing data

Source: Stacks Project, More on Algebra, Lemmas 05EK and 05EM.
(blueprint: lem-weil-pbc-formal-glueing-morphism-lifting).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- Every morphism between canonical objects lifts to a linear map.
Source: Stacks, More on Algebra, Lemmas 05EK and 05EM; steps 3–4 and 6 of
Proposition 05ER's formal-glueing equivalence proof.
(blueprint: lem-weil-pbc-formal-glueing-morphism-lifting).
Proof: for a morphism z and m in M, form the tuple (z.prime (1 tensor m),
(z.chart i (m/1))_i). The prime compatibility equation says its first compatibility
difference is zero under the canonical comparison. The chart compatibility equation
says the two chart values agree in the iterated localization. Clearing both denominators
shows they agree in the product localization, so every overlap difference is zero.
Exactness of the formal glueing complex produces a preimage in N; its injective initial
map makes that preimage unique. Define u(m) by this unique preimage. Injectivity applied
to the images of sums and scalar multiples proves that u is linear. On pure tensors,
u extended to S agrees with z.prime. On m/1 each localized u agrees with z.chart i;
uniqueness for localization extends this to every fraction. Thus Can.map u = z by
componentwise equality. Empty chart families are covered by the same exact complex;
zero charts and zero modules do not require cancellation in R. -/
theorem canonical_map_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hmap : (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (M N : ModuleCat.{max u v w} R) :
    Function.Surjective (Can.map : (M ⟶ N) → (Can.obj M ⟶ Can.obj N)) := by
  sorry

end FormalGlueing
