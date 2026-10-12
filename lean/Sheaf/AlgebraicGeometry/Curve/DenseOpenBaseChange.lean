/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Field extension across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The two conditional field-extension assertions transfer across a dense-open counit
for a constructible sheaf killed by a prime.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and remark (c)
(blueprint: lem-pbc-s2-dense-open-base-change).

Proof: Write G=j_!j^*F and B=i_*i^*F for the reduced closed complement. The complement is
a finite union of k-rational points. Its base change to an algebraically closed extension
is the corresponding union of spectra of that field, and inverse image identifies the
geometric stalks of F at these points with the new stalks. Thus the cohomology pullback
for B is bijective in degree zero (the product of these stalk identifications) and in
positive degrees (both groups are zero). Inverse image preserves the open-closed short
exact sequence and identifies the pullback of G with extension by zero from the base
change of U. The pullback-cohomology ladder is a morphism of long exact sequences with
the canonical cohomologyMap as vertical maps. Since both boundary sheaves have zero
positive cohomology, the higher-degree counit maps are bijective on both rows. Therefore
the field-extension maps for F and G in degrees at least two are bijective together.
For degrees zero and one, use the exact five-term sequence
0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0.
If all vertical maps for G are bijective, the five lemma at H^0(F) and at H^1(F), using
the bijective B map and zero end terms, makes all vertical maps for F bijective. Conversely,
if all vertical maps for F are bijective, the five lemma at H^0(G) and at H^1(G), again
using the bijective B map and zero end terms, gives the maps for G. This proves the proper
base-change assertion. For the invertible-order assertion, if r is invertible in k,
both F and G have invertible-order torsion and the same ladder applies. If r equals the
positive characteristic, any invertible-order hypothesis on either r-torsion sheaf makes
that sheaf zero, since each stalk element is killed by coprime integers. Its pullback is
zero and every comparison is bijective. Constructibility and r-torsion of G follow from
its stalks, which equal those of F on U and vanish off U. These cases prove both conditional
implications, including the empty scheme, the zero sheaf, and the full open. -/
theorem dense_open_base_change (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (BaseChangeOfInvertibleOrder Λ f F ↔ BaseChangeOfInvertibleOrder Λ f G) ∧
    (BaseChangeOfIsProper Λ f F ↔ BaseChangeOfIsProper Λ f G) := by sorry

end AlgebraicGeometry.IsCurve
