/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.RingTheory.GRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# A compatible henselian G-ring stage for a finite étale closed-fibre cover

Source: Stacks Project, Tag 0GS2, proof, General case.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite étale cover of the closed fibre descends to a proper scheme over a henselian
G-ring, with maps from the original scheme and its closed fibre that commute with the
closed-fibre inclusions. This constructs the stage only; it does not lift the cover.

Source: Stacks Project, Tag 0GS2, proof, General case, using Tags 0A0P, 01ZM, 01ZO,
07RP, 07PX, 0A02, 0A04 and 0AH3.
(blueprint: lem-weil-pbc-finite-etale-henselian-g-ring-stage).

Proof:
1. Approximate Y over Spec A by proper Y_i over Spec A_i, where the A_i are finitely
   generated over Z, with affine transitions and limit Y (Tag 0A0P). The affine
   bases have ring colimit A. Put I_i equal to the inverse image of I in A_i.
2. The quotients A_i/I_i have colimit A/I: every element lifts from a stage, and an
   element vanishes in A/I precisely when its representative belongs to I_i. The
   closed fibres Y_i,0 have affine transitions and limit Y_0, since spectra turn
   these ring colimits into limits and fibre products commute with limits.
3. Descend V to a finitely presented cover of some Y_i,0 by Tag 01ZM. By Tags 01ZO
   and 07RP and directedness, increase i until this cover is finite and étale.
4. Henselize (A_i,I_i), obtaining (B,J). The ring A_i is a Noetherian G-ring by
   Tag 07PX, so B is a G-ring by Tag 0AH3. Tag 0A02 gives a henselian pair and
   A_i/I_i isomorphic to B/J. The map A_i to A extends to B to A by the
   henselization universal property (also the specialization in Tag 0A04), and
   this extension sends J into I.
5. Put Z = Y_i times Spec B over Spec A_i and let g be its proper projection.
   Pullback universality gives s : Y to Z from the limit projection and B to A.
   The quotient isomorphism identifies the closed fibre of Z with Y_i,0;
   transport the descended cover across this identification to obtain W.
6. The induced quotient map B/J to A/I and the closed-fibre limit projection give
   k : Y_0 to Z_0. Both sides of j_Y followed by s = k followed by j_Z have the
   same projections to Y_i and Spec B, so they agree by pullback extensionality.
   Base change of the descended cover along k gives V, as an isomorphism over Y_0.
   No lifting theorem for arbitrary henselian pairs is used in these steps. -/
theorem exists_finiteEtale_henselian_gRing_stage
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsGRing B)
      (J : Ideal B) (_ : HenselianRing B J) (Z : Scheme.{u})
      (g : Z ⟶ Spec (.of B)) (_ : IsProper g) (s : Y ⟶ Z)
      (k : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
      (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
        (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ s =
        k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ∧
      Nonempty (Over.mk (pullback.snd W.hom k) ≅ Over.mk V.hom) := by sorry

end AlgebraicGeometry.Scheme
