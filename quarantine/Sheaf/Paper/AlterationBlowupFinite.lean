module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.GDelta.Basic
import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Gluing
import WeilConjectures.Compactification.StrictTransform
import Sheaf.AlgebraicGeometry.FiniteAfterBlowup
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.Proper
import WeilConjectures.Compactification.StrictTransformBlowup

/-!
# Blowup refinement of an alteration

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 2.5, p. 4,
and Lemma 3.2.1 proof, p. 8 (blueprint: lem-trf-alteration-blowup-finite).

The statement uses the canonical blow-up `IdealSheafData.blowup` of an ideal sheaf. The
center `R` is the closed subscheme `I.subscheme` of an ideal sheaf `I` on the target, with closed
immersion `I.subschemeι`, and `Bl_R(Z)` is `I.blowup`; the source blow-up modification is the
canonical blow-up `J.blowup` of an ideal sheaf `J` on the source (in the proof, the strict
transform, identified with the blow-up of the extended ideal `I𝒪_W`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Orgogozo

/-- An alteration of integral reduced Noetherian schemes admits blow-up modifications making its
strict transform finite and surjective over the target blow-up.
Source: Orgogozo, Lemma 2.5, p. 4, and Lemma 3.2.1 proof, p. 8
(blueprint: lem-trf-alteration-blowup-finite).

Proof. By properness and generic flatness, restrict the alteration to a nonempty affine open on
which it is finite, flat, and locally of finite presentation. Apply the finite-after-admissible-
blow-up theorem to obtain an admissible blow-up of the target whose strict transform is finite
locally free. The admissible center is disjoint from the chosen dense open, hence nowhere dense,
and the target blow-up is a modification. The finite strict transform is proper and has closed
image containing the dense inverse image of the chosen open, so it is surjective. The strict
transform is the blow-up of the extended center on the source; it is therefore a blow-up
modification, and the defining pullback square gives the displayed compatibility over the target.
The cited steps use `def-trf-orgogozo-induction-data`, `def-nagata-global-blowup`,
`def-weil-closed-immersion`, `def-weil-finite-integral-morphism`, and the finite-after-blow-up
and strict-transform statements recorded in the DAG.
-/
theorem exists_blowup_finite_surjective
    {W Z : Scheme.{u}} [IsIntegral W] [IsIntegral Z] [IsReduced W] [IsReduced Z]
    [IsNoetherian W] [IsNoetherian Z] (a : W ⟶ Z) (ha : IsAlteration a) :
    ∃ (I : Z.IdealSheafData),
      IsNowhereDense (I.support : Set Z) ∧ IsClosedImmersion I.subschemeι ∧
      IsModification I.blowupMap ∧
      ∃ (J : W.IdealSheafData), IsModification J.blowupMap ∧
        ∃ (p : J.blowup ⟶ I.blowup),
          IsFinite p ∧ Surjective p ∧
            J.blowupMap ≫ a = p ≫ I.blowupMap := by
  sorry

end AlgebraicGeometry.Orgogozo
