/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.FieldTheory.SeparableClosure
import Sheaf.RingTheory.EtaleHenselianRingLift
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift

/-! # Strict localizations above the closed point of a strict-local base change

Source: Stacks Project, Tags 0GIP (case (2)), 0GJS and 0GJU, first paragraph
(blueprint: lem-weil-pbc-strict-base-closed-point-localizations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Strict-local base change preserves strict localizations above its closed point.
Source: Stacks Project, Tags 0GIP (case (2)), 0GJS and 0GJU, first paragraph
(blueprint: lem-weil-pbc-strict-base-closed-point-localizations).

`hcart` allows any presentation of the specified fibre product. The canonical
closed-point lift is `Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s))`.
The functorial maps `b`, `d`, `q` are specified by their structural equations and their
compatibility with the canonical geometric-point lifts. By strict-henselization
functoriality these are precisely the canonical maps, not arbitrary maps over the base.
Here `b` is the map from the strict localization of the new base to that of the old
base, `d` is the strict-local map induced by `f`, and `q` is induced by `p`.

Proof:
1. Functoriality identifies the residue field of the strictly henselian base ring
with the separable algebraic closure of the original residue field in Ω. The equation
`hclosed` puts the new point at its closed point, with this fixed embedding into Ξ.
2. For each affine pointed etale neighbourhood of the new base, its pointed residue
field is finite separable over the separably closed base residue field, hence equal to it
(`lem-weil-pbc-etale-algebra-residue-field-separable`). Henselian etale lifting
(`lem-sc-etale-henselian-ring-lift`) supplies a unique section. Compatibility of these
sections and the colimit universal property show that the first structural map is an
isomorphism.
3. The relative separable closure of the original residue field in Ξ is the image of
its relative separable closure in Ω: a separable polynomial already splits over the
latter. Thus the etale-local-ring triple diagrams agree, yielding the specified base
isomorphism `e`. Functoriality gives its displayed composite with the first map as `b`.
4. Restrict to affine charts. The strict-local base ring is ind-etale over the chart
(`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`). Apply
`lem-weil-pbc-ind-etale-affine-strict-local-base-change` on those charts, and transport
by `lem-weil-pbc-etale-local-ring-triples`. Its comparison identifies the source of `q`
with the pullback of its target along `b`.
5. Since the two base maps are isomorphisms, the pullback projection and hence `q` are
isomorphisms. The structural and pointed equations identify these with the canonical
maps. The pullback equation gives the compatibility over the new base; `hq` gives
compatibility over X.
6. Pull back `q` and its inverse along any geometric point `t` of the new base, using
`e` to identify bases. The two projection equations give inverse morphisms and show
the resulting isomorphism is over X. No algebraicity of either extension is used. -/
theorem strictBaseClosedPointLocalizations
    {X S X' : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ strictHenselizationScheme s)
    (hcart : IsPullback p f' f (strictHenselizationStructuralMap s))
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (x' : Spec (.of Ξ) ⟶ X')
    (a : Spec (.of Ξ) ⟶ Spec (.of Ω))
    (hclosed : x' ≫ f' =
      a ≫ Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s)))
    (b : strictHenselizationScheme (x' ≫ f') ⟶
      strictHenselizationScheme ((x' ≫ p) ≫ f))
    (hb : b ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      strictHenselizationStructuralMap (x' ≫ f') ≫ strictHenselizationStructuralMap s)
    (hbpoint : Spec.map (CommRingCat.ofHom
        (strictHenselizationPointEvaluation (x' ≫ f'))) ≫ b =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation ((x' ≫ p) ≫ f))))
    (d : strictHenselizationScheme (x' ≫ p) ⟶
      strictHenselizationScheme ((x' ≫ p) ≫ f))
    (hd : d ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      strictHenselizationStructuralMap (x' ≫ p) ≫ f)
    (hdpoint : Spec.map (CommRingCat.ofHom
        (strictHenselizationPointEvaluation (x' ≫ p))) ≫ d =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation ((x' ≫ p) ≫ f))))
    (q : strictHenselizationScheme x' ⟶ strictHenselizationScheme (x' ≫ p))
    (hq : q ≫ strictHenselizationStructuralMap (x' ≫ p) =
      strictHenselizationStructuralMap x' ≫ p)
    (hqpoint : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x')) ≫ q =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x' ≫ p)))) :
    IsIso (strictHenselizationStructuralMap (x' ≫ f')) ∧ IsIso q ∧
      ∃ e : strictHenselizationScheme s ≅ strictHenselizationScheme ((x' ≫ p) ≫ f),
        strictHenselizationStructuralMap (x' ≫ f') ≫ e.hom = b ∧
        q ≫ d = (strictHenselizationStructuralMap x' ≫ f') ≫ e.hom ∧
        ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
          (t : Spec (.of Ω') ⟶ strictHenselizationScheme s),
          ∃ E : pullback (strictHenselizationStructuralMap x' ≫ f') t ≅
              pullback d (t ≫ e.hom),
            E.hom ≫ pullback.fst d (t ≫ e.hom) =
              pullback.fst (strictHenselizationStructuralMap x' ≫ f') t ≫ q ∧
            E.hom ≫ pullback.snd d (t ≫ e.hom) =
              pullback.snd (strictHenselizationStructuralMap x' ≫ f') t := by
  sorry

end AlgebraicGeometry.Scheme
