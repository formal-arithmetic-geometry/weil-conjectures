/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift

/-! # Ind-etale affine strict-local base change

Source: Stacks Project, Tag 0GIP, case (2), and Tag 0GJS, the displayed strict-local
ring comparison (blueprint: lem-weil-pbc-ind-etale-affine-strict-local-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical comparison of strict localizations is an isomorphism for an ind-etale
map on one side of an affine fibre product. The four functorial maps are specified by
commuting with the structural maps and with the canonical geometric-point evaluations.
These are the pointed maps of `strictHenselizationFunctoriality`; their existence is part
of the conclusion, so no choices of residue identifications or local-ring instances are
extra hypotheses. The isomorphism is uniquely characterized by its two projections.

Source: Stacks Project, Tag 0GIP, case (2), and Tag 0GJS
(blueprint: lem-weil-pbc-ind-etale-affine-strict-local-base-change).

Proof:
1. Identify the original affine fibre product with Spec of B tensor_A C, using
   lem-weil-pbc-fibre-product-affine-spectra. Strict-henselization functoriality supplies
   the four pointed local maps, and its uniqueness makes their square commute.
2. By lem-weil-pbc-strict-henselization-affine-chart-ind-etale, the maps from A, B, C,
   and B tensor_A C to their strict-local rings are ind-etale. Composition, base change,
   and the relative-map clause of lem-weil-pbc-ind-etale-stability imply that the maps
   from the strict-local A ring to the strict-local B ring and from the strict-local C
   ring to the strict-local tensor ring are ind-etale, hence weakly etale.
3. Functoriality makes these local maps of strictly henselian local rings. Apply
   thm-weil-pbc-weak-etale-strict-local (Olivier's theorem) to both. Thus u and m below
   are isomorphisms.
4. The second projection of pullback u v is an isomorphism since u is. Its inverse is
   the pair (v followed by u inverse, identity). Compose this inverse with m to obtain
   the comparison isomorphism. The commuting square gives its first projection l;
   its second projection is m. The pullback universal property gives uniqueness and,
   using the structural equations for l and m, compatibility with the map to Y.
No finiteness of A to C or algebraicity of the geometric-point field is used. -/
theorem indEtale_affine_strictLocal_baseChange
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : A ⟶ C)
    (hf : f.hom.IndEtale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ pullback (Spec.map f) (Spec.map g))
    (barB : Spec (.of Ω) ⟶ Spec B) (barC : Spec (.of Ω) ⟶ Spec C)
    (barA : Spec (.of Ω) ⟶ Spec A)
    (hbarB : barB = barY ≫ pullback.fst (Spec.map f) (Spec.map g))
    (hbarC : barC = barY ≫ pullback.snd (Spec.map f) (Spec.map g))
    (hbarA : barA = barB ≫ Spec.map f) :
    ∃ (u : strictHenselizationScheme barB ⟶ strictHenselizationScheme barA)
      (v : strictHenselizationScheme barC ⟶ strictHenselizationScheme barA)
      (hu : u ≫ strictHenselizationStructuralMap barA =
        strictHenselizationStructuralMap barB ≫ Spec.map f)
      (hv : v ≫ strictHenselizationStructuralMap barA =
        strictHenselizationStructuralMap barC ≫ Spec.map g),
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barB)) ≫ u =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barA)) ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barC)) ≫ v =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barA)) ∧
      ∃ (l : strictHenselizationScheme barY ⟶ strictHenselizationScheme barB)
        (m : strictHenselizationScheme barY ⟶ strictHenselizationScheme barC),
        l ≫ strictHenselizationStructuralMap barB =
          strictHenselizationStructuralMap barY ≫
            pullback.fst (Spec.map f) (Spec.map g) ∧
        m ≫ strictHenselizationStructuralMap barC =
          strictHenselizationStructuralMap barY ≫
            pullback.snd (Spec.map f) (Spec.map g) ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫ l =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barB)) ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫ m =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barC)) ∧
        ∃! e : strictHenselizationScheme barY ≅ pullback u v,
          e.hom ≫ pullback.fst u v = l ∧
          e.hom ≫ pullback.snd u v = m ∧
          e.hom ≫ pullback.map u v (Spec.map f) (Spec.map g)
            (strictHenselizationStructuralMap barB)
            (strictHenselizationStructuralMap barC)
            (strictHenselizationStructuralMap barA) hu hv =
              strictHenselizationStructuralMap barY := by
  sorry

end AlgebraicGeometry.Scheme
