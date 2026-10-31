/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest

/-!
# A specialization trait with two sections and reduced closed fibre

Source: Stacks Project, More on Morphisms, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, second proof paragraph.
(blueprint: lem-trf-flat-reduced-specialization-trait-data)

In the statement, `S = Spec (.of R)`, `b = a ≫ g`, `X = pullback g b`,
`f = pullback.snd g b`, and `r = pullback.fst g b`. The two projection equations
for each section uniquely specify the base-changed section and the graph section.
Geometric fibres are taken over the canonical algebraic closures of residue fields.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsLocalRing TopologicalSpace

namespace AlgebraicGeometry

/-- Trace a strict specialization by a DVR and pull back the family, retaining its
section, the graph section, and reducedness and Noetherianity of the closed fibre.

Source: Stacks Project, Tag 055Q, second proof paragraph.
(blueprint: lem-trf-flat-reduced-specialization-trait-data)

Proof:
1. Apply `exists_trait_of_strict_specializes` to obtain the DVR and the map `a`.
   Put `S = Spec R`, `b = a ≫ g`, and let `f` and `r` be the pullback projections.
2. Base-change instances preserve flatness, local finite presentation,
   quasi-compactness and quasi-separatedness. A DVR is Noetherian. Local finite
   presentation implies local finite type, so the total space and the closed
   fibre are Noetherian. The closed fibre's topological Noetherianity follows
   from `IsNoetherian.noetherianSpace`.
3. Pullback pasting identifies the original geometric fibre with the
   algebraic-closure base change of the ordinary fibre. Apply
   `geometricallyReduced_iff_isReduced_pullback_algebraicClosure` to the latter.
   The cartesian square of ordinary fibres transports geometric reducedness to
   the new closed fibre. Its residue field is reduced and Noetherian, so
   `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` gives ordinary
   reducedness. Geometric reducedness applied to the canonical algebraic closure,
   followed by pullback pasting, gives the required geometric reducedness claim.
4. Construct both sections by `pullback.lift`. Their projection equations give
   the two section identities and the graph's required point images.
5. Apply `section_component_preimage_of_isPullback` to identify the component
   loci. The graph's closed point maps to `q`, which belongs to the original
   component locus. Its section identity identifies its image in the trait with
   the closed point, giving the final connected-component assertion. -/
theorem exists_flat_reduced_specialization_trait_data
    {P T : Scheme.{u}} [IsNoetherian P] [IsNoetherian T]
    (g : P ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    {p q : P} (hpq : p ⤳ q) (hne : p ≠ q)
    (hq : q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q)))
    (hred : IsReduced (pullback g
      (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (g q))
        (AlgebraicClosure (T.residueField (g q))))) ≫ T.fromSpecResidueField (g q)))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (a : Spec (.of R) ⟶ P),
      a (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) = p ∧ a (closedPoint R) = q ∧
      Flat (pullback.snd g (a ≫ g)) ∧
      LocallyOfFinitePresentation (pullback.snd g (a ≫ g)) ∧
      QuasiCompact (pullback.snd g (a ≫ g)) ∧
      QuasiSeparated (pullback.snd g (a ≫ g)) ∧
      IsNoetherian (Spec (.of R)) ∧ IsNoetherian (pullback g (a ≫ g)) ∧
      IsNoetherian ((pullback.snd g (a ≫ g)).fiber (closedPoint R)) ∧
      NoetherianSpace ((pullback.snd g (a ≫ g)).fiber (closedPoint R)) ∧
      IsReduced (pullback (pullback.snd g (a ≫ g))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((Spec (.of R)).residueField (closedPoint R))
            (AlgebraicClosure ((Spec (.of R)).residueField (closedPoint R))))) ≫
          (Spec (.of R)).fromSpecResidueField (closedPoint R))) ∧
      IsReduced ((pullback.snd g (a ≫ g)).fiber (closedPoint R)) ∧
      ∃ (σR τ : Spec (.of R) ⟶ pullback g (a ≫ g)),
        σR ≫ pullback.snd g (a ≫ g) = 𝟙 (Spec (.of R)) ∧
        τ ≫ pullback.snd g (a ≫ g) = 𝟙 (Spec (.of R)) ∧
        σR ≫ pullback.fst g (a ≫ g) = (a ≫ g) ≫ σ ∧
        τ ≫ pullback.fst g (a ≫ g) = a ∧
        pullback.fst g (a ≫ g) (τ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) = p ∧
        pullback.fst g (a ≫ g) (τ (closedPoint R)) = q ∧
        {x : ↥(pullback g (a ≫ g)) |
          x ∈ connectedComponentIn
            ((pullback.snd g (a ≫ g)) ⁻¹' {pullback.snd g (a ≫ g) x})
            (σR (pullback.snd g (a ≫ g) x))} =
          (pullback.fst g (a ≫ g)) ⁻¹'
            {y : P | y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y))} ∧
        τ (closedPoint R) ∈ connectedComponentIn
          ((pullback.snd g (a ≫ g)) ⁻¹' {closedPoint R}) (σR (closedPoint R)) := by
  obtain ⟨R, hR, hdom, hdvr, a, haq, hap⟩ :=
    exists_trait_of_strict_specializes hpq hne
  let S := Spec (.of R)
  let b : S ⟶ T := a ≫ g
  let f : pullback g b ⟶ S := pullback.snd g b
  let r : pullback g b ⟶ P := pullback.fst g b
  let s : S := closedPoint R
  have hbs : b s = g q := by
    change g (a (closedPoint R)) = g q
    rw [haq]
  have : IsNoetherian S := inferInstance
  have : IsNoetherian (pullback g b) := {}
  have : IsNoetherian (f.fiber s) := by
    have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd f (S.fromSpecResidueField s) inferInstance
    exact { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s) }
  -- Compare the ordinary fibre after scalar extension with the geometric fibre.
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (T.residueField (g q)) (AlgebraicClosure (T.residueField (g q)))))
  have : IsReduced (pullback g (j ≫ T.fromSpecResidueField (g q))) := hred
  have hredg : IsReduced (pullback (g.fiberToSpecResidueField (g q)) j) :=
    isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g (T.fromSpecResidueField (g q)) j).hom
  let := g.fiberOverSpecResidueField (g q)
  have hggeom : GeometricallyReduced (g.fiberToSpecResidueField (g q)) :=
    (geometricallyReduced_iff_isReduced_pullback_algebraicClosure
      (T.residueField (g q)) (g.fiber (g q))
      (AlgebraicClosure (T.residueField (g q)))).mpr hredg
  have : GeometricallyReduced (g.fiberToSpecResidueField (b s)) := by
    rw [hbs]
    exact hggeom
  have : GeometricallyReduced (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback g b) s) inferInstance
  have hfred : IsReduced (f.fiber s) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (f.fiberToSpecResidueField s)
  let jR := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))
  have hredR : IsReduced (pullback (f.fiberToSpecResidueField s) jR) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  have : IsReduced (pullback (pullback.snd f (S.fromSpecResidueField s)) jR) := hredR
  have hgeomred : IsReduced (pullback f (jR ≫ S.fromSpecResidueField s)) :=
    isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) jR).inv
  let σR : S ⟶ pullback g b :=
    pullback.lift (b ≫ σ) (𝟙 S) (by simp [Category.assoc, hσ])
  let τ : S ⟶ pullback g b := pullback.lift a (𝟙 S) (by simp [b])
  have hσRsnd : σR ≫ f = 𝟙 S := pullback.lift_snd _ _ _
  have hτsnd : τ ≫ f = 𝟙 S := pullback.lift_snd _ _ _
  have hσRfst : σR ≫ r = b ≫ σ := pullback.lift_fst _ _ _
  have hτfst : τ ≫ r = a := pullback.lift_fst _ _ _
  have hτpoint (z : S) : r (τ z) = a z := by
    rw [← Scheme.Hom.comp_apply, hτfst]
  have hτbase (z : S) : f (τ z) = z := by
    rw [← Scheme.Hom.comp_apply, hτsnd]
    rfl
  have hc := (section_component_preimage_of_isPullback g σ hσ r f b
    (IsPullback.of_hasPullback g b) σR hσRsnd hσRfst).symm
  refine ⟨R, hR, hdom, hdvr, a, hap, haq, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hgeomred, hfred, σR, τ, hσRsnd, hτsnd, hσRfst, hτfst,
    (hτpoint _).trans hap, (hτpoint _).trans haq, hc, ?_⟩
  have hm : τ s ∈ r ⁻¹'
      {y : P | y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y))} := by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hτpoint, s, haq] using hq
  rw [← hc] at hm
  simpa only [Set.mem_ofPred_eq, hτbase] using hm

end AlgebraicGeometry
