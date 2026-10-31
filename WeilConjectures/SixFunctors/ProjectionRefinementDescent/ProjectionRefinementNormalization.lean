/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRefinementAmbientNormalization

/-! # The inverse witnessed comparison is the canonical refinement map

Source: lem-sf-projection-refinement-descent, steps 4 and 7; Stacks 0F7B, 0F7G
and 0D6E (blueprint: lem-sf-projection-refinement-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.ProjectionRefinementDescent

attribute [local irreducible] properOpenMate leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction Functor.mapDerivedCategory Functor.rightDerivedFunctor

private def comparisonNat
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d) :
    coefficientImage A d ⟶ coefficientImage A c := by
  letI := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  letI := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let γ := RefinementProjection.identityNormalize
    (ProperOpenShriek A c.i) (ProperOpenShriek A d.i)
    (ProperOpenPush A (𝟙 X.obj.left)) (ProperOpenPush A r.hom)
    ((ordinary D A).sId X).inv
    (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
      (r.i_hom.trans (Category.id_comp _).symm))
  exact Functor.whiskerRight γ (ProperOpenPush A d.g) ≫
    Functor.whiskerLeft (ProperOpenShriek A c.i)
      (conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) d.g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r.hom ≫ d.g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom d.g)).hom ≫
    Functor.whiskerLeft (ProperOpenShriek A c.i)
      (RefinementProjection.indexIso (ProperOpenPush A) r.hom_g).hom

private theorem comparisonNat_app
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    (K : ProperOpenDerived A X.obj.left) :
    (comparisonNat D A r).app K = RefinementProjection.finiteComparison D A r K := rfl

private theorem inverseIsoTransport
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (γ : F ⟶ G) {M K : C} (e : M ≅ K) (b : G.obj M ≅ F.obj M)
    (hb : b.inv = γ.app M) :
    (G.mapIso e.symm ≪≫ b ≪≫ F.mapIso e).inv = γ.app K := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, hb, Category.assoc]
  rw [← γ.naturality e.hom, ← Category.assoc, ← F.map_comp,
    e.inv_hom_id, F.map_id, Category.id_comp]

attribute [local irreducible] refinementComparisonAtWitness refinementFixedObject

private theorem comparison_transport
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    (O : EtaleOriginDerivedCategory X.obj.left A) (K : ProperOpenDerived A X.obj.left)
    (e : refinementFixedObject X.obj.left A O ≅ K) :
    ((coefficientImage A c).mapIso e.symm ≪≫
      refinementComparisonAtWitness A r O ≪≫ (coefficientImage A d).mapIso e).inv =
        RefinementProjection.finiteComparison D A r K := by
  have hO := CompactSupportFiniteProjection.refinementComparisonAtWitness_inv_eq D A r O
  have hb : (refinementComparisonAtWitness A r O).inv =
      (comparisonNat D A r).app (refinementFixedObject X.obj.left A O) :=
    hO.trans (comparisonNat_app D A r _).symm
  exact (inverseIsoTransport (comparisonNat D A r) e
    (refinementComparisonAtWitness A r O) hb).trans (comparisonNat_app D A r K)

/-- The inverse of theta is the un-inverted proper/open mate followed by the
conjugate proper direct-image compositor. This assertion involves no tensor,
projection map, Tor bound or constructibility predicate.

Source: lem-sf-projection-refinement-descent, step 4 and the compositor in step 7;
Stacks 0F7B (lemma-shriek-proper-and-open), 0F7G (lemma-shriek-lqf-and-proper),
0D6E; the specified comparison in def-sf-refinement-comparison-isomorphism.
(blueprint: lem-sf-projection-refinement-normalization).

Proof: first take K to be the comparison inverse image of the bounded-below
etale object retained in O. The finite clopen-mate site-transport formula writes
the mate as inverse open-extension comparison, the etale clopen mate, canonical
comparison/direct-image mate, and the proper image of the first open-extension
comparison. In the square (j1,j2,id,r), the etale refinement clause identifies
the etale clopen mate with the resolution-normalized proper/open comparison.
The comparison/direct-image unit normalization on the identity edge cancels
the left identity direct image. The resulting four-factor word is precisely
properOpenProEtaleIso, including the two bounded-below inclusion comparisons.
Naturality transports this identity along refinementFixedWitnessIso and then e,
so it is independent of the retained presentation. Invert the definition of theta:
its proper/open inverse becomes the proper/open mate just identified. The inverse
of finiteDirectImageComposition is the conjugate of leftDerivedUpperStarComp,
because both right comparisons have the same adjunction counit (the universal
right-derived normalization of lowerStarComp); uniqueness of conjugate adjunction
comparisons identifies them. The remaining equality-of-index comparison is the
one for r.hom_g; its inverse is indexIso in finiteComparison. Functoriality and
naturality of the compositor cancel the two transported presentation maps. These
are exactly the three factors defining finiteComparison. No projection morphism
is inverted. Quasi-compactness of the opens follows from that of f; the schemes
are finite type over D.k, without absolute separatedness. Identity refinements,
zero objects and empty opens use the same unit and inverse-pair cancellations.

Existing proof templates: the generic site-word calculations in
Sheaf.Paper.PurityWitnessedMateNormalization (their finite-setting parameter is
used only for its coefficient ring), and the private
finiteDirectImageComposition_conjugate in WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage.
The former calculations must be used without that public theorem's unnecessary
absolute separatedness and coefficient-embedding restrictions. -/
theorem normalized_refinement_inverse
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ) {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    (K : ProperOpenDerived (Coefficient C.l E n) X.obj.left)
    (O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X.obj.left)
    (e : refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X.obj.left O ≅ K) :
    (theta C.l E n r K O e).inv =
      RefinementProjection.finiteComparison D (Coefficient C.l E n) r K := by
  let : TopologicalSpace (Coefficient C.l E n) := ⊥
  let : DiscreteTopology (Coefficient C.l E n) := discreteTopology_bot _
  exact comparison_transport D (Coefficient C.l E n) r O K e

end WeilConjectures.ProjectionRefinementDescent
