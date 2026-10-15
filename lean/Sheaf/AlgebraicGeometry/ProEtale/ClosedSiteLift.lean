/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.RingTheory.ProEtale.ClosedLiftMap
import Sheaf.RingTheory.IndEtaleStability

/-! # Lifting the affine closed site

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`, definition
`def-exc-closed-site-lift`, order 1843 (blueprint: def-exc-closed-site-lift).
The base-change functor is `closedSiteBaseChange`; `closedSiteLift` sends an affine
object with coordinate algebra C to Spec H_A(C), with the opposite induced maps.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Base change to the closed subscheme Spec(A/I).
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteBaseChange :
    (Spec (.of A)).AffineProEt ⥤ (Spec (.of (A ⧸ I))).AffineProEt :=
  CategoryTheory.MorphismProperty.Over.pullback
    (P := proAffineEtale) (Q := ⊤) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The coordinates of an affine object over Spec(A/I), as an A-algebra via A → A/I.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteCoordinates (V : (Spec (.of (A ⧸ I))).AffineProEt) : CommAlgCat.{u} A :=
  @CommAlgCat.of A _ Γ(V.left, ⊤) _
    (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop).hom.toAlgebra)

/-- Pullback of functions commutes with the structural A-algebra maps.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift).
Proof: apply global sections to the commuting triangle defining f, and compose with
Γ(Spec A) ≅ A; functoriality of global sections gives the required equality. -/
theorem closedSiteCoordinates_commutes
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) (a : A) :
    f.left.appTop.hom (algebraMap A (closedSiteCoordinates A I W) a) =
      algebraMap A (closedSiteCoordinates A I V) a := sorry

/-- The coordinate map reverses a morphism in the affine basis.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteCoordinatesMap {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    closedSiteCoordinates A I W →ₐ[A] closedSiteCoordinates A I V :=
  { f.left.appTop.hom with commutes' := closedSiteCoordinates_commutes A I f }

/-- The spectrum of the closed lift belongs to the affine ind-etale basis over A.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift).
Proof: the indexing category is filtered by lem-exc-closed-lift-filtered; its diagram
consists of etale A-algebras. Thus its colimit is ind-etale, by the filtered-colimit
clause of lem-weil-pbc-ind-etale-stability. Apply proAffineEtale_Spec_iff. -/
theorem closedSiteLift_mem (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    proAffineEtale (Spec.map (CommRingCat.ofHom
      (algebraMap A (Algebra.ClosedLift A (closedSiteCoordinates A I V))))) := sorry

/-- Lift an affine closed-site object by taking Spec of its closed-lift algebra.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteLiftObj (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (Spec (.of A)).AffineProEt :=
  AffineProEt.mk _ (closedSiteLift_mem A I V)

/-- Opposite closed-lift algebra maps commute with the maps to Spec A.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift).
Proof: the induced closed-lift map is an A-algebra map, so its composite with the
structural map from A is the structural map. Apply the contravariant Spec functor. -/
theorem closedSiteLiftMap_over
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    Spec.map (CommRingCat.ofHom
      (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f)).toRingHom) ≫
      (closedSiteLiftObj A I W).hom = (closedSiteLiftObj A I V).hom := sorry

/-- Lift a map by the opposite of the induced closed-lift algebra map.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteLiftMap {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    closedSiteLiftObj A I V ⟶ closedSiteLiftObj A I W :=
  CategoryTheory.MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f)).toRingHom))
    (closedSiteLiftMap_over A I f)

/-- The lift preserves identities.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift).
Proof: the coordinate identity is the identity algebra map. The colimit-induced
closed-lift map is the identity by its values on every colimit structure map;
contravariant Spec preserves identities. -/
theorem closedSiteLiftMap_id (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    closedSiteLiftMap A I (𝟙 V) = 𝟙 (closedSiteLiftObj A I V) := sorry

/-- The lift preserves composition.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift).
Proof: global sections reverses composition. On each colimit structure map,
postcomposition twice agrees with postcomposition by the composite, so the induced
closed-lift algebra maps compose accordingly. Spec reverses composition again. -/
theorem closedSiteLiftMap_comp
    {V W T : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) (g : W ⟶ T) :
    closedSiteLiftMap A I (f ≫ g) = closedSiteLiftMap A I f ≫ closedSiteLiftMap A I g :=
  sorry

/-- The functor v from the affine closed-site basis to the affine basis over A:
V = Spec C is sent to Spec H_A(C), and maps are the opposite induced algebra maps.
Source: blueprint order 1843 (blueprint: def-exc-closed-site-lift). -/
def closedSiteLift :
    (Spec (.of (A ⧸ I))).AffineProEt ⥤ (Spec (.of A)).AffineProEt where
  obj := closedSiteLiftObj A I
  map := closedSiteLiftMap A I
  map_id := closedSiteLiftMap_id A I
  map_comp := closedSiteLiftMap_comp A I

end AlgebraicGeometry.Scheme.AffineProEt
