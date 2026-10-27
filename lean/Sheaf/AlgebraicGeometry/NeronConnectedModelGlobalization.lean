/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.NeronLftModel
public import Sheaf.AlgebraicGeometry.RelativeIdentityComponent
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.ClosedPointFPPatching
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.AlgebraicGeometry.Morphisms.PointedSectionStageDescent
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods

/-! # Globalization of local Néron models with a common connected model

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §10.1, Proposition 9 (b) ⇒ (a),
pp.294–295, with the gluing of Proposition 7, p.293
(blueprint: lem-sfb-neron-connected-model-globalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The generic-point map of the affine domain.
Source: BLR §10.1, Proposition 9 (blueprint: lem-sfb-neron-connected-model-globalization). -/
noncomputable def neronGenericPoint (D : Type u) [CommRing D] [IsDomain D] :
    Spec (.of (FractionRing D)) ⟶ Spec (.of D) :=
  Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))

/-- The canonical localization map at a maximal ideal.
Source: BLR §10.1, Proposition 9 (blueprint: lem-sfb-neron-connected-model-globalization). -/
noncomputable def neronLocalization (D : Type u) [CommRing D] (m : MaximalSpectrum D) :
    Spec (.of (Localization.AtPrime m.asIdeal)) ⟶ Spec (.of D) :=
  Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime m.asIdeal)))

/-- The canonical generic-point map into the localized base, induced by the localization
map into the fraction field; it is not an arbitrary choice of a base morphism.
Source: BLR §10.1, Proposition 9 (blueprint: lem-sfb-neron-connected-model-globalization). -/
noncomputable def neronLocalizedGenericPoint (D : Type u) [CommRing D] [IsDomain D]
    (m : MaximalSpectrum D) :
    Spec (.of (FractionRing D)) ⟶ Spec (.of (Localization.AtPrime m.asIdeal)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.AtPrime m.asIdeal) (FractionRing D)))

/-- Local Néron lft-models with a common finite-type connected model globalize, with their
specified generic identifications and identity component. The equations through the first
pullback projections express compatibility without choosing an iterated-pullback isomorphism.
Source: BLR §10.1, Proposition 9 (b) ⇒ (a), pp.294–295, and Proposition 7, p.293
(blueprint: lem-sfb-neron-connected-model-globalization).

Proof plan:
1. At a closed point s, the punctured local spectrum is Spec K by dimension one.
   Quasi-compact opens W of N_s containing B_s cover N_s. Separatedness makes their
   intersections quasi-compact; smoothness then makes W and B finitely presented.
   Use lem-weil-pbc-qcqs-over-affine, separated-affine-open-intersection,
   smooth-restrict-open-subschemes, qcqs-morphism-permanence and closed-immersion-base-change.
2. Apply lem-sfb-closed-point-fp-patching to B outside s and W at s to obtain smooth
   separated charts P_(s,W). Full faithfulness gives all inclusions, their compatibility
   and their intersections. Use finite-presentation-base-change-composition for products.
3. Glue B and all these charts, with same-point overlaps P_(s,W∩W') and different-point
   overlaps B. The cocycle holds on common larger charts and is the identity on mixed
   overlaps. Use lem-weil-pbc-glue-schemes and scheme-morphism-gluing. Smoothness is
   local on the source (lem-weil-pbc-smooth-local-on-source); the generic fibre is G.
4. At s, the s-charts recover N_s and every other chart restricts to B_s. Gluing their
   inclusions and inverses gives the required localization isomorphism.
5. Check the diagonal on products of charts. Same-point overlaps give restricted local
   diagonals, and mixed overlaps give graphs into separated charts. Closed-point patching
   detects closed immersions. Target locality then gives separatedness; use
   lem-weil-pbc-section-separated-closed-immersion and separated-base-change.
6. For affine smooth X, the local Néron property extends a generic map at each s.
   Express Spec D_s as the affine-neighbourhood limit by
   lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods. Use limit-fibre-products and
   lem-sbc-pointed-section-stage-descent to spread each extension to a neighbourhood.
7. On overlaps local Néron uniqueness and
   lem-weil-pbc-locally-finite-type-limit-map-equality give equality after shrinking at
   every closed point; at a generic-only open equality is already given. Glue uniquely.
   An affine open cover gives the mapping property for every smooth X, without a
   quasi-compactness assumption on X or N.
8. Products of smooth schemes are smooth by lem-pc-proper-base-change (smooth clause)
   and lem-trf-smooth-composition. Extend the generic group operations by the mapping
   property. Uniqueness gives all group identities, commutativity, and compatibility
   with the local operations. B is an open subgroup; its geometric fibres are exactly
   the identity components, at the generic point and at every closed point. No finite
   set of maximal ideals or finite component group was used. -/
theorem neron_connected_model_globalization
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (hdim : ringKrullDim D = 1)
    (G : Grp (Over (Spec (.of (FractionRing D))))) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom] [GeometricallyConnected G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (B : Grp (Over (Spec (.of D)))) [IsCommMonObj B.X]
    [Smooth B.X.hom] [IsSeparated B.X.hom] [GeometricallyConnected B.X.hom]
    [LocallyOfFiniteType B.X.hom] [QuasiCompact B.X.hom]
    (eB : (Over.pullback (neronGenericPoint D)).mapGrp.obj B ≅ G)
    (L : ∀ m : MaximalSpectrum D, Grp (Over (Spec (.of (Localization.AtPrime m.asIdeal)))))
    (eL : ∀ m : MaximalSpectrum D,
      (Over.pullback (neronLocalizedGenericPoint D m)).mapGrp.obj (L m) ≅ G)
    (hL : ∀ m : MaximalSpectrum D,
      IsNeronLftModel (L m) G (eL m))
    (jL : ∀ m : MaximalSpectrum D,
      (Over.pullback (neronLocalization D m)).obj B.X ⟶ (L m).X)
    (hjL : ∀ m : MaximalSpectrum D, IsRelativeIdentityComponent (jL m))
    (hcompat : ∀ m : MaximalSpectrum D,
      (((Over.pullback (neronLocalizedGenericPoint D m)).map (jL m) ≫ (eL m).hom.hom.hom).left ≫
          eB.inv.hom.hom.left ≫ pullback.fst B.X.hom (neronGenericPoint D)) =
        pullback.fst ((Over.pullback (neronLocalization D m)).obj B.X).hom
            (neronLocalizedGenericPoint D m) ≫
          pullback.fst B.X.hom (neronLocalization D m)) :
    ∃ (N : Grp (Over (Spec (.of D))))
      (eN : (Over.pullback (neronGenericPoint D)).mapGrp.obj N ≅ G),
      IsCommMonObj N.X ∧ IsNeronLftModel N G eN ∧
      (∃ j : B.X ⟶ N.X, IsRelativeIdentityComponent j ∧
        (Over.pullback (neronGenericPoint D)).map j ≫ eN.hom.hom.hom = eB.hom.hom.hom) ∧
      ∀ m : MaximalSpectrum D,
        ∃ q : (Over.pullback (neronLocalization D m)).obj N.X ≅ (L m).X,
          IsMonHom q.hom ∧
          (((Over.pullback (neronLocalizedGenericPoint D m)).map q.hom ≫ (eL m).hom.hom.hom).left ≫
              eN.inv.hom.hom.left ≫ pullback.fst N.X.hom (neronGenericPoint D)) =
            pullback.fst ((Over.pullback (neronLocalization D m)).obj N.X).hom
                (neronLocalizedGenericPoint D m) ≫
              pullback.fst N.X.hom (neronLocalization D m) := by
  sorry

end AlgebraicGeometry
