module

public import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Points and local rings under local-spectrum base change

Source: Stacks Project, Schemes, Tags 01J6, 02NA, 01JR, 01I4, 01HV;
Algebra, Tags 00DK, 00E3, 00CP
(blueprint: lem-sfb-local-spectrum-base-change-stalks).

The square is any realization of the specified fibre product. On an affine chart,
its section ring, with the algebra structure given by the projection, is the
localization at the image of the base denominators. This characterizes the canonical
identification with the spectrum of that localization, including the projection.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The image in the chart ring of the complement of the prime of the base point.
Source: Stacks, Algebra, Tags 00DK and 00E3, applied to the chart of Schemes, 02NA
(blueprint: lem-sfb-local-spectrum-base-change-stalks). This uses the actual section
map; it does not assume that this map is injective. -/
noncomputable def localSpectrumBaseChangeDenominators {X T : Scheme.{u}} (f : T ⟶ X) (p : X)
    (U : X.Opens) (hU : IsAffineOpen U) (hp : p ∈ U)
    (W : T.Opens) (hWU : W ≤ f ⁻¹ᵁ U) : Submonoid Γ(T, W) :=
  (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl.map (f.appLE U W hWU).hom

/-- Every point above the base point lifts uniquely; its base projection is the
closed point, its actual projection stalk map is invertible, and a closed point
has a closed lift. Source: Stacks, Schemes, Tags 01J6, 02NA, 01JR, 01HV;
Algebra, Tags 00DK, 00E3, 00CP
(blueprint: lem-sfb-local-spectrum-base-change-stalks).

Proof: (1) Choose affine neighborhoods U of p and W of q inside f⁻¹(U).
The canonical-morphism node identifies the base ring with R localized at p;
open-fibre-product, affine-spectra and localization-base-change identify the
inverse image of W with Spec of D localized at the image of R minus p.
(2) The prime Q of q contracts to p. Localization-spectrum-embedding therefore
gives its unique extended prime, and that prime contracts to the maximal ideal
in the localized base. Every point over q lies in this same open chart, so the
uniqueness is global. (3) Localization-universal-property constructs inverse maps
D_Q to B_P and B_P to D_Q: each map extends the same map on D, and uniqueness
shows the two composites are identities. (4) Affine-open-stalk-localization and
compatibility of germs with the morphism identify this map with h.stalkMap, so
that actual map is an isomorphism. (5) If q is closed, the inverse image of its
singleton under continuous h is closed; uniqueness says it is the lift singleton.
No Noetherian, finite-type, separatedness or closedness hypothesis on p is used. -/
theorem localSpectrumBaseChange_points_stalks {X T Y : Scheme.{u}}
    (f : T ⟶ X) (p : X) (π : Y ⟶ Spec (X.presheaf.stalk p)) (h : Y ⟶ T)
    (hpb : IsPullback π h (X.fromSpecStalk p) f) (q : T) (hq : f q = p) :
    (∃! z : Y, h z = q) ∧
    ∀ (z : Y), h z = q →
      π z = closedPoint (X.presheaf.stalk p) ∧ IsIso (h.stalkMap z) ∧
        (IsClosed ({q} : Set T) → IsClosed ({z} : Set Y)) := by
  sorry

/-- The affine chart is the canonical localization, its lifted prime is the
extended prime, and the actual stalk map has the stated forward and inverse
fraction formulas. Source: Stacks, Schemes, Tags 01J6, 02NA, 01JR, 01I4, 01HV;
Algebra, Tags 00DK, 00E3, 00CP
(blueprint: lem-sfb-local-spectrum-base-change-stalks).

Proof: (1) Factor the canonical local-spectrum map through U using
spec-local-ring-canonical-morphism. Open-fibre-product and affine-spectra identify
h⁻¹(W) with the spectrum of the base-change tensor ring. Localization-base-change
identifies its section map with localization at the image of R minus p. Thus
h⁻¹(W) is affine and its actual section ring B has this localization structure.
(2) For q = h(z) over p, Q contracts to p; localization-spectrum-embedding says
that the prime P of z is the extension of Q. (3) Every image denominator is a
unit in D_Q. Extend D to B then B_P by localization-universal-property; conversely
extend D to B_P through D_Q. Uniqueness gives inverse ring maps, the forward map
sends d/e to (d/1)/(e/1), and the inverse sends (d/s)/(e/t) to dt/(se).
(4) Affine-open-stalk-localization identifies D_Q and B_P with the actual stalks
via their germ maps. Germ-stalkMap compatibility identifies the comparison with
h.stalkMap, giving the displayed commutative square. Ring.inverse denotes the
inverse of a unit, so the formulas below are precisely these fraction formulas. -/
theorem localSpectrumBaseChange_affine_fractions {X T Y : Scheme.{u}}
    (f : T ⟶ X) (p : X) (π : Y ⟶ Spec (X.presheaf.stalk p)) (h : Y ⟶ T)
    (hpb : IsPullback π h (X.fromSpecStalk p) f)
    (U : X.Opens) (hU : IsAffineOpen U) (hp : p ∈ U)
    (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ f ⁻¹ᵁ U) :
    ∃ (hV : IsAffineOpen (h ⁻¹ᵁ W))
      (a : Algebra Γ(T, W) Γ(Y, h ⁻¹ᵁ W))
      (_hL : IsLocalization (localSpectrumBaseChangeDenominators f p U hU hp W hWU)
        Γ(Y, h ⁻¹ᵁ W)),
      algebraMap Γ(T, W) Γ(Y, h ⁻¹ᵁ W) = (h.app W).hom ∧
      (∃ e : (h ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of
          (Localization (localSpectrumBaseChangeDenominators f p U hU hp W hWU))),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W)
          (Localization (localSpectrumBaseChangeDenominators f p U hU hp W hWU)))) ≫
            hW.fromSpec = (h ⁻¹ᵁ W).ι ≫ h) ∧
      ∀ (z : Y) (hz : h z ∈ W), f (h z) = p →
        (hV.primeIdealOf ⟨z, hz⟩).asIdeal =
          Ideal.map (algebraMap Γ(T, W) Γ(Y, h ⁻¹ᵁ W))
            (hW.primeIdealOf ⟨h z, hz⟩).asIdeal ∧
        ∃ (eD : Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal ≃+*
              T.presheaf.stalk (h z))
          (eB : Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≃+*
              Y.presheaf.stalk z)
          (φ : Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal ≃+*
              Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal),
          eD.toRingHom.comp (algebraMap Γ(T, W)
            (Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal)) =
              (T.presheaf.germ W (h z) hz).hom ∧
          eB.toRingHom.comp (algebraMap Γ(Y, h ⁻¹ᵁ W)
            (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)) =
              (Y.presheaf.germ (h ⁻¹ᵁ W) z hz).hom ∧
          eB.toRingHom.comp φ.toRingHom = (h.stalkMap z).hom.comp eD.toRingHom ∧
          (∀ (d : Γ(T, W)) (e : (hW.primeIdealOf ⟨h z, hz⟩).asIdeal.primeCompl),
            φ (IsLocalization.mk'
              (Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal) d e) =
              algebraMap Γ(Y, h ⁻¹ᵁ W)
                (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
                (algebraMap Γ(T, W) Γ(Y, h ⁻¹ᵁ W) d) *
              Ring.inverse (algebraMap Γ(Y, h ⁻¹ᵁ W)
                (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
                (algebraMap Γ(T, W) Γ(Y, h ⁻¹ᵁ W) e))) ∧
          ∀ (d e : Γ(T, W))
            (s t : localSpectrumBaseChangeDenominators f p U hU hp W hWU)
            (_he : e ∉ (hW.primeIdealOf ⟨h z, hz⟩).asIdeal),
            φ.symm (algebraMap Γ(Y, h ⁻¹ᵁ W)
              (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
              (IsLocalization.mk' Γ(Y, h ⁻¹ᵁ W) d s) *
              Ring.inverse (algebraMap Γ(Y, h ⁻¹ᵁ W)
                (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
                (IsLocalization.mk' Γ(Y, h ⁻¹ᵁ W) e t))) =
              algebraMap Γ(T, W)
                (Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal)
                (d * (t : Γ(T, W))) *
              Ring.inverse (algebraMap Γ(T, W)
                (Localization.AtPrime (hW.primeIdealOf ⟨h z, hz⟩).asIdeal)
                ((s : Γ(T, W)) * e)) := by
  sorry

end AlgebraicGeometry.Scheme
