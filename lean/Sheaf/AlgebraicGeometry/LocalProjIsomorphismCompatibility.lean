module

public import Sheaf.AlgebraicGeometry.LocalGradedAlgebraIso
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Mathlib.AlgebraicGeometry.Gluing

/-! # Local Proj comparisons, restrictions and degreewise units

Source: Stacks Project, Constructions, Tags 01MY, 01N2 and 02NC
(blueprint: lem-trf-local-proj-isomorphism-compatibility).
The relative Proj is the canonical affine-data construction. Its specified affine
identifications transport the ordinary Proj chart formulas to the relative restrictions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RelativeProjAlgebra

variable {S : Scheme.{u}} {A B : RelativeProjAlgebra S} {U : S.affineOpens}

/-- The local comparison in the specified section-ring Proj coordinates.
Source: Stacks, Tags 01MY and 01N2
(blueprint: lem-trf-local-proj-isomorphism-compatibility). -/
def localProjChartMap
    (r : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅ (A.realization.π ⁻¹ᵁ U.1).toScheme) :
    B.localProj U ⟶ A.localProj U :=
  (B.realization.restrictionIso U).inv ≫ r.hom ≫ (A.realization.restrictionIso U).hom

/-- The required U-map with its inverse-image charts, spectrum maps and covering.
`Away.map` is the actual degree-zero homogeneous localization map, not arbitrary chart data.
Source: Stacks, Constructions, Tag 01MY
(blueprint: lem-trf-local-proj-isomorphism-compatibility). -/
def IsLocalProjComparison (β : LocalGradedIso A B U)
    (r : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅ (A.realization.π ⁻¹ᵁ U.1).toScheme) :
    Prop :=
  localProjChartMap r ≫ A.localBase U = B.localBase U ∧
  (∀ (d : ℕ) (f : A.sections U), f ∈ A.sectionGrade U d → 0 < d →
    localProjChartMap r ⁻¹ᵁ Proj.basicOpen (A.sectionGrade U) f =
      Proj.basicOpen (B.sectionGrade U) (β.hom U le_rfl f)) ∧
  (∀ (d : ℕ) (f : A.sections U) (hf : f ∈ A.sectionGrade U d) (hd : 0 < d),
    Proj.awayι (B.sectionGrade U) (β.hom U le_rfl f) ((β.hom U le_rfl).map_mem hf) hd ≫
        localProjChartMap r =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (β.hom U le_rfl) f)) ≫
        Proj.awayι (A.sectionGrade U) f hf hd) ∧
  (⨆ (p : {p : ℕ × A.sections U // p.2 ∈ A.sectionGrade U p.1 ∧ 0 < p.1}),
    Proj.basicOpen (B.sectionGrade U) (β.hom U le_rfl p.1.2)) = ⊤

/-- A fraction b/(u^d g)^m in the ordinary localization at g, using the unit inverse
u^(-d) times g^(-1). This is the canonical identification of the two common charts;
when b has degree m*d it represents a degree-zero fraction. No cancellation of g occurs.
Source: Stacks, Constructions, Tag 02NC, change of local frame
(blueprint: lem-trf-local-proj-isomorphism-compatibility). -/
def unitAdjustedChartFraction (B : RelativeProjAlgebra S) (U : S.affineOpens)
    (v : Γ(S, U.1)ˣ) (d m : ℕ) (b g : B.sections U) : Localization.Away g :=
  algebraMap (B.sections U) (Localization.Away g) b *
    (algebraMap (B.sections U) (Localization.Away g)
        (algebraMap Γ(S, U.1) (B.sections U) ((↑(v⁻¹) : Γ(S, U.1)) ^ d)) *
      IsLocalization.Away.invSelf g) ^ m

/-- Existence and uniqueness of the local U-isomorphism with its complete chart formula.
The last clause writes the induced map on every homogeneous fraction explicitly.
Source: Stacks, Constructions, Tags 01MY and 01N2
(blueprint: lem-trf-local-proj-isomorphism-compatibility).

Proof: specialize lem-nagata-affine-proj-scalar-extension to the identity base-ring map.
The graded tensor isomorphism sends t tensor a to t*beta(a); its inverse sends b to
1 tensor beta-inverse(b). The balanced relation verifies both identities. The theorem
supplies the inverse-image charts, their covering and the spectrum maps. Conjugate by
the specified affine identifications of def-nagata-relative-proj. Applying the same
construction to beta-inverse gives two identity composites on all fractions in the chart
rings (def-nagata-homogeneous-localization-degree-zero). Spectrum functoriality and
lem-weil-pbc-scheme-morphism-gluing give inverse scheme maps and uniqueness globally.
Away.map_mk gives the displayed fraction formula. No equality A_0 = O_U is used. -/
theorem exists_unique_localProjComparison (β : LocalGradedIso A B U) :
    (∃! r : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅
        (A.realization.π ⁻¹ᵁ U.1).toScheme, IsLocalProjComparison β r) ∧
    (∀ (d : ℕ) (f : A.sections U) (hf : f ∈ A.sectionGrade U d)
      (_hd : 0 < d) (m : ℕ) (a : A.sections U) (ha : a ∈ A.sectionGrade U (m • d)),
      HomogeneousLocalization.Away.map (β.hom U le_rfl) f
          (HomogeneousLocalization.Away.mk (A.sectionGrade U) hf m a ha) =
        HomogeneousLocalization.Away.mk (B.sectionGrade U)
          ((β.hom U le_rfl).map_mem hf) m (β.hom U le_rfl a)
          ((β.hom U le_rfl).map_mem ha)) := by
  sorry

/-- The comparison for the inverse algebra isomorphism is the inverse comparison.
Source: Stacks, Constructions, Tag 01MY
(blueprint: lem-trf-local-proj-isomorphism-compatibility).

Proof: apply the chart construction of lem-nagata-affine-proj-scalar-extension to
beta-inverse. Both composite ring maps fix a/f^m. These fractions exhaust the chart rings
by def-nagata-homogeneous-localization-degree-zero. Spectrum functoriality makes the
scheme composites identities on every chart. The charts cover, so
lem-weil-pbc-scheme-morphism-gluing proves they are globally identities. Uniqueness of
the chart-defined comparison identifies this map with the inverse of the comparison. -/
theorem localProjComparison_inverse (β : LocalGradedIso A B U)
    (r : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅ (A.realization.π ⁻¹ᵁ U.1).toScheme)
    (hr : IsLocalProjComparison β r) : IsLocalProjComparison β.symm r.symm := by
  sorry

/-- Both comparisons commute with affine restriction, and restriction on each chart
sends beta(a)/beta(f)^m to rho(beta(a))/rho(beta(f))^m.
Source: Stacks, Constructions, Tags 01MY and 01N2
(blueprint: lem-trf-local-proj-isomorphism-compatibility).

Proof: the specified identifications in def-nagata-relative-proj turn the inclusions
of relative restrictions into the Proj maps of coefficient restriction. Sheaf naturality
says rho_B*beta = beta_V*rho_A. Thus the two composites have the same inverse-image opens
and send a/f^m to the same restricted fraction. The chart cover stays a cover after
restriction. Spectrum functoriality and lem-weil-pbc-scheme-morphism-gluing identify the
two composites. Repeat with beta-inverse for the inverse maps. Away.map_mk gives the
coefficient-restriction formula, including m=0, zero divisors and nilpotent denominators. -/
theorem localProjComparison_restrict (β : LocalGradedIso A B U)
    (V : S.affineOpens) (h : V ≤ U)
    (r : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅ (A.realization.π ⁻¹ᵁ U.1).toScheme)
    (rV : (B.realization.π ⁻¹ᵁ V.1).toScheme ≅ (A.realization.π ⁻¹ᵁ V.1).toScheme)
    (hr : IsLocalProjComparison β r) (hrV : IsLocalProjComparison (β.restrict V h) rV) :
    B.realization.proj.homOfLE (B.realization.π.preimage_mono h) ≫ r.hom =
        rV.hom ≫ A.realization.proj.homOfLE (A.realization.π.preimage_mono h) ∧
    A.realization.proj.homOfLE (A.realization.π.preimage_mono h) ≫ r.inv =
        rV.inv ≫ B.realization.proj.homOfLE (B.realization.π.preimage_mono h) ∧
    (∀ (d : ℕ) (f : A.sections U) (hf : f ∈ A.sectionGrade U d)
      (_hd : 0 < d) (m : ℕ) (a : A.sections U) (ha : a ∈ A.sectionGrade U (m • d)),
      HomogeneousLocalization.Away.map (B.restriction h) (β.hom U le_rfl f)
          (HomogeneousLocalization.Away.map (β.hom U le_rfl) f
            (HomogeneousLocalization.Away.mk (A.sectionGrade U) hf m a ha)) =
        HomogeneousLocalization.Away.mk (B.sectionGrade V)
          ((B.restriction h).map_mem ((β.hom U le_rfl).map_mem hf)) m
          (B.restriction h (β.hom U le_rfl a))
          ((B.restriction h).map_mem ((β.hom U le_rfl).map_mem ha))) := by
  sorry

/-- Degreewise multiplication by a base unit leaves the comparison, its inverse and
its chart maps unchanged. The last two equalities take place in the ordinary localization
at beta(f), in which unitAdjustedChartFraction is beta'(a)/beta'(f)^m on the common chart.
Source: Stacks, Constructions, Tag 02NC (local frame changes), and Tag 01MY
(blueprint: lem-trf-local-proj-isomorphism-compatibility).

Proof: the image v of the base unit in degree zero is a unit. The elements v^d*beta(f)
and beta(f) therefore define the same standard open. The canonical identification of
chart rings sends b/(v^d*beta(f))^m to v^(-d*m)*b/beta(f)^m. Its inverse multiplies the
numerator by v^(d*m); both respect ordinary localization and preserve degree zero.
For a of degree m*d, substitute beta'(a)=v^(m*d)*beta(a). The unit factors cancel,
leaving beta(a)/beta(f)^m. Equality in ordinary localization is equality of homogeneous
fractions by def-nagata-homogeneous-localization-degree-zero. Thus the spectrum maps
agree on the covering charts. Lem-weil-pbc-scheme-morphism-gluing gives equality of the
scheme maps, hence of the isomorphisms and their inverses. Only units are cancelled;
there is no regularity or non-zero-divisor condition on f. -/
theorem localProjComparison_degreewise_unit (β β' : LocalGradedIso A B U)
    (v : Γ(S, U.1)ˣ)
    (hscale : ∀ (k : ℕ) (a : A.sections U), a ∈ A.sectionGrade U k →
      β'.hom U le_rfl a =
        algebraMap Γ(S, U.1) (B.sections U) ((↑v : Γ(S, U.1)) ^ k) * β.hom U le_rfl a)
    (r r' : (B.realization.π ⁻¹ᵁ U.1).toScheme ≅ (A.realization.π ⁻¹ᵁ U.1).toScheme)
    (hr : IsLocalProjComparison β r) (hr' : IsLocalProjComparison β' r') :
    r' = r ∧ r'.inv = r.inv ∧
    (∀ (d : ℕ) (f : A.sections U), f ∈ A.sectionGrade U d → 0 < d →
      Proj.basicOpen (B.sectionGrade U) (β'.hom U le_rfl f) =
        Proj.basicOpen (B.sectionGrade U) (β.hom U le_rfl f)) ∧
    (∀ (d : ℕ) (f : A.sections U) (hf : f ∈ A.sectionGrade U d) (_hd : 0 < d),
      ∃ e : HomogeneousLocalization.Away (B.sectionGrade U) (β'.hom U le_rfl f) ≃+*
          HomogeneousLocalization.Away (B.sectionGrade U) (β.hom U le_rfl f),
        (∀ (m : ℕ) (b : B.sections U) (hb : b ∈ B.sectionGrade U (m • d)),
          (e (HomogeneousLocalization.Away.mk (B.sectionGrade U)
            ((β'.hom U le_rfl).map_mem hf) m b hb)).val =
              unitAdjustedChartFraction B U v d m b (β.hom U le_rfl f)) ∧
        e.toRingHom.comp (HomogeneousLocalization.Away.map (β'.hom U le_rfl) f) =
          HomogeneousLocalization.Away.map (β.hom U le_rfl) f) ∧
    (∀ (d : ℕ) (f : A.sections U) (hf : f ∈ A.sectionGrade U d)
      (_hd : 0 < d) (m : ℕ) (a : A.sections U) (ha : a ∈ A.sectionGrade U (m • d)),
      unitAdjustedChartFraction B U v d m (β'.hom U le_rfl a) (β.hom U le_rfl f) =
          unitAdjustedChartFraction B U v d m
            (algebraMap Γ(S, U.1) (B.sections U) ((↑v : Γ(S, U.1)) ^ (m * d)) *
              β.hom U le_rfl a) (β.hom U le_rfl f) ∧
      unitAdjustedChartFraction B U v d m
          (algebraMap Γ(S, U.1) (B.sections U) ((↑v : Γ(S, U.1)) ^ (m * d)) *
            β.hom U le_rfl a) (β.hom U le_rfl f) =
        (HomogeneousLocalization.Away.map (β.hom U le_rfl) f
          (HomogeneousLocalization.Away.mk (A.sectionGrade U) hf m a ha)).val) := by
  sorry

end AlgebraicGeometry.RelativeProjAlgebra
