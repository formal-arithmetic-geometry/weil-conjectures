module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Sheaf.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normal_stalks_of_smooth_integral_base {X Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : X ⟶ Y) [Smooth g] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, hVU, hg⟩ := Smooth.exists_isStandardSmooth g x
  let : Nonempty U := ⟨⟨g x, hVU hx⟩⟩
  let : IsIntegrallyClosed Γ(Y, U) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hY U
  have hnormal := (g.smooth_appLE hU hV hVU).isNormalRing (fun p hp ↦ by
    let : IsIntegrallyClosed (Localization.AtPrime p) :=
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
    exact ⟨inferInstance, inferInstance⟩)
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨hd, hi⟩ := hnormal p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (X.presheaf.stalk x)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_stalks_of_flat_preimmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Flat g] [IsPreimmersion g]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨hd, hi⟩ := hY (g x)
  let : IsDomain (Y.presheaf.stalk (g x)) := hd
  let : IsIntegrallyClosed (Y.presheaf.stalk (g x)) := hi
  algebraize [(g.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g x) (g.toLRSHom.prop x)
  have hf : RingHom.FaithfullyFlat (g.stalkMap x).hom :=
    ‹Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)›
  let e := RingEquiv.ofBijective (g.stalkMap x).hom
    ⟨hf.injective,
      g.stalkMap_surjective x⟩
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e⟩

-- The existing statement binds an unused projection `n`; retain its signature verbatim.
set_option linter.unusedVariables false in
/-- Normality of the localized relative normalization.

Source: Stacks Project, Tags 033C (smooth ascent of normality), 035L
(relative normalization in a normal source), and 0307 (localization of integral closure).
(blueprint: lem-sbc-stalk-normalization-normal-part)

Proof: Apply smooth ascent directly to the smooth composite P -> C_U -> C -> S.
On affine charts, the base section ring is an integrally closed domain, by the
normality of the stalks of the integral S. `RingHom.Smooth.isNormalRing` makes
all prime localizations of each smooth source section ring normal domains.
The affine stalk-localization equivalence transports this to the stalks of P.
Finite type over the locally Noetherian S also makes P locally Noetherian.
Apply `relativeNormalization_normal_stalks` to f: its relative normalization
has normal domain stalks, by the finite-component argument of Stacks 035L.
The map Spec O(S,s) -> S is a flat preimmersion. Both pullback projections
l: L -> C and N -> f.normalization inherit flatness and the preimmersion
property. On stalks a preimmersion is surjective, while a flat local ring map
is faithfully flat and therefore injective. Thus N -> f.normalization induces
ring isomorphisms on every stalk. Transport domainhood and integral closedness
across these isomorphisms. This uses no assertion about arbitrary flat base
change preserving normality. Empty source schemes have no stalks to check. -/
theorem stalk_normalization_normal_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro f l n z
  let : IsLocallyNoetherian ((𝟭 Scheme).obj PA.obj.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  have hP := normal_stalks_of_smooth_integral_base hS (f ≫ c)
  have hN := relativeNormalization_normal_stalks f hP
  exact normal_stalks_of_flat_preimmersion (pullback.fst f.fromNormalization l) hN z

end AlgebraicGeometry.Scheme
