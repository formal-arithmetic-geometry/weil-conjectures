/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.ReesBaseChange
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.ReesConeNormalization
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleReesChart
import Sheaf.RingTheory.ReesAssociatedGradedChart
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.OrzechProperty
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Functoriality of the extended-Rees deformation of a smooth section

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction, explicit base-change maps and etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).

The deformation, augmentation, punctured chart and two fibres are the existing
extended-Rees constructions. All maps below are fixed coefficientwise on every affine
restriction, including the quotient by t. Pushout assertions encode the displayed
canonical tensor-product isomorphisms, without a flatness hypothesis on the base map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace AlgebraicGeometry.SectionReesBaseChange

/-- The canonical conormal comparison already characterized by its adjunction and
representative formulas. Source: sk-thm-dnc, Local construction; Stacks 01R4
(blueprint: lem-trf-section-rees-base-change-etale). -/
def conormalMap {V V' S S' : Scheme.{u}} (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) :
    (Scheme.Modules.tensorPullback b).obj
        ((Scheme.Modules.tensorPullback s).obj s.ker.toModules) ⟶
      (Scheme.Modules.tensorPullback s').obj s'.ker.toModules :=
  Classical.choose ((Classical.choose_spec
    (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).2).2)

/-- The coefficientwise canonical map of Rees spaces for a commuting square of centres.
Source: sk-thm-dnc, Local construction, t and b/t
(blueprint: lem-trf-section-rees-base-change-etale). -/
def pairMap {V V' S S' : Scheme.{u}} (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) : s'.ker.deformationSpace ⟶ s.ker.deformationSpace :=
  Scheme.IdealSheafData.deformationSpaceMap h s.ker s'.ker fun {U' U} hU ↦
    (s.ker.ideal_map_appLE_le_ideal_comap h ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).1 ⟨U'.1, U'.2⟩)

/-- The affine coefficientwise comparison on the zero fibre, obtained by quotienting
the existing extended-Rees map by t. Source: sk-thm-dnc, Local construction; Stacks 0632
(blueprint: lem-trf-section-rees-base-change-etale). -/
def zeroAlgebraMap {R R' : Type u} [CommRing R] [CommRing R']
    (I : Ideal R) (J : Ideal R') (a : R →+* R') (ha : I.map a ≤ J) :
    I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT} →+*
      J.extendedReesAlgebra ⧸ Ideal.span {J.extendedReesAlgebraT} :=
  Ideal.quotientMap _ (I.extendedReesAlgebraMap a J ha)
    (Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.extendedReesAlgebraMap_T]))

/-- Compatibility with the augmented pair and both fibre identifications. The zero
and punctured maps are specified on EVERY affine restriction by their coefficient maps.
In particular the zero map is the associated-graded map, hence its degree-one map is
the canonical conormal comparison, rather than an arbitrary normal-bundle isomorphism.
Source: sk-thm-dnc, Local construction, restriction and homogeneous-class formulas
(blueprint: lem-trf-section-rees-base-change-etale). -/
def Compatible {V V' S S' : Scheme.{u}} (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (h : V' ⟶ V) (b : S' ⟶ S)
    (φ : s'.ker.deformationSpace ⟶ s.ker.deformationSpace) : Prop :=
  φ ≫ Scheme.Hom.deformationSpaceProj g s =
      Scheme.Hom.deformationSpaceProj g' s' ≫ AffineSpace.map (ULift.{u} (Fin 1)) b ∧
  s'.deformationSpaceSection ≫ φ =
      AffineSpace.map (ULift.{u} (Fin 1)) b ≫ s.deformationSpaceSection ∧
  Scheme.Hom.deformationSpaceOneFibre g' s' ≫ φ =
      h ≫ Scheme.Hom.deformationSpaceOneFibre g s ∧
  ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone) (l : V'.laurentSpec ⟶ V.laurentSpec),
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ∃ ha : (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U',
        colimit.ι (relativeGluingData s'.ker.coequifibered_toReesPresheaf).functor U' ≫ φ =
          Spec.map (CommRingCat.ofHom ((s.ker.siteIdeal U).extendedReesAlgebraMap
            (h.appLE U.1 U'.1 hU).hom (s'.ker.siteIdeal U') ha)) ≫
              colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U) ∧
    ν ≫ s.ker.normalConeToDeformationSpace = s'.ker.normalConeToDeformationSpace ≫ φ ∧
    ν ≫ Scheme.Hom.normalConeProj g s = Scheme.Hom.normalConeProj g' s' ≫ b ∧
    s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection ∧
    l ≫ s.ker.laurentSpecToDeformationSpace = s'.ker.laurentSpecToDeformationSpace ≫ φ ∧
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ∃ ha : (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U',
        colimit.ι (relativeGluingData s'.ker.coequifibered_toNormalConePresheaf).functor U' ≫ ν =
          Spec.map (CommRingCat.ofHom (zeroAlgebraMap (s.ker.siteIdeal U)
            (s'.ker.siteIdeal U') (h.appLE U.1 U'.1 hU).hom ha)) ≫
              colimit.ι (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).functor U) ∧
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      colimit.ι (relativeGluingData V'.coequifibered_toLaurentPresheaf).functor U' ≫ l =
        Spec.map (CommRingCat.ofHom
          (LaurentPolynomial.mapRingHom (h.appLE U.1 U'.1 hU).hom)) ≫
            colimit.ι (relativeGluingData V.coequifibered_toLaurentPresheaf).functor U)

/-- Arbitrary base change of a section Rees family, with the augmented pair at zero
and one and the punctured trivialization. Source: sk-thm-dnc, Local construction
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: (1) Smooth dimension, separated finite type and closed-section permanence give
the same setting over S'. (2) Choose centred etale affine coordinates, so I=(x)B.
(3) Use etale_rees_chart to present the Rees algebra as B tensor_P R[t,u]; tensor
reassociation gives the base-changed presentation, with no tensoring of an injection.
(4) The comparison is the existing coefficientwise map, t maps to t and b/t to b'/t.
Glue the affine comparisons and their inverses, using also the punctured charts.
(5) The augmentation kills u, and setting t=1 gives the original coefficient map.
(6) On conormals [x_j] maps to [x'_j]; generation and equal finite rank show it is
an isomorphism. Symmetric algebras give the normal-bundle comparison. The class
[b]_m corresponds to [b t^(-m)], proving zero-fibre compatibility. (7) Apply the
Noetherian Rees geometry to the new section. (10) All formulas commute with further
restriction since they are coefficientwise, including d=0 and the empty base. -/
theorem base_change {V S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    ∃ (s' : S' ⟶ pullback g b) (_ : IsClosedImmersion s')
      (w : s' ≫ pullback.fst g b = b ≫ s),
      s' = Scheme.Hom.baseChangeSection g s hs b ∧
      IsPullback (pairMap s s' (pullback.fst g b) b w)
        (s'.ker.deformationSpaceProj ≫ pullback.snd g b)
        (s.ker.deformationSpaceProj ≫ g) b ∧
      Compatible g (pullback.snd g b) s s' (pullback.fst g b) b
        (pairMap s s' (pullback.fst g b) b w) ∧
      IsIso (conormalMap s s' (pullback.fst g b) b w) ∧
      ∃ ν : s'.ker.normalCone ⟶ s.ker.normalCone,
        ν ≫ s.ker.normalConeToDeformationSpace =
          s'.ker.normalConeToDeformationSpace ≫ pairMap s s' (pullback.fst g b) b w ∧
        IsPullback ν (Scheme.Hom.normalConeProj (pullback.snd g b) s')
          (Scheme.Hom.normalConeProj g s) b := by
  sorry

/-- Smooth separated dimension-d geometry and compactifiability of the new structural
maps; these are conclusions, not additional base-change assumptions.
Source: sk-thm-dnc, Local construction
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Steps 1 and 7 reapply Noetherian section-Rees geometry after arbitrary base
change. The zero-fibre pullback gives the same smooth dimension and separated finite
type for the normal bundle. Finite-type Noetherian permanence and Nagata give the
Noetherian sources and compactifications. No flatness or finite type of b is used. -/
theorem base_change_geometry {V S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    ∃ (s' : S' ⟶ pullback g b) (_ : IsClosedImmersion s'),
      s' = Scheme.Hom.baseChangeSection g s hs b ∧
      SmoothOfRelativeDimension d (pullback.snd g b) ∧
      IsSeparated (pullback.snd g b) ∧ LocallyOfFiniteType (pullback.snd g b) ∧
      QuasiCompact (pullback.snd g b) ∧ s' ≫ pullback.snd g b = 𝟙 S' ∧
      SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      IsSeparated (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj (pullback.snd g b) s') ∧
      IsSeparated (Scheme.Hom.normalConeProj (pullback.snd g b) s') ∧
      HasCompactification (Scheme.Hom.normalConeProj (pullback.snd g b) s') := by
  sorry

/-- Etale maps of pairs with Cartesian centres give the canonical pullback of the Rees
space, preserve augmentation and both fibres, and induce the linear normal-bundle
isomorphism. Source: sk-thm-dnc, Local construction, etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: (8) On an affine restriction B to B1, etaleness implies flatness and the
Cartesian centres give I1=I B1. Tensor the Rees inclusion in the Laurent ring with
flat B1. Its image is generated by t and b/t, hence is exactly B1[t,I1/t].
(9) Relative Spec and gluing give the asserted pullback and etaleness. Augmentations
kill b/t and at one the map is h. Flat tensor exactness identifies every graded
piece by [b] maps to [h-sharp(b)]; multiplication is preserved on representatives.
Thus degree one is precisely conormalMap and relative Spec Sym gives the linear
normal isomorphism, including its zero section. The Rees associated-graded formula
[b]_m maps to [b t^(-m)] gives the displayed zero map. (10) All identifications
commute with restrictions and compositions by the same coefficientwise formulas. -/
theorem etale {V V₁ S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (h : V₁ ⟶ V) [Etale h] [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h] (s₁ : S ⟶ V₁) [IsClosedImmersion s₁]
    (hs₁ : s₁ ≫ (h ≫ g) = 𝟙 S) (w : s₁ ≫ h = (𝟙 S) ≫ s)
    (centres : IsPullback s₁ (𝟙 S) h s) :
    IsPullback (pairMap s s₁ h (𝟙 S) w) s₁.ker.deformationSpaceProj
      s.ker.deformationSpaceProj h ∧
    Etale (pairMap s s₁ h (𝟙 S) w) ∧
    Compatible g (h ≫ g) s s₁ h (𝟙 S) (pairMap s s₁ h (𝟙 S) w) ∧
    IsIso (conormalMap s s₁ h (𝟙 S) w) ∧
    ∃ ν : s₁.ker.normalCone ⟶ s.ker.normalCone,
      ν ≫ s.ker.normalConeToDeformationSpace =
        s₁.ker.normalConeToDeformationSpace ≫ pairMap s s₁ h (𝟙 S) w ∧ IsIso ν := by
  sorry

/-- The affine algebra identification, encoded by pushout squares of the specified
coefficient maps. The last two pushouts are the presentations B tensor_P R[t,u]
and B' tensor_P' R'[t,u], using mvPolynomialExtendedReesAlgebraEquiv. The first
pushout is B[t,I/t] tensor_R R' = B'[t,I'/t].
Source: sk-thm-dnc, Local construction, x_j=t*u_j
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Steps 2--3 identify P'=P tensor_R R', B'=B tensor_R R', and C'=C tensor_R R'.
Etale ring base change makes P' to B' etale. Apply the existing etale Rees chart
on both sides and reassociate the three tensor factors by the tensor universal
property. Step 4 identifies this map with the coefficientwise Laurent map. It
fixes t, sends b to a(b), and sends x_j/t to x'_j/t. Step 6 sends the degree-one
conormal class [x_j] to [x'_j] by the same quotient formula. No injection is
tensored along R to R'. The empty coordinate family gives the polynomial algebra. -/
theorem affine_base_change (R R' B B' : Type u)
    [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [IsNoetherianRing R] [IsNoetherianRing R'] (d : ℕ)
    (κ : R →+* R') (ψ : MvPolynomial (Fin d) R →+* B)
    (ψ' : MvPolynomial (Fin d) R' →+* B') (a : B →+* B')
    (σ : B →+* R) (hσ : σ.comp (ψ.comp MvPolynomial.C) = RingHom.id R)
    (hI : (Ideal.mvPolynomialOrigin R (Fin d)).map ψ = RingHom.ker σ)
    (he : ψ.Etale) (w : a.comp ψ = ψ'.comp (MvPolynomial.map κ))
    (hB : IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (ψ.comp MvPolynomial.C))
      (CommRingCat.ofHom (ψ'.comp MvPolynomial.C)) (CommRingCat.ofHom a)) :
    IsPushout (CommRingCat.ofHom κ)
      (CommRingCat.ofHom ((algebraMap B
        ((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebra).comp
          (ψ.comp MvPolynomial.C)))
      (CommRingCat.ofHom ((algebraMap B'
        ((Ideal.mvPolynomialOrigin R' (Fin d)).map ψ').extendedReesAlgebra).comp
          (ψ'.comp MvPolynomial.C)))
      (CommRingCat.ofHom (((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebraMap
        a _ (Ideal.map_map_mvPolynomialOrigin κ ψ ψ' a w).le)) ∧
    IsPushout (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) R)
        (Ideal.mvPolynomialOrigin R (Fin d)).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B
        ((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebra))
      (CommRingCat.ofHom ((Ideal.mvPolynomialOrigin R (Fin d)).extendedReesAlgebraMap
        ψ _ le_rfl)) ∧
    IsPushout (CommRingCat.ofHom ψ')
      (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) R')
        (Ideal.mvPolynomialOrigin R' (Fin d)).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B'
        ((Ideal.mvPolynomialOrigin R' (Fin d)).map ψ').extendedReesAlgebra))
      (CommRingCat.ofHom ((Ideal.mvPolynomialOrigin R' (Fin d)).extendedReesAlgebraMap
        ψ' _ le_rfl)) := by
  sorry

/-- On an affine etale restriction the tensor-product algebra map is the specified
coefficientwise extended-Rees map. Source: sk-thm-dnc, etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Step 8 uses flatness of the etale coefficient map to preserve the inclusion
of the Rees algebra in Laurent polynomials. The image is generated by t and the
images of b/t; since I1=IB1 these generate the entire new Rees algebra. This proves
the pushout, hence the canonical B1 tensor_B B[t,I/t] isomorphism. -/
theorem affine_etale (B B₁ : Type u) [CommRing B] [CommRing B₁]
    (I : Ideal B) (a : B →+* B₁) (ha : a.Etale) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom (algebraMap B I.extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B₁ (I.map a).extendedReesAlgebra))
      (CommRingCat.ofHom (I.extendedReesAlgebraMap a (I.map a) le_rfl)) := by
  sorry

/-- Identification of the same normal cone with the symmetric-algebra bundle, including
its normalized representative map and its zero section. This makes explicit the bundle
used in both functoriality assertions: their zero-fibre comparison on every chart sends
[a/t] to [h-sharp(a)/t], hence is the linear map of these bundles induced by conormalMap.
Source: sk-thm-dnc, Local construction; Stacks 0632--0633
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Step 6 uses the centred-coordinate conormal basis. Products of its degree-one
classes identify Sym(I/I^2) with the associated graded. Relative Spec gives the stated
bundle identification, with the displayed canonical symmetricComparison map. The Rees
associated-graded chart gives q with the specified homogeneous representative formula.
Both augmentations kill degree one, giving the zero-section identity. The argument
applies to the base-changed section and the etale pair as well, by Steps 1, 7 and 9. -/
theorem normal_bundle {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    ∃ (_ : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d)
      (_ : IsIso (ConormalGradedAlgebra.symmetricComparison s))
      (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (e : PurityNormalBundle.normalCone s ≅
        VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1)),
      Etale.FiniteSmoothPurity.ReesConeNormalized s q ∧
      e = (Over.forget S).mapIso
        ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
          (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
            (ObjectProperty.isoMk _
              (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop)) ∧
      (q ≪≫ e).hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
        Scheme.Hom.normalConeProj g s ∧
      s.normalConeZeroSection ≫ (q ≪≫ e).hom =
        VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
  sorry

end AlgebraicGeometry.SectionReesBaseChange
