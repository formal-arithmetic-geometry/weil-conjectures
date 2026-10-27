module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.TangentBundle
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-! # Finite presentation of relative differentials of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tags 04CT, 04CU, 04CV and 05ZF
(blueprint: lem-sfb-space-relative-differentials-finite-presentation).

The differential module is the sheafification of sectionwise differentials of the
canonical structural ring map, transported from the existing small affine model.
The chart comparison is an isomorphism of additive presheaves on the whole scheme
étale site, with an explicit scalar-linearity condition. Thus it compares module
sheaves, including their restriction maps, rather than only their section groups.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The relative differential module on the original small étale ringed site.
Source: Stacks 04CT, 08TP and 039Z
(blueprint: lem-sfb-space-relative-differentials-finite-presentation).
This uses the actual sheafified differential construction and the inverse of the
recorded affine-basis restriction equivalence; neither module nor ring map is arbitrary. -/
def spaceRelativeDifferentials (f : X ⟶ Y) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj (SheafDifferentials.omega (cotangentRingMap f))

/-- Étale schemes over a chart, regarded as schemes over the original base.
Source: Stacks 04CU (blueprint: lem-sfb-space-relative-differentials-finite-presentation). -/
def differentialChartOver (U : X.EtaleSite) :
    (X.etaleForget.obj U).Etale ⥤ Over S :=
  Scheme.Etale.forget _ ⋙ Over.map U.obj.left.hom

/-- The canonical composite map of each étale chart to the algebraic space.
Source: Stacks 04CU (blueprint: lem-sfb-space-relative-differentials-finite-presentation). -/
def differentialChartArrow (U : X.EtaleSite) :
    (X.etaleForget.obj U).Etale ⥤ CostructuredArrow yoneda X.obj.obj :=
  (differentialChartOver U).toCostructuredArrow yoneda X.obj.obj
    (fun W ↦ yoneda.map (Over.homMk W.hom) ≫ U.obj.hom)
    (by
      intro W Z a
      simp only [← Category.assoc, ← Functor.map_comp]
      congr 2
      ext1
      exact MorphismProperty.Over.w a)

/-- The representable étale chart inclusion, with its proof inherited from the
recorded scheme-test criterion and composition of representable étale maps.
Source: Stacks 04CU (blueprint: lem-sfb-space-relative-differentials-finite-presentation). -/
def differentialChartInclusion (U : X.EtaleSite) :
    (X.etaleForget.obj U).Etale ⥤ X.EtaleSite :=
  ObjectProperty.lift _ (differentialChartArrow U) (fun W ↦
    isEtale_comp _ _
      (((representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1
        ((differentialChartOver U).obj W) U.obj.left (Over.homMk W.hom rfl)).2 W.prop) U.property)

/-- Relative differentials have the usual description on compatible étale scheme
charts, and are quasi-coherent and locally finitely presented for a locally finitely
presented morphism. The chart square is only required to commute, not to be cartesian.
Source: Stacks 04CT, 04CU, 04CV and 05ZF
(blueprint: lem-sfb-space-relative-differentials-finite-presentation).

Proof:
1. Use lem-trf-space-chartwise-etale-permanence and
   lem-trf-space-enlarged-etale-ringed-site-model to compute restriction as ringed
   localization. The structural rings restrict to the usual regular functions.
   The sheafified-module-differentials-cokernel construction and
   lem-trf-topos-inverse-image-differentials identify restricted differentials with
   differentials relative to a^{-1}f^{-1}O_Y. The commuting square and étaleness of
   the target chart identify this ring with g^{-1}O_V; no cartesian square is needed.
2. Apply lem-sfb-scheme-etale-relative-differentials-comparison to identify these
   differentials with the associated étale sheaf of the usual scheme differentials.
   Its isomorphism is linear and natural on the entire scheme étale site.
3. Choose compatible locally finitely presented scheme charts. Around each source
   point choose affine W = Spec A mapping to affine T = Spec R with A finitely
   presented over R. The affine differential description gives quasi-coherence.
   By lem-sfb-ring-finite-presentation-differentials, Omega_{A/R} is finitely
   presented over A. Use lem-sc-relative-differentials-affine-sections and clause
   (b) of lem-weil-pbc-quasi-coherent-finite-type-affine to obtain finite
   presentation of the scheme differential module on W, hence locally on U.
4. Apply lem-sfb-scheme-etale-module-exact-finiteness-comparison. Its local finite
   free presentations transport through the chart comparison. Compose coverings
   using chartwise-etale-permanence. This gives local finite free presentations
   on X_et, and these also give quasi-coherence. No finite atlas, uniform rank,
   Noetherian, separation or quasi-compactness condition is required. -/
theorem spaceRelativeDifferentials_finitePresentation (f : X ⟶ Y)
    (hfp : MapIsLocallyOfFinitePresentation f) :
    (∀ (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left),
      U.obj.hom ≫ f.hom.hom = yoneda.map g ≫ V.obj.hom →
      ∃ e : (differentialChartInclusion U).op ⋙ (spaceRelativeDifferentials f).val.presheaf ≅
          (Scheme.Modules.etaleTensorSectionsSheaf g.left.relativeDifferentials).obj,
        ∀ (W : (X.etaleForget.obj U).Etale) (r : Γ(W.left, ⊤))
          (m : (spaceRelativeDifferentials f).val.obj
            (op ((differentialChartInclusion U).obj W))),
          e.hom.app (op W) (r • m) =
            (((Scheme.Modules.tensorPullback W.hom).obj g.left.relativeDifferentials).smul r).hom
              (e.hom.app (op W) m)) ∧
    (spaceRelativeDifferentials f).IsQuasicoherent ∧
    (spaceRelativeDifferentials f).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
