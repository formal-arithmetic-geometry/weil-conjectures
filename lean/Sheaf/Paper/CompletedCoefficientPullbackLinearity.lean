/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Mathlib.CategoryTheory.Linear.Basic
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.AutomorphismCompletionUnitComparison
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Scalar compatibility and linearity of completed coefficient pullback

Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
def-wf-tensor-product, second sentence; Stacks Tags 09A5, 0H7J, 03D7 and 03CR.
(blueprint: lem-sf-completed-coefficient-pullback-linearity).

The coefficient maps are the actual constant-section and inverse-limit maps.
Ordinary K-flat derived pullback is distinguished from exact termwise descent.
The complete subcategory uses the published intrinsic Koszul unit for each tuple.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Both scalar squares, including the equation on scalar sections.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 09A5 and 0H7J
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: for P_n=A/I^(n+1), the projection of pbcCompletedScalar is the constant
quotient map followed by the fixed constant-to-function comparison. The profinite
coefficient inverse-image theorem identifies the projection of completedCoefficientMap
with inverse image of the projection followed by the finite constant comparison.
Naturality of constant inverse image gives equality after each projection. Joint
monicity proves the first square. Adjunction-unit naturality gives the second square.
Evaluate it on the constant section b; the constant direct-image map fixes b, giving
the last equation. These are steps 1 and 2 of the node's proof. -/
theorem sfCompletedCoefficientScalarSquares
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    (proEtaleConstantInverseImageMap e.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        pbcCompletedScalar X d =
      (proEtaleSheafInverseImage e.hom CommRingCat.{u + 1}).map
        (pbcCompletedScalar X d) ≫ completedCoefficientMap e.hom d) ∧
    (pbcCompletedScalar X d ≫ completedCoefficientDirectImageMap e.hom d =
      proEtaleConstantDirectImageMap e.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d)) ∧
    (∀ (U : X.ProEtᵒᵖ) (b : A),
      (completedCoefficientDirectImageMap e.hom d).hom.app U (pbcCompletedSection X d U b) =
        pbcCompletedSection X d ((proEtaleBaseChange e.hom).op.obj U) b) := by
  have hp (n : ℕ) :
      pbcCompletedScalar X d ≫ pbcAdicProjection X d n =
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison X d n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists X
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n]
    rfl
  have hp' := hp
  simp only [pbcAdicProjection] at hp'
  have hs : proEtaleConstantInverseImageMap e.hom CommRingCat.{u + 1}
      (CommRingCat.of A) ≫ pbcCompletedScalar X d =
      (proEtaleSheafInverseImage e.hom CommRingCat.{u + 1}).map
        (pbcCompletedScalar X d) ≫ completedCoefficientMap e.hom d := by
    apply limit.hom_ext
    rintro ⟨n⟩
    change _ ≫ pbcAdicProjection X d n = _ ≫ pbcAdicProjection X d n
    rw [Category.assoc, hp]
    simp only [pbcAdicProjection, completedCoefficientMap, limit.lift_π,
      completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc]
    rw [← Functor.map_comp_assoc, hp']
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc _ (pbcLevelConstantComparison X d n).hom
      (pbcLevelConstantComparison X d n).inv, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (proEtaleConstantInverseImageMap_naturality e.hom
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).symm =≫ _
  have hd : pbcCompletedScalar X d ≫ completedCoefficientDirectImageMap e.hom d =
      proEtaleConstantDirectImageMap e.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d) := by
    let adj := proEtaleSheafAdjunction e.hom CommRingCat.{u + 1}
    have h := congrArg (adj.homEquiv _ _) hs
    dsimp only [adj] at h
    simpa only [Adjunction.homEquiv_unit, proEtaleConstantInverseImageMap,
      completedCoefficientDirectImageMap,
      Functor.map_comp, Category.assoc, Adjunction.unit_naturality_assoc,
      Adjunction.right_triangle_components_assoc] using h.symm
  refine ⟨hs, hd, ?_⟩
  intro U b
  have h := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b)) hd
  have hc := ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of A)))).apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange e.hom).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hcU := congrArg (fun f ↦ f.app U b) hc
  change (proEtaleConstantDirectImageMap e.hom CommRingCat.{u + 1}
    (CommRingCat.of A)).hom.app U _ = _ at hcU
  change _ = (pbcCompletedScalar X d).hom.app
    ((proEtaleBaseChange e.hom).op.obj U) _ at h
  exact h.trans (congrArg
    ((pbcCompletedScalar X d).hom.app ((proEtaleBaseChange e.hom).op.obj U)) hcU)

/-- Finite-limit exactness of the specified module left adjoint.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 03CR and 03D7
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: the inverse image of the automorphism is a site equivalence. The finite
coefficient comparisons and their inverse-limit comparison are isomorphisms by the
profinite-coefficient inverse-image theorem. Ringed-presentation transport therefore
identifies the specified module adjunction with an equivalence; its left functor
preserves finite limits. This is step 5 of the node's proof. -/
@[instance] theorem sfCompletedModulePullback_preservesFiniteLimits
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    PreservesFiniteLimits (completedModulePullback e.hom d) := by
  rw [← pbcIsoModulePullback_eq_completed e.hom d]
  infer_instance

/-- Finite-colimit exactness of the specified module left adjoint.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 03CR and 03D7
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: as in step 5, inverse image and its fixed completed coefficient isomorphism
give a ringed-topos equivalence. Ringed-presentation transport makes the specified
module left adjoint an equivalence, which preserves finite colimits. -/
@[instance] theorem sfCompletedModulePullback_preservesFiniteColimits
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    PreservesFiniteColimits (completedModulePullback e.hom d) := by
  rw [← pbcIsoModulePullback_eq_completed e.hom d]
  infer_instance

/-- Finite-limit exactness of module direct image with the adjunct ring action.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 03CR and 03D7
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: step 5 identifies the specified module adjunction with the equivalence
induced by the site equivalence and completed coefficient isomorphism. Its right
adjoint is exactly completedModuleDirectImage, so it preserves finite limits. -/
@[instance] theorem sfCompletedModuleDirectImage_preservesFiniteLimits
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    PreservesFiniteLimits (completedModuleDirectImage e.hom d) := by
  infer_instance

/-- Finite-colimit exactness of module direct image with the adjunct ring action.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 03CR and 03D7
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: step 5 identifies the specified module adjunction with the equivalence
induced by the site equivalence and completed coefficient isomorphism. Its right
functor is exactly completedModuleDirectImage, so it preserves finite colimits. -/
@[instance] theorem sfCompletedModuleDirectImage_preservesFiniteColimits
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    PreservesFiniteColimits (completedModuleDirectImage e.hom d) := by
  have hF : (completedModulePullback e.hom d).IsEquivalence := by
    rw [← pbcIsoModulePullback_eq_completed e.hom d]
    infer_instance
  have := (pbcActualModuleAdjunction e.hom d).isEquivalence_right_of_isEquivalence_left
  infer_instance

/-- Additivity and constant A-linearity on modules, exact derived descent, and ordinary
K-flat derived pullback, always for the published constant-section Hom actions.
Source: blueprint def-wf-tensor-product, second sentence; Stacks 03D7
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: step 3 evaluates module direct image on U as evaluation on u_e(U). The scalar
section equation identifies its action, so it preserves addition and b times each
map. For step 4 use the specified adjunction: its Hom bijection is the unit followed
by direct image. It is additive and A-linear by step 3 and bilinearity of composition.
Naturality of the unit and injectivity of the Hom bijection prove these properties
for the specified left adjoint. Step 5 supplies exactness. Step 6 applies the linear
abelian-derived-category and exact-linear-derived-functor theorems to both functors.
For ordinary K-flat pullback use ringedDerivedPullback_linear: the scalar hypothesis
is the adjunct scalar square on the final object. Its comparison on flat-term K-flat
resolutions extends scalar preservation to all derived morphisms, as in step 7. -/
theorem sfCompletedCoefficientPullbackLinearity
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X) :
    (completedModuleDirectImage e.hom d).Additive ∧
    (completedModuleDirectImage e.hom d).Linear A ∧
    (completedModulePullback e.hom d).Additive ∧
    (completedModulePullback e.hom d).Linear A ∧
    (completedModuleDirectImage e.hom d).mapDerivedCategory.Additive ∧
    (completedModuleDirectImage e.hom d).mapDerivedCategory.Linear A ∧
    (completedModulePullback e.hom d).mapDerivedCategory.Additive ∧
    (completedModulePullback e.hom d).mapDerivedCategory.Linear A ∧
    (completedOrdinaryPullback e.hom d).Additive ∧
    (completedOrdinaryPullback e.hom d).Linear A := by
  have hG : (completedModuleDirectImage e.hom d).Linear A := by
    constructor
    intro M N f b
    ext U x
    change (pbcCompletedSection X d ((proEtaleBaseChange e.hom).op.obj U) b) •
        f.val.app ((proEtaleBaseChange e.hom).op.obj U) x =
      ((completedCoefficientDirectImageMap e.hom d).hom.app U
        (pbcCompletedSection X d U b)) •
        f.val.app ((proEtaleBaseChange e.hom).op.obj U) x
    rw [(sfCompletedCoefficientScalarSquares X d e).2.2]
  have hF : (completedModulePullback e.hom d).Linear A := by
    let adj := pbcActualModuleAdjunction e.hom d
    constructor
    intro M N f b
    apply (adj.homEquiv M _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul,
      adj.unit_naturality, Linear.smul_comp]
  have hI : (pbcIsoModulePullback e.hom d).Linear A := by
    rw [pbcIsoModulePullback_eq_completed e.hom d]
    exact hF
  have hOrd : (completedOrdinaryPullback e.hom d).Linear A :=
    Functor.linear_of_iso A (pbcIsoOrdinaryDerivedComparison e.hom d).symm
  have hOrdAdd : (completedOrdinaryPullback e.hom d).Additive :=
    Functor.additive_of_iso (pbcIsoOrdinaryDerivedComparison e.hom d).symm
  exact ⟨inferInstance, hG, inferInstance, hF, inferInstance, inferInstance,
    inferInstance, inferInstance, hOrdAdd, hOrd⟩

/-- Ordinary K-flat pullback preserves the complete full subcategory for every finite
list generating I, using the actual intrinsic completion unit.
Source: blueprint def-wf-tensor-product, second sentence
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: step 7 applies the automorphism-completion-unit comparison with the same
datum, coefficient map and generating list. It compares the explicit intrinsic
completion units under ordinary derived pullback, so invertibility of the source
unit implies invertibility of the target unit. Independence of representatives
allows the representative used by WfIsComplete. No boundedness or constructibility
restriction enters this argument. -/
theorem sfCompletedCoefficientPullback_preservesComplete
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha K →
      WfIsComplete X d r a ha ((completedOrdinaryPullback e.hom d).obj K) := by
  intro hK
  let H := pbcIsoAmbientPullback e.hom d
  let alpha := (pbcIsoOrdinaryDerivedComparison e.hom d).app K
  let D := wfCompletionRepresentative X d ((completedOrdinaryPullback e.hom d).obj K)
  let realD := DerivedCategory.Q.objObjPreimageIso
    ((completedOrdinaryPullback e.hom d).obj K)
  obtain ⟨c, hc, _⟩ := (automorphism_completion_unit_comparison X d r a ha e).2.2.2
    K (wfCompletionRepresentative X d K) (DerivedCategory.Q.objObjPreimageIso K)
    D (realD ≪≫ alpha)
  let : IsIso (intrinsicCompletionUnit X d r a ha K
    (wfCompletionRepresentative X d K) (DerivedCategory.Q.objObjPreimageIso K)) := hK
  have hu : IsIso (intrinsicCompletionUnit X d r a ha (H.obj K) D
      (realD ≪≫ alpha)) := by
    rw [← hc]
    infer_instance
  change IsIso (intrinsicCompletionUnit X d r a ha
    ((completedOrdinaryPullback e.hom d).obj K) D realD)
  have heq : intrinsicCompletionUnit X d r a ha
      ((completedOrdinaryPullback e.hom d).obj K) D realD =
      alpha.hom ≫ intrinsicCompletionUnit X d r a ha (H.obj K) D
        (realD ≪≫ alpha) := by
    simp [intrinsicCompletionUnit]
  rw [heq]
  infer_instance

/-- The restriction to all intrinsically complete objects is additive and A-linear,
with its underlying ambient functor fixed by the inclusion square.
Source: blueprint def-wf-tensor-product, second sentence
(blueprint: lem-sf-completed-coefficient-pullback-linearity).
Proof: lift the ordinary derived pullback through the full-subcategory inclusion,
using preservation of completeness from step 7. Objects are its actual images and
maps are its actual derived maps. Full-subcategory Hom groups inherit addition and
the constant A-action unchanged. Apply the ordinary pullback's additivity and
linearity to these inherited Hom groups. This gives both displayed map equations,
which are precisely the final assertion of step 7. -/
theorem sfCompletedCoefficientCompletePullback_linearity
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (e : Aut X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ H : WfCompleteCategory X d r a ha ⥤ WfCompleteCategory X d r a ha,
      H ⋙ ObjectProperty.ι (WfIsComplete X d r a ha) =
        ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ completedOrdinaryPullback e.hom d ∧
      H.Additive ∧ H.Linear A ∧
      ∀ (M N : WfCompleteCategory X d r a ha) (f g : M ⟶ N) (b : A),
        H.map (b • f) = b • H.map f ∧ H.map (f + g) = H.map f + H.map g := by
  let H := ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ completedOrdinaryPullback e.hom d)
    (fun M ↦ sfCompletedCoefficientPullback_preservesComplete X d e r a ha M.obj M.property)
  have := (sfCompletedCoefficientPullbackLinearity X d e).2.2.2.2.2.2.2.2.1
  have := (sfCompletedCoefficientPullbackLinearity X d e).2.2.2.2.2.2.2.2.2
  have hAdd : H.Additive := by
    constructor
    intro M N f g
    ext
    exact (completedOrdinaryPullback e.hom d).map_add
  have hLin : H.Linear A := by
    constructor
    intro M N f b
    ext
    exact Functor.map_smul _ b f.hom
  exact ⟨H, rfl, hAdd, hLin, fun M N f g b ↦
    ⟨Functor.map_smul H b f, H.map_add⟩⟩

end AlgebraicGeometry.Scheme
