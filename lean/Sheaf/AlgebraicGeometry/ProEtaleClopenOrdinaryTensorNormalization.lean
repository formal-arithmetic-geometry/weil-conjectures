/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetectionData

/-! Ordinary normalized braided tensor restriction along a clopen immersion.
Source: Stacks Project, sites-modules.tex, Tag 0GMW; sites-cohomology.tex, Tag 0FPQ.
(blueprint: lem-pur-clopen-ordinary-tensor-normalization). -/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

/-- Ordinary restriction admits its canonical normalized braided structure.
Source: Stacks Project, Modules on Sites, Tags 03EL and 0GMW.
(blueprint: lem-pur-clopen-ordinary-tensor-normalization).

Proof: Precomposition along the clopen inclusion identifies the presheaf tensors
sectionwise: both evaluate at U to F(jU) tensor H(jU). The topology on the component
is the induced topology, and covers of jU lift uniquely to covers of U. Consequently
precomposition preserves locally bijective maps and commutes with sheafification,
with the comparison commuting with the sheafification units. Localize the sectionwise
strong symmetric monoidal precomposition functor along module sheafification.
The localized tensorator is invertible because of this sheafification comparison.
Associativity, units and symmetry follow from the presheaf diagrams by the localization
universal property. The equation on pure tensors follows from the equation on the
sheafification units and the identity map on the sectionwise tensor product. The
argument also applies to the empty component and the zero coefficient ring. -/
theorem clopen_ordinary_tensor_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ h : (ClopenData.clopenTensorRestriction.{t, u} j R).Braided,
      ∀ (F H : ClopenData.clopenTensorModules.{t, u} R) (U : Y.ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U))),
        (ClopenData.clopenTensorComparison.{t, u} j R h F H).hom.val.app (op U)
          (ClopenData.clopenTensorPure.{t, u} R F H _ x y) =
        ClopenData.clopenTensorPure.{t, u} ((ClopenData.clopenTensorRings.{t, u} j).obj R)
          ((ClopenData.clopenTensorRestriction.{t, u} j R).obj F)
          ((ClopenData.clopenTensorRestriction.{t, u} j R).obj H) (op U) x y := by sorry

end AlgebraicGeometry.Scheme.ProEt
