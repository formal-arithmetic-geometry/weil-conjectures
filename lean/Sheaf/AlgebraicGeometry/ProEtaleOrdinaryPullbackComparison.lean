/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition

/-!
# The section-normalized ordinary pro-etale pullback comparison

Source: Stacks Project, sites-modules.tex, Tag 03D8,
lemma-push-pull-composition-modules; sites-cohomology.tex, Tag 0D6D.
(blueprint: def-sfb-proetale-ordinary-pullback-comparison).

The composite coefficient identification is the published
`proEtaleRingCompositeCoefficients`. The ordinary comparison is its canonical
adjunction mate, fixed by the fibre-product pasting equation on sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AcyclicHypercover

variable {X Y : Scheme.{u}} (h : Y ⟶ X)
  (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)

/-- The unique ordinary pullback comparison characterized by its direct-image mate.
Its section equation uses the actual fibre-product pasting isomorphism.
Source: Stacks, Tags 03D8 and 0D6D, used in the composition refinement of Tag 09A2
(blueprint: def-sfb-proetale-ordinary-pullback-comparison).
Proof: the coefficient identification for the composite is the canonical inverse-image
composition followed by c and d. The canonical pasting of base changes identifies
successive direct images on every section and preserves these scalar actions. Use the
normalized module adjunctions and their conjugation bijection to obtain a. This is the
ordinary comparison in lem-weil-pbc-proetale-derived-pullback-composition. The section
equation fixes the direct-image isomorphism; conjugation fixes a uniquely. -/
theorem existsUnique_composition {Z : Scheme.{u}} (k : Z ⟶ Y)
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T) :
    ∃! a : proEtaleRingModulePullback (k ≫ h) R T
        (proEtaleRingCompositeCoefficients k h R S T c d) ≅
      proEtaleRingModulePullback h R S c ⋙ proEtaleRingModulePullback k S T d,
      ∀ (N : proEtaleRingModules Z T) (W : X.ProEt)
        (m : ((proEtaleRingModuleDirectImage k S T d ⋙
          proEtaleRingModuleDirectImage h R S c).obj N).val.obj (op W)),
        ((conjugateIsoEquiv ((proEtaleRingModuleAdjunction h R S c).comp
          (proEtaleRingModuleAdjunction k S T d))
          (proEtaleRingModuleAdjunction (k ≫ h) R T
            (proEtaleRingCompositeCoefficients k h R S T c d)) a).hom.app N).val.app
              (op W) m =
          N.val.map ((MorphismProperty.Over.pullbackComp k h).hom.app W).op m := by
  sorry

/-- The ordinary coefficient comparison fixed by the section-normalized mate equation.
Source: Stacks, Tags 03D8 and 0D6D
(blueprint: def-sfb-proetale-ordinary-pullback-comparison). -/
def compositionIso {Z : Scheme.{u}} (k : Z ⟶ Y)
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T) :
    proEtaleRingModulePullback (k ≫ h) R T
        (proEtaleRingCompositeCoefficients k h R S T c d) ≅
      proEtaleRingModulePullback h R S c ⋙ proEtaleRingModulePullback k S T d :=
  Classical.choose (existsUnique_composition h R S c k T d).exists

end AlgebraicGeometry.Scheme.AcyclicHypercover
