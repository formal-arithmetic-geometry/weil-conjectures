/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact

/-! # Adjunction-normalized composition with independent coefficient universes

Source: Stacks Project, sites-modules.tex, Tag 03D8,
lemma-push-pull-composition-modules
(blueprint: lem-pur-proetale-module-pullback-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t r
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- The unique left-adjoint compositor whose mate is restriction along canonical
fibre-product pasting, for any commutative constant ring in an independent universe.
Source: Stacks Project, Tag 03D8, lemma-push-pull-composition-modules
(blueprint: lem-pur-proetale-module-pullback-composition).
Proof: the fibre-product pasting isomorphism gives the displayed direct-image map
on sections. The constant-section coefficient maps commute with this pasting:
transpose through sheafification and both maps send each coefficient to its
constant section. This gives the module direct-image natural isomorphism d.
Conjugate d through the composite and single module adjunctions. The mate
bijection gives a and its uniqueness, without choosing an unrelated isomorphism.
This is the same construction as proEtaleConstantRingModulePullbackComposition,
transported through the coefficient-sized site models; neither the site object
and morphism universes nor the coefficient and scheme universes are identified. -/
theorem coefficientModulePullbackComposition_existsUnique
    {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    ∃! a : coefficientProEtaleModulePullback (h ≫ f) A ≅
      coefficientProEtaleModulePullback f A ⋙ coefficientProEtaleModulePullback h A,
      ∃ d : coefficientProEtaleModuleDirectImage h A ⋙
          coefficientProEtaleModuleDirectImage f A ≅
            coefficientProEtaleModuleDirectImage (h ≫ f) A,
        conjugateIsoEquiv
          ((coefficientProEtaleModuleAdjunction f A).comp
            (coefficientProEtaleModuleAdjunction h A))
          (coefficientProEtaleModuleAdjunction (h ≫ f) A) a = d ∧
        ∀ (N : SheafOfModules.{max r (t + 1)}
            ((sheafCompose (ProEt.topology Z)
              (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
                ((constantSheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}).obj A)))
          (U : Y.ProEt)
          (x : ((coefficientProEtaleModuleDirectImage h A ⋙
            coefficientProEtaleModuleDirectImage f A).obj N).val.obj (op U)),
          (d.hom.app N).val.app (op U) x =
            N.val.map ((MorphismProperty.Over.pullbackComp h f).hom.app U).op x := by
  sorry

/-- Canonical composition fixed by the direct-image mate, with its finite unit normalization.
Source: Stacks Project, Tag 03D8
(blueprint: lem-pur-proetale-module-pullback-composition). -/
def coefficientModulePullbackComposition
    {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :=
  (coefficientModulePullbackComposition_existsUnique h f A).exists.choose

end AlgebraicGeometry.Scheme
