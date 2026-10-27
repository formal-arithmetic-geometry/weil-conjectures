/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.CategoryTheory.CechLocalizationUnitModels
import Sheaf.CategoryTheory.CechPushforwardAugmentedModel
import Sheaf.CategoryTheory.CosimplicialInjectiveTotalReplacement

/-! # Functorial augmented Cech pushforward models

Source: Stacks 03FC and 0141.
(blueprint: lem-sfb-cech-pushforward-augmented-family).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uP vP

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CechLocalizationUnit

/-- Strict assembly of the normalized pushforward models over the parameter category.

Source: Stacks sites-cohomology.tex, lemma-injective-module-trivial-cech (03FC),
derived.tex, lemma-functorial-injective-resolutions (0141), and the normalized
pushforward interface of lem-sfb-cech-pushforward-augmented-model.
(blueprint: lem-sfb-cech-pushforward-augmented-family).

Proof: Choose one functorial nonnegative injective resolution functor, and apply it to
N in degree zero. Each N.map has its resulting strict resolution map. Apply D.image
in every nerve degree and f.modules termwise. Use D.image.map for every coface,
codegeneracy and refinement. Functoriality and naturality of D.image give the identity,
composition and mixed squares, so these data are a functor P into cosimplicial complexes.
The point model is f.modules applied to the same resolution. The augmentation is
D.augmentation on that resolution, followed by f.modules. Its naturality supplies a
transformation of the entire P diagrams. The normalized total augmentation is the map
into Cech degree zero; the augmentation equation makes it a chain map. In nonnegative
degree its component is the prescribed summand inclusion, and in negative degree its
source vanishes. The injective-image augmentation theorem, as packaged by the existing
pushforward-model theorem, makes it a quasi-isomorphism. Use the same theorem's column
and composition-unit equations to identify its columns with baseColumn. The unique
right-derived comparisons for the fixed resolution give pointIso. Their unit equations
and naturality under image transformations give operator and natural, including all
codegeneracies and simultaneous changes of cover and module. The unit equation for
D.augmentation gives augmentation. No arbitrary lifts are chosen independently for
arrows: all maps come from the one resolution functor, so the laws hold before
localization as required by PushforwardFamily. -/
theorem cech_pushforward_augmented_family
    {CX CV : Type u} [SmallCategory CX] [SmallCategory CV]
    {JX : GrothendieckTopology CX} {JV : GrothendieckTopology CV}
    (RX : Sheaf JX CommRingCat.{u}) (RV : Sheaf JV CommRingCat.{u})
    [IsGrothendieckAbelian.{u} (Modules RX)] [IsGrothendieckAbelian.{u} (Modules RV)]
    [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} (Modules RV)]
    (f : RingedToposMorphism
      ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose JV (forget₂ CommRingCat RingCat)).obj RV))
    (fInverse : Modules RV ⥤ Modules RX) [fInverse.Additive]
    [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (fAdj : fInverse ⊣ f.modules)
    {P : Type uP} [Category.{vP} P]
    (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ Modules RX)
    (cover : ∀ p : P, Epi (terminal.from (V.obj (op p))))
    (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)) :
    Nonempty (PushforwardFamily RX RV D f.modules V N) := by sorry

end CategoryTheory.CechLocalizationUnit
