/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.Sites.ToposComplementFactorization
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.TraceFormula.EtaleClosedComplementSets
import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Closed complementary subtopoi and supported constant-coefficient modules

Source: Stacks Project, Sites, Tags 08LY, 08LZ, 08M0, 08M1 and 00YV;
Modules on Sites, Tag 08M3; Etale Cohomology, Tag 04CA(1)
(blueprint: lem-trf-oriented-closed-base-localization).

The three parts of the statement are packaged below. Small-site presentations in the
module part allow use of the recorded category of modules over a constant ring sheaf.
Its inverse images are the normalized lifts of the actual geometric adjunctions, so the
unit and counit in the conclusion are their actual adjunction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v uH vH uG vG t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ClosedBaseLocalization

/-- The construction and universal properties of the closed complement of `U`.
The `baseChange` field spells out its inverse-image property: a morphism into the new
closed complement exists exactly when its composite factors through the old one, and
right whiskering is bijective on all direct-image natural transformations.

Source: Stacks, Sites, Tags 08LY, 08LZ, 08M0, 08M1
(blueprint: lem-trf-oriented-closed-base-localization). -/
structure ComplementData {E : Type u} [Category.{v} E] [HasBinaryProducts E] (U : E) where
  closedTopos : IsGrothendieckTopos.{w} (closedComplementObjects U).FullSubcategory
  openTopos : IsGrothendieckTopos.{w} (Over U)
  i : GeometricMorphism (closedComplementObjects U).FullSubcategory E
  j : GeometricMorphism (Over U) E
  inclusion : i.direct ≅ (closedComplementObjects U).ι
  openInverse : j.inverse ≅ Over.star U
  fullyFaithful : i.direct.FullyFaithful
  factorization : ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
    (∀ a : GeometricMorphism H E,
      (∃ b : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
        Nonempty ((b.comp i).direct ≅ a.direct)) ↔
      Nonempty (IsInitial (a.inverse.obj U))) ∧
    (∀ b d : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
      Function.Bijective (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ i.direct))
  baseChange : ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
    ∀ a : GeometricMorphism H E, ∃ products : HasBinaryProducts H,
      IsGrothendieckTopos.{w}
        (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory ∧
      ∃ k : GeometricMorphism
          (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory H,
        Nonempty (k.direct ≅
          (@closedComplementObjects H _ products (a.inverse.obj U)).ι) ∧
        Nonempty k.direct.FullyFaithful ∧
        ∃ r : GeometricMorphism
            (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory
            (closedComplementObjects U).FullSubcategory,
          Nonempty ((r.comp i).direct ≅ (k.comp a).direct) ∧
          ∀ (G : Type uG) [Category.{vG} G], IsGrothendieckTopos.{w} G →
            (∀ b : GeometricMorphism G H,
              (∃ d : GeometricMorphism G
                  (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory,
                Nonempty ((d.comp k).direct ≅ b.direct)) ↔
              (∃ c : GeometricMorphism G (closedComplementObjects U).FullSubcategory,
                Nonempty ((c.comp i).direct ≅ (b.comp a).direct))) ∧
            (∀ d e : GeometricMorphism G
                (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory,
              Function.Bijective
                (fun τ : d.direct ⟶ e.direct ↦ Functor.whiskerRight τ k.direct))

/-- The module clauses on any small-site presentations of the closed and open embeddings.
The hypotheses on `i` and `j` say precisely that these are the closed complement and the
open slice of `U`. The supplied lifts are those of the recorded constant-module interface,
including its scalar normalization and compatibility with the original adjunction unit.
Exactness of `i_*` is expressed by preservation of finite limits and finite colimits.

Source: Stacks, Sites, 00YV and 08M1; Modules on Sites, 08M3
(blueprint: lem-trf-oriented-closed-base-localization). -/
def ModuleAssertion {C D O : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory O]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology O)
    (U : Sheaf J (Type w))
    (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w))) : Prop :=
  Nonempty i.direct.FullyFaithful →
  (∀ H : Sheaf J (Type w), i.direct.essImage H ↔ closedComplementObjects U H) →
  (∃ e : Sheaf L (Type w) ≌ Over U, Nonempty (j.inverse ⋙ e.functor ≅ Over.star U)) →
  ∀ (Λ : Type w) [CommRing Λ]
    (di : ConstantLeftModuleInverseImageLift J K Λ i.inverse i.direct i.adj i.leftExact)
    (dj : ConstantLeftModuleInverseImageLift J L Λ j.inverse j.direct j.adj j.leftExact),
    PreservesFiniteLimits di.moduleDirect ∧ PreservesFiniteColimits di.moduleDirect ∧
    di.moduleDirect.Full ∧ di.moduleDirect.Faithful ∧
    (∀ N : ConstantLeftModuleInverseImage.Modules K Λ, IsIso (di.moduleAdj.counit.app N)) ∧
    (∀ M : ConstantLeftModuleInverseImage.Modules J Λ,
      di.moduleDirect.essImage M ↔ IsZero (dj.moduleFunctor.obj M)) ∧
    (∀ M : ConstantLeftModuleInverseImage.Modules J Λ,
      IsZero (dj.moduleFunctor.obj M) → IsIso (di.moduleAdj.unit.app M))

/-- The subterminal represented by the complementary open of a scheme closed immersion.
We use the existing sheafified Yoneda functor, lifted to the universe of small etale
sheaves; the small etale topology is subcanonical, so this is the represented sheaf.

Source: Stacks, Etale Cohomology, 04CA(1); Sites, 08LY
(blueprint: lem-trf-oriented-closed-base-localization). -/
def representedOpenComplement {F S : AlgebraicGeometry.Scheme.{t}} (k : F ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion k] : Sheaf S.smallEtaleTopology (Type (t + 1)) :=
  (presheafToSheaf S.smallEtaleTopology (Type (t + 1))).obj
    (uliftYoneda.{t + 1}.obj (AlgebraicGeometry.Scheme.Etale.mk k.openComplement.ι))

end CategoryTheory.ClosedBaseLocalization

namespace CategoryTheory

/-- Closed complementary subtopoi, their universal inverse-image property, exact fully
faithful direct image of constant-ring modules, and the small etale scheme example.

Source: Stacks, Sites, 08LY, 08LZ, 08M0, 08M1, 00YV; Modules on Sites, 08M3;
Etale Cohomology, 04CA(1)
(blueprint: lem-trf-oriented-closed-base-localization).

Proof plan (the three steps of the DAG node):
1. Apply `lem-trf-topos-complement-factorization` to `U` to obtain the full subcategory,
   geometric embedding with inclusion direct image, open slice, and universal property
   including all direct-image 2-morphisms. Apply the same construction to `a.inverse.obj U`.
   The factorization criterion for a composite is initiality of `b.inverse.obj
   (a.inverse.obj U)`. It gives the comparison square and the inverse-image universal
   property in `ComplementData.baseChange`, including 2-morphisms by full faithfulness.
2. Apply `lem-pe-constant-left-module-inverse-image` to these geometric adjunctions. Their
   normalized lifts give exact inverse image on constant-ring modules. The underlying
   closed direct image is fully faithful, so its module direct image is fully faithful
   and its counit is invertible. The condition `j^* M = 0` says that the underlying sheaf
   has `U × M → U` invertible. Lift its underlying object through the closed embedding;
   full faithfulness descends addition and zero, and the canonical constant-ring comparison
   descends the scalar action. Faithfulness verifies the module axioms. This proves the
   essential-image characterization. For exactness, the right adjoint preserves kernels.
   The ambient cokernel of a map between closed-image modules is supported, since exact
   open restriction kills it. Descend it through the essential image; exact closed inverse
   image and the invertible counit identify it with the closed cokernel. Hence direct image
   also preserves cokernels and is exact. The triangle identities give the actual unit
   isomorphism for supported modules.
3. Apply `lem-trf-etale-closed-complement-sets` to the scheme closed immersion. Its actual
   direct image is fully faithful, its counit is invertible, and its essential image is
   precisely terminal restriction to the complementary open. Open restriction is the slice
   pullback along the represented subterminal, so this condition is exactly invertibility
   of `U × H → U`. Equality of the essential images gives the displayed equivalence over
   the ambient etale topos, with comparison to the scheme-induced direct image.
-/
theorem oriented_closed_base_localization :
    (∀ (E : Type u) [Category.{v} E], IsGrothendieckTopos.{w} E →
      ∀ U : E, IsSubterminal U → ∃ products : HasBinaryProducts E,
        Nonempty (@ClosedBaseLocalization.ComplementData.{w, u, v, uH, vH, uG, vG}
          E _ products U)) ∧
    (∀ (C D O : Type w) [SmallCategory C] [SmallCategory D] [SmallCategory O]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology O)
      (U : Sheaf J (Type w)), IsSubterminal U →
      ∀ (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
        (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w))),
        ClosedBaseLocalization.ModuleAssertion J K L U i j) ∧
    (∀ (F S : AlgebraicGeometry.Scheme.{t}) (k : F ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion k],
      IsSubterminal (ClosedBaseLocalization.representedOpenComplement k) ∧
      ∃ e : Sheaf F.smallEtaleTopology (Type (t + 1)) ≌
          (closedComplementObjects
            (ClosedBaseLocalization.representedOpenComplement k)).FullSubcategory,
        Nonempty (e.functor ⋙
          (closedComplementObjects (ClosedBaseLocalization.representedOpenComplement k)).ι ≅
            AlgebraicGeometry.etaleSetDirectImage k)) := by
  sorry

end CategoryTheory
