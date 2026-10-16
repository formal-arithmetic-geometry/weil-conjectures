/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ClosedProperSupportLocality
import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk

/-!
# Composition and base change for sections with proper support

Source: Stacks Project, More on Étale Cohomology, Tags 0F4X, 0F4Y, 0F50, 0F51,
0F55 and 0F77 (blueprint: lem-cbc-proper-support-sheaf-composition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The proper-support subsheaves form functors, with composition, proper and open
specializations, and base change compatible with composition.
Source: Stacks Project, Tags 0F4X, 0F4Y, 0F50, 0F51, 0F55, 0F77.
(blueprint: lem-cbc-proper-support-sheaf-composition)

The functors and inclusions are specified together: objectwise their images are exactly
sections with the indicated closed geometric-germ support and proper reduced subscheme.
The composition isomorphism is specified by its composite into the ordinary direct image.
The base-change isomorphism is specified by the ordinary adjunction comparison.

Proof:
1. The zero locus is open (lem-sc-etale-section-zero-open). Inverse-image stalk germs
identify pulled-back supports with inverse images (lem-weil-pbc-inverse-image-stalk-germ
and prop-weil-pbc-inverse-image-modules-exact). Supports of sums lie in unions and scalar
multiplication decreases support.
2. Closed-subset properness and finite unions give submodules. Properness is local for
étale covers (lem-cbc-closed-proper-support-locality), so gluing in the direct image gives
a subsheaf. Linear maps decrease support, yielding the functor and natural inclusion.
3. Separatedness and local finite type are preserved by composition and base change;
the closed-subscheme maps used below are locally of finite type.
4. For a section with support proper over the intermediate base, its support as a section
of the support direct image is the closed image of its original support: vanishing is
Zariski local, and the subsheaf inclusion detects zero sections.
5. A closed support proper over the final base is proper over the separated intermediate
base (lem-weil-pbc-proper-over-separated); its image is proper over the final base.
Conversely properness over the intermediate base and properness of that image imply
properness over the final base by the union-preimage lemma. Thus composition is the
identity on sections inside the ordinary composite direct image.
6. If the map is proper every closed support is proper, by proper base change and
properness of closed immersions (lem-weil-pbc-closed-immersion-proper).
7. For an open immersion the presheaf extension maps into the support subsheaf, and hence
so does its sheafification. Its stalks agree inside the open and both vanish outside;
lem-weil-pbc-extension-by-zero-stalks and stalk detection give the isomorphism.
8. Pullback of sections preserves proper support by base change. Adjunction gives the
restricted ordinary comparison. On geometric stalks it is the identity on compactly
supported sections of the geometric fibre (lem-cbc-proper-support-geometric-stalk), so
it is invertible by lem-weil-pbc-sets-etale-iso-on-geometric-stalks.
9. Ordinary comparison maps paste by lem-weil-pbc-mate-pasting, using the unit-compatible
inverse-image compositors of lem-weil-pbc-sets-etale-inverse-image-composition-units.
Compose both support paths with the injective support inclusion to obtain equality.
Every map is linear and natural; composition is the identity on underlying sections. -/
theorem properSupportSheafComposition (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} Λ) f),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (op V)) ∧
        ∀ s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (op V)) t = s) ↔
          ∃ T : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v default ∈ T ↔
                (Scheme.pointSmallEtale
                  (v ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
              pullback.fst V.hom f)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsProper f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso ((ι f).app F)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsOpenImmersion f],
        ∃ o : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) f ≅ L f,
          o.hom ≫ ι f = openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) f) ∧
      ∃ (c : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g],
          L f ⋙ L g ≅ L (f ≫ g))
        (e : ∀ (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (a : X' ⟶ X)
          (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
          [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b),
          L f ⋙ upperStar (ModuleCat.{u + 1} Λ) b ≅
            upperStar (ModuleCat.{u + 1} Λ) a ⋙ L f'),
        (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (c X Y Z f g).hom.app F ≫ (ι (f ≫ g)).app F =
            (ι g).app ((L f).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) g).map ((ι f).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F) ∧
        (∀ (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (a : X' ⟶ X)
          (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
          [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b)
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (e X Y X' Y' f a b f' sq).hom.app F ≫
              (ι f').app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) =
            (upperStar (ModuleCat.{u + 1} Λ) b).map ((ι f).app F) ≫
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app
                ((upperStar (ModuleCat.{u + 1} Λ) b).obj
                  ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) f').map
                ((upperStarComp (ModuleCat.{u + 1} Λ) f' b).inv.app
                  ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
                  (upperStarComp (ModuleCat.{u + 1} Λ) a f (f' ≫ b) sq.w.symm).hom.app
                    ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) f').map
                ((upperStar (ModuleCat.{u + 1} Λ) a).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F))) ∧
        (∀ (X Y Z X' Y' Z' : Scheme.{u})
          (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
          (a : Z' ⟶ Z) (b : Y' ⟶ Y) (d : X' ⟶ X)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
          [IsSeparated f'] [LocallyOfFiniteType f'] [IsSeparated g'] [LocallyOfFiniteType g']
          (sf : IsPullback d f' f b) (sg : IsPullback b g' g a)
          (sfg : IsPullback d (f' ≫ g') (f ≫ g) a)
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (upperStar (ModuleCat.{u + 1} Λ) a).map ((c X Y Z f g).hom.app F) ≫
              (e X Z X' Z' (f ≫ g) d a (f' ≫ g') sfg).hom.app F =
            (e Y Z Y' Z' g b a g' sg).hom.app ((L f).obj F) ≫
              (L g').map ((e X Y X' Y' f d b f' sf).hom.app F) ≫
              (c X' Y' Z' f' g').hom.app
                ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) := by
  sorry

end AlgebraicGeometry.Etale
