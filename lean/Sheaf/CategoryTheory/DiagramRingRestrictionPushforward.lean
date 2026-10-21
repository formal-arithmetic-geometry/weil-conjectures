/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.DiagramSiteSheafEquivalence
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Coefficient restriction and direct image on derived diagram topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition, applied on the small diagram sites
(blueprint: lem-pur-diagram-ring-restriction-pushforward).

Ring diagrams are represented by ring sheaves on `diagramSiteTopology J C K`.
Their module sheaves have precisely the semilinear horizontal transition maps.
The helpers below transport the componentwise geometric adjunction to those sites.
The final equation characterizes the comparison through the common composite:
its two sides are the two derived composition units, after termwise scalar restriction.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Componentwise inverse image, transported to the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; the product-site realization
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientInverse
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (F : Sheaf L (Type u) ⥤ Sheaf K (Type u)) :=
  ((diagramSiteSheafEquivalence J D L).functor ⋙
    (Functor.whiskeringRight J _ _).obj F) ⋙ (diagramSiteSheafEquivalence J C K).inverse

/-- Componentwise direct image, transported to the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; the product-site realization
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientDirect
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u)) :=
  (diagramSiteSheafEquivalence J C K).functor ⋙
    ((Functor.whiskeringRight J _ _).obj G ⋙ (diagramSiteSheafEquivalence J D L).inverse)

/-- The componentwise geometric adjunction on the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; componentwise adjunction and site equivalence
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientAdjunction
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (adj : F ⊣ G) :
    diagramCoefficientInverse J C D K L F ⊣ diagramCoefficientDirect J C D K L G :=
  ((diagramSiteSheafEquivalence J D L).toAdjunction.comp
    (adj.whiskerRight J)).comp (diagramSiteSheafEquivalence J C K).symm.toAdjunction

/-- Forget module structure to the underlying sheaf of sets on a diagram site.
This is only the composite of the existing forgetful functors.
Source: Stacks Project, Modules on Sites, Tag 03DA
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
noncomputable abbrev diagramCoefficientUnderlying
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) :=
  SheafOfModules.toSheaf.{u} R ⋙ sheafCompose K (forget AddCommGrpCat)

/-- Derived scalar restriction commutes with derived diagram direct image, with its
common-composite normalization before evaluation.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition
(blueprint: lem-pur-diagram-ring-restriction-pushforward).

Proof plan:
1. Use lem-weil-pbc-diagram-site-realization to realize the diagram topoi.
A ring sheaf on the product site is the ring diagram; its module sheaves have
semilinear transitions by def-weil-sheaf-of-modules-category. The geometric
adjunction is the componentwise adjunction transported by the site equivalences.
2. The identity-topos ring maps aX and aY have module direct images
SheafOfModules.restrictScalars (def-pc-sheaf-restrict-scalars). The square hRing
identifies the two structural maps of the composite. Under the specified
underlying direct-image identifications this gives the unique ordinary iso c.
3. Restriction changes only scalar actions, so is exact on underlying abelian
sheaves. By lem-weil-pbc-exact-functor-derived-factorization, it has termwise
localization lifts rX and rY with the isomorphisms phiX and phiY. For a resolution
M -> I, restriction preserves the quasi-isomorphism, even if its image is not
K-injective; this identifies the lifts with the derived identity-topos direct images.
4. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to both
factorizations of the common ringed-topos morphism. The two composition
comparisons, through the derived direct image of that common morphism, give kappa.
5. The composition comparisons commute with their resolution units. After the
termwise identifications of step 3, this is exactly the displayed equation for
every complex M. Uniqueness of derived functors makes this equation characterize
kappa uniquely. All functors act on the full diagram site; no evaluation is used. -/
theorem diagramRingRestrictionPushforward
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (SX : Sheaf K RingCat.{u}) (SY : Sheaf L RingCat.{u})
    (hSX : ∀ (U : Cᵒᵖ) (a b : SX.obj.obj U), a * b = b * a)
    (hSY : ∀ (U : Dᵒᵖ) (a b : SY.obj.obj U), a * b = b * a)
    (BX : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    (BY : Sheaf (diagramSiteTopology J D L) RingCat.{u})
    (hBX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (hBY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : BY.obj.obj U), a * b = b * a)
    (aX : diagramSiteRing J C K SX ⟶ BX) (aY : diagramSiteRing J D L SY ⟶ BY)
    (s : RingedToposMorphism SX SY)
    (fB : RingedToposMorphism BX BY)
    (fS : RingedToposMorphism (diagramSiteRing J C K SX) (diagramSiteRing J D L SY))
    (hInvB : fB.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hInvS : fS.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hDirB : fB.direct = diagramCoefficientDirect J C D K L s.direct)
    (hDirS : fS.direct = diagramCoefficientDirect J C D K L s.direct)
    (hAdjB : HEq fB.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hAdjS : HEq fS.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hStructuralS : ∀ (j : J) (U : C),
      HEq (fS.ringMap.hom.app (Opposite.op (Opposite.op j, U)))
        (s.ringMap.hom.app (Opposite.op U)))
    (hRing : fB.inverse.map ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).map aY) ≫ fB.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).obj (diagramSiteRing J D L SY)))
        (hInvB.trans hInvS.symm)) ≫ fS.ringMap ≫
      (sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY))] :
    ∃ (rX : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)))
      (rY : DerivedCategory.{w} (ringedSiteModules.{u} BY) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
        (SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
        (SheafOfModules.restrictScalars.{u} aY).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (RB : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} BY))
      (RS : DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (etaB : fB.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RB)
      (etaS : fS.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RS),
      RB.IsRightDerivedFunctor etaB
        (HomologicalComplex.quasiIso (ringedSiteModules.{u} BX) (ComplexShape.up ℤ)) ∧
      RS.IsRightDerivedFunctor etaS (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} (diagramSiteRing J C K SX)) (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} BX) ℤ,
        I.IsKInjective → IsIso (etaB.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ℤ,
        I.IsKInjective → IsIso (etaS.app I)) ∧
      ∃! c : fB.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
          SheafOfModules.restrictScalars.{u} aX ⋙ fS.modules,
        (∀ M : ringedSiteModules.{u} BX,
          (diagramCoefficientUnderlying (diagramSiteRing J D L SY)).map (c.hom.app M) ≫
              fS.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
            fB.underlying.hom.app M ≫
              eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M))
                (hDirB.trans hDirS.symm))) ∧
        ∃! kappa : RB ⋙ rY ≅ rX ⋙ RS,
          ∀ M : CochainComplex (ringedSiteModules.{u} BX) ℤ,
            phiY.inv.app ((fB.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
                rY.map (etaB.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
              DerivedCategory.Q.{w}.map
                  ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app M) ≫
                etaS.app
                  (((SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj M) ≫ RS.map (phiX.inv.app M) := by
  sorry

end CategoryTheory
