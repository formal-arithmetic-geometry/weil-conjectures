/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist

/-!
# Transport of the classical closed-support localization triangle

Source: main-20261015, sec-six-functors-basics/sk-prop-a1/sk-prop-a1.proof.md,
the localization triangle before applying Rp_*
(blueprint: lem-pur-classical-localization-triangle-transport).

The comparison maps below use the canonical derived mates. The unbounded etale
right derived functors are identified with their bounded below restrictions by
the canonical injective-derived compatibility, including on the closed term.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical mate on a bounded below input, with the unbounded etale source.
The first factor is the inverse of the canonical D+/D right-derived comparison;
the second is the inclusion of the specified bounded below mate. Exact comparison
inverse image is literally restricted to D+ in mapDerivedCategoryPlus.
Source: sk-prop-a1 proof, opening triangle; direct-image comparison, Tag 09A6
(blueprint: lem-pur-classical-localization-triangle-transport). -/
def classicalLocalizationDirectImageMap (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (g : V ⟶ T)
    (M : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj M.obj) ⟶
      ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlus.obj M)).obj :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.inv.app M) ≫
    DerivedCategory.Plus.ι.map ((comparisonDirectImageCanonicalMate A g).app M)

/-- All three transported arrows and their naturality, on precisely the inputs for
which the etale closed-support value is bounded below. The two isomorphism families
are fixed by equations with the canonical mates, rather than chosen freely. The
boundary formula uses the exact functor's canonical shift and contains no rotation.
The final three equations are naturality of the first object, third object and
boundary for arbitrary derived morphisms of admissible inputs.
Source: sk-prop-a1 proof, opening triangle, and direct-image comparison, Tag 09A6
(blueprint: lem-pur-classical-localization-triangle-transport). -/
def ClassicalLocalizationTriangleTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let C := ModuleCat.{u + 1} P.Coefficient
  let F := fun T : Scheme.{u} ↦ (comparisonUpperStar C T).mapDerivedCategory
  let Fp := fun T : Scheme.{u} ↦ (comparisonUpperStar C T).mapDerivedCategoryPlus
  let Ie := (Etale.lowerStar C i).rightDerivedFunctor
  let S := Ie.rightAdjoint
  let Ip := (lowerStar C i).rightDerivedFunctorPlus
  let Je := (Etale.upperStar C j).mapDerivedCategory
  let Jep := (Etale.upperStar C j).mapDerivedCategoryPlus
  let Re := (Etale.lowerStar C j).rightDerivedFunctor
  let Jp := (upperStar C j).mapDerivedCategoryPlus
  let Rp := (lowerStar C j).rightDerivedFunctorPlus
  let E := DerivedCategory.Plus (Sheaf X.smallEtaleTopology C)
  let H := fun B : E ↦ DerivedCategory.TStructure.t.plus (S.obj B.obj)
  let D := fun (B : E) (h : H B) ↦
    (⟨S.obj B.obj, h⟩ : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C))
  let V := fun (B : E) (h : H B) ↦ (Ip.obj ((Fp Z).obj (D B h))).obj
  let W := fun B : E ↦ (Rp.obj (Jp.obj ((Fp X).obj B))).obj
  ∃ δ : Je ⋙ Re ⟶ (S ⋙ Ie) ⋙ shiftFunctor _ (1 : ℤ),
    (∀ B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      Triangle.mk ((Adjunction.ofIsLeftAdjoint Ie).counit.app B)
        ((Etale.mapDerivedUpperStarLowerStarAdjunction C j).unit.app B)
        (δ.app B) ∈ distTriang _) ∧
    ∃ (α : ∀ (B : E) (h : H B), (F X).obj (Ie.obj (S.obj B.obj)) ≅ V B h)
      (γ : ∀ (B : E) (_h : H B), (F X).obj (Re.obj (Je.obj B.obj)) ≅ W B),
      (∀ (B : E) (h : H B),
        (α B h).hom = classicalLocalizationDirectImageMap P.Coefficient i (D B h)) ∧
      (∀ (B : E) (h : H B),
        (γ B h).hom = classicalLocalizationDirectImageMap P.Coefficient j (Jep.obj B) ≫
          DerivedCategory.Plus.ι.map (Rp.map
            ((directImageComparisonPullbackPlusIso P.Coefficient j).inv.app B))) ∧
      (∀ (B : E) (h : H B),
        (F X).map ((Etale.mapDerivedUpperStarLowerStarAdjunction C j).unit.app B.obj) ≫
          (γ B h).hom = DerivedCategory.Plus.ι.map
            ((derivedUpperStarLowerStarAdjunctionPlus C j).unit.app ((Fp X).obj B))) ∧
      (let b := fun (B : E) (h : H B) ↦
          (γ B h).inv ≫ (F X).map (δ.app B.obj) ≫
            ((F X).commShiftIso (1 : ℤ)).hom.app (Ie.obj (S.obj B.obj)) ≫
            (shiftFunctor _ (1 : ℤ)).map (α B h).hom
       (∀ (B : E) (h : H B),
          Triangle.mk
            ((α B h).inv ≫ (F X).map ((Adjunction.ofIsLeftAdjoint Ie).counit.app B.obj))
            (DerivedCategory.Plus.ι.map
              ((derivedUpperStarLowerStarAdjunctionPlus C j).unit.app ((Fp X).obj B)))
            (b B h) ∈ distTriang _) ∧
       (∀ (B B' : E) (h : H B) (h' : H B') (f : B ⟶ B'),
          (F X).map (Ie.map (S.map f.hom)) ≫ (α B' h').hom =
            (α B h).hom ≫ DerivedCategory.Plus.ι.map
              (Ip.map ((Fp Z).map (DerivedCategory.Plus.ι.preimage
                (X := D B h) (Y := D B' h') (S.map f.hom)))) ∧
          (F X).map (Re.map (Je.map f.hom)) ≫ (γ B' h').hom =
            (γ B h).hom ≫ DerivedCategory.Plus.ι.map (Rp.map (Jp.map ((Fp X).map f))) ∧
          DerivedCategory.Plus.ι.map (Rp.map (Jp.map ((Fp X).map f))) ≫ b B' h' =
            b B h ≫ (shiftFunctor _ (1 : ℤ)).map
              (DerivedCategory.Plus.ι.map
                (Ip.map ((Fp Z).map (DerivedCategory.Plus.ι.preimage
                  (X := D B h) (Y := D B' h') (S.map f.hom)))))))

/-- Exact comparison inverse image transports the whole ordinary etale localization
triangle with the specified canonical arrows and sign. No constructibility is assumed.
Source: sk-prop-a1.proof.md, first triangle before Rp_*
(blueprint: lem-pur-classical-localization-triangle-transport).

Proof (the eight steps of the node):
1. Closed and open immersions are monomorphisms and hence quasi-separated; i is
quasi-compact and j is quasi-compact by hypothesis. Apply direct-image comparison.
2. Closed direct images are exact on both sites (open-closed recollement and
proetale closed exactness); normalize their derived functors by the exact-functor
comparison. Exact comparison and open inverse images preserve D+ and triangles.
3. Bounded below injective models are K-injective and compute total derived direct
image. Thus its restriction to D+ is the bounded below functor, with the same unit;
this is rightDerivedFunctorPlusCompatibility in classicalLocalizationDirectImageMap.
4. Take the natural etale closed-support triangle of exists_etale_closedSupportTriangle
and apply the exact comparison functor, retaining its canonical shift isomorphism.
5. Use the canonical direct-image mates for i and j, and the inverse pullback
comparison for j, to obtain alpha and gamma. All factors are natural isomorphisms.
6. The mate unit identity identifies the transported second arrow with the actual
proetale unit. The first arrow is the etale counit precomposed with alpha inverse.
7. Conjugate the etale boundary by gamma inverse, the canonical shift, and alpha[1].
The three resulting squares give a triangle isomorphism, hence distinguishedness
by TR1. No rotation is made, so the displayed formula fixes the boundary sign.
8. Conjugate the natural etale triangle morphism for any f by these isomorphisms.
Naturality of the two mates and shift gives precisely the three final equations. -/
theorem classicalLocalizationTriangleTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ClassicalLocalizationTriangleTransport P i j := by
  sorry

end AlgebraicGeometry.ProEtale
