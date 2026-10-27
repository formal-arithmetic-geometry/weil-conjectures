module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.DerivedPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology

/-! # Derived base change of a relatively flat closed kernel

Source: Stacks Project, Tags 0CTA and 0E23
(blueprint: lem-sfb-relative-flat-closed-kernel-base-change).

The comparison is the derived counit followed by ordinary module exchange and
structure-sheaf multiplication. Only the two ambient derived categories are needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The derived-to-ordinary tensor-pullback comparison on a module in degree zero.
It uses the fixed derived counit and the comparison of left adjoints preserving the
section-normalized tensor adjunction; no derived-category choices on other schemes occur.
Source: Stacks, Tag 06YJ, specialized as in Tag 0E23
(blueprint: lem-sfb-relative-flat-closed-kernel-base-change). -/
def relativeClosedKernelPullbackComparison {T T0 : Scheme.{u}} (q : T ⟶ T0)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T0.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (M : T0.Modules) :
    (derivedPullback q).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T0.toRingedSpace)) 0).obj M) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback q).obj M) :=
  (derivedPullbackCounit q).app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T0.toRingedSpace)) 0).obj M) ≫
    (modulesQhCompSchemeDerivedCategoryEquivInverse T).hom.app
      (((Scheme.Modules.pullback q).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings T0.toRingedSpace)) 0).obj M)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback q) (.up ℤ) 0).hom.app M)) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
        (((Scheme.Modules.tensorPullbackSectionAdjunction q).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction q)).inv.app M)

/-- The canonical closed structure-kernel comparison: derived counit, ordinary exchange,
then the pushed-forward map `1 ⊗ s ↦ s` on the structure sheaf. It is defined for every
commutative square, independently of flatness or of being a closed immersion.
Source: Stacks, Tag 0E23 and Tag 0096
(blueprint: lem-sfb-relative-flat-closed-kernel-base-change). -/
def relativeClosedKernelBaseChangeMap {T0 T W0 W : Scheme.{u}}
    (i0 : W0 ⟶ T0) (i : W ⟶ T) (q : T ⟶ T0) (r : W ⟶ W0)
    (h : r ≫ i0 = i ≫ q)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T0.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    (derivedPullback q).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T0.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward i0).obj (SheafOfModules.unit W0.ringCatSheaf))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) :=
  relativeClosedKernelPullbackComparison q
      ((Scheme.Modules.pushforward i0).obj (SheafOfModules.unit W0.ringCatSheaf)) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
        (Scheme.Modules.moduleBaseChangeMap i0 i q r h
            (SheafOfModules.unit W0.ringCatSheaf) ≫
          (Scheme.Modules.pushforward i).map (Scheme.Modules.tensorPullbackObjUnitToUnit r))

/-- Arbitrary base change of a relatively flat closed structure-sheaf kernel.
The isomorphism is pinned to the canonical comparison just defined.

Source: Stacks Project, Tag 0CTA, lemma-case-of-tor-independence, and Tag 0E23,
lemma-compare-base-change-closed-immersion
(blueprint: lem-sfb-relative-flat-closed-kernel-base-change).

Proof:
1. Set X = X0 ×_{S0} S. Fibre-product pasting identifies T with T0 ×_{X0} X,
   and W with W0 ×_{X0} X. Since Y0/S0 is flat, T0/X0 is flat by
   lem-weil-pbc-flat-morphism-base-change. The morphism i is closed by
   lem-weil-pbc-closed-immersion-base-change.
2. Apply lem-sfb-flat-families-tor-independent over X0 to W0 and T0, whose
   structure maps are flat, with base extension X → X0. It gives stalkwise
   Tor independence of i0 and q, with no flatness assumption on q or i0.
3. Apply lem-sfb-tor-independent-closed-pushforward-comparison to this square
   and O_W0[0], obtaining Lq* Ri0* O_W0[0] ≅ Ri* Lr* O_W0[0].
4. Use lem-sc-derived-pullback-structure-sheaf-local to identify Lr* O_W0[0]
   with O_W[0]. Both closed pushforwards preserve homology by
   lem-pc-closed-module-pushforward-homology, so their derived images of these
   singles equal ordinary pushforward in degree zero. The derived counit and
   adjunction mate identify the resulting map with relativeClosedKernelBaseChangeMap;
   its structure map is normalized by 1 ⊗ s ↦ s. No condition on a, X0/S0,
   Noetherianity or finiteness has been used. -/
theorem relativeFlatClosedKernel_baseChange
    {S0 S X0 Y0 T0 T W0 W : Scheme.{u}}
    (x0 : X0 ⟶ S0) (y0 : Y0 ⟶ S0) (a : S ⟶ S0)
    (pX : T0 ⟶ X0) (pY : T0 ⟶ Y0) (hT0 : IsPullback pX pY x0 y0)
    (q : T ⟶ T0) (b : T ⟶ S) (hT : IsPullback q b (pX ≫ x0) a)
    (i0 : W0 ⟶ T0) [IsClosedImmersion i0] [Flat y0] [Flat (i0 ≫ pX)]
    (r : W ⟶ W0) (i : W ⟶ T) (hW : IsPullback r i i0 q)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T0.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ e : (derivedPullback q).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings T0.toRingedSpace)) 0).obj
            ((Scheme.Modules.pushforward i0).obj (SheafOfModules.unit W0.ringCatSheaf))) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)),
      e.hom = relativeClosedKernelBaseChangeMap i0 i q r hW.w := by
  sorry

end AlgebraicGeometry
