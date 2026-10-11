/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # The derived base-change morphism of O-modules

Source: Stacks Project, Cohomology, Remark 08HY; equivalently the unit construction
of Lemma 02N7 (blueprint: def-pc-derived-base-change-map).
-/

set_option autoImplicit false
universe uBC wBC uAdj wAdj
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry

/-- Derived pullback is left adjoint to derived direct image, bifunctorially on the
unbounded derived categories of O-modules. Source: Stacks, Tag 079W
(blueprint: def-pc-derived-base-change-map).
Proof: nonempty_derivedPullbackAdjunction (lem-pc-ringed-spaces-derived-adjoint)
gives existence of an unbounded adjunction. To specify the canonical one, the
module tensor pullback is left adjoint to module direct image by
lem-pc-module-pullback-adjunction. Their left and right derived functors are the
recorded derivedPullback and schemeDerivedDirectImage. Apply the abstract derived
adjunction theorem lem-pc-derived-adjoint-functors (Tag 09T5); its functoriality
clause gives naturality in both arguments. K-flat and K-injective resolutions give
existence on all objects, so the adjunction is unbounded. The displayed identity
pins its Hom equivalence to the canonical underived tensor-pullback adjunction,
the supplied left-derived counit and the recorded right-derived unit, as in
lem-pc-derived-adjoint-functors. It rules out arbitrary adjunction twists. -/
theorem exists_schemeDerivedAdjunction {X Y : Scheme.{uAdj}} (f : X ⟶ Y)
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))]
    [hAdd : (Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ adj : derivedPullback f ⊣ schemeDerivedDirectImage f,
      ∀ (M : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
        (K : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
        (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M ⟶ K),
        adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (ε.app M ≫ DerivedCategory.Qh.map a) =
          (DerivedCategory.Qh
            (C := SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))).map
            (((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory
                (ComplexShape.up ℤ)).homEquiv M K a) ≫
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K
      := by
  sorry


/-- The canonical base-change map for a commutative square of schemes. In particular
apply this to the chosen fibre product, or to the cartesian square obtained by
restricting its upper row to an open W and its inverse image W'.

This is the counit description of Stacks, Remark 08HY: transpose under Lf'^* ⊣ Rf'_*
the composite Lf'^* Lg^* Rf_* E ≅ Lg'^* Lf^* Rf_* E → Lg'^* E.
It is equivalently the unit description of Lemma 02N7 in the node: transpose under
Lg^* ⊣ Rg_* the unit map followed by direct-image composition comparisons.
Those comparisons are the mates of the same derived-pullback composition comparisons.
The functor comparisons below are selected from their left-derived universal property,
not arbitrary isomorphisms. The adjunction Hom equivalences are pinned to the same
left-derived counits as these comparisons and to the recorded right-derived units, via
`exists_schemeDerivedAdjunction`; no independent adjunction choice is allowed.
Source: Stacks, cohomology.tex, Remark 08HY and Lemma 02N7
(blueprint: def-pc-derived-base-change-map). -/
def schemeDerivedBaseChangeMap
    [∀ Y : Scheme.{uBC},
      HasDerivedCategory.{wBC} (SheafOfModules.{uBC} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{uBC}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (E : schemeDerivedCategory X) :
    (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ⟶
      (schemeDerivedDirectImage f').obj ((derivedPullback g').obj E) :=
  (Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f')
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f')
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f'))).homEquiv _ _
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app
        ((schemeDerivedDirectImage f).obj E) ≫
      eqToHom (congrArg (fun k =>
        (derivedPullback k).obj ((schemeDerivedDirectImage f).obj E)) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app
        ((schemeDerivedDirectImage f).obj E) ≫
      (derivedPullback g').map
        ((Classical.choose (exists_schemeDerivedAdjunction f
          (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
          ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
          ((Classical.choose (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition))) f))).counit.app E))

end AlgebraicGeometry
end
