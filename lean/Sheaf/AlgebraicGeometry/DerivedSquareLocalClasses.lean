/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedSquareUnitMap
public import Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Local classes of the ordinary-unit map in a square

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-derived-square-local-classes).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- Restrict an h-map, keeping the restriction of its global coefficient as target.
Source: Stacks Project, Tag 01FB
(blueprint: lem-weil-pbc-derived-square-local-classes). -/
def restrictedDirectImageMap {Z X : Scheme.{u}} (v : Z ⟶ X)
    {F : X.Modules} {G : Z.Modules} (φ : F ⟶ (pushforward v).obj G) (U : X.Opens) :
    (restrictFunctor U.ι).obj F ⟶
      (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) :=
  ((restrictAdjunction U.ι).homEquiv _ _).symm
    (φ ≫ (pushforward v).map ((restrictAdjunction (v ⁻¹ᵁ U).ι).unit.app G) ≫
      (pushforwardComp (v ⁻¹ᵁ U).ι v).hom.app
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) ≫
      ((pushforwardComp (v.resLE U (v ⁻¹ᵁ U) le_rfl) U.ι ≪≫
        pushforwardCongr (v.resLE_comp_ι le_rfl)).inv.app
          ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G)))

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical total/classical comparison, with the total derived-category
universe fixed by the supplied family of scheme module categories.
Source: total/classical right-derived compatibility
(blueprint: lem-weil-pbc-derived-square-local-classes). -/
def schemeSingleCohomologyComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) ≅
      ((pushforward f).rightDerived q).obj F :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F q


/-- The local cocycle equation for an arbitrary coefficient h-map in a commutative
square. The edge is specified solely by its local sheafification equation. This
requires no derived-pullback input, top-degree bound, or tensor-pullback unit.
Source: Stacks Project, Cohomology, Tags 01E4 and 01FB, with the canonical local
Leray and sheafification comparisons of Tags 0D5X and 0BKJ
(blueprint: lem-weil-pbc-derived-square-local-classes).

Proof: Resolve F and G by I and J. Resolve v_*J by an injective complex L and
lift the coefficient map to beta:I -> L. Its augmentation is phi followed by
v_* of the augmentation of J and the replacement ell:v_*J -> L. The normalized
right-adjoint comparison of the square identifies Rf(phi[0]) followed by that
comparison with the roof f_*I -> f_*L <- g_*k_*J. Its arrows are f_*beta and
f_*ell, including the sectionwise comparison of the square. Restriction preserves
injective resolutions and the augmentation equations. On U, sections of ell are
a quasi-isomorphism by the pushforward-injectives section theorem. Thus the map
on cohomology of this roof is precisely moduleCohomologyFMap of the restricted
phi, by its independence-of-choices theorem. The local class map sends a cocycle
to the section of the cohomology sheaf represented by that cocycle. Its naturality
for both arrows of the roof gives the same equation after passage to cohomology
sheaves. The edge's defining equation removes the intermediate local cohomology
of Rg_*Rk_*G. Finally the canonical total/classical comparisons and the two
augmentation-preserving restricted-resolution comparisons give exactly the
maps displayed below. No class map is inverted, only comparison isomorphisms
and the cohomology of sections of ell. The argument includes q=0, empty opens,
zero coefficients, and nonflat morphisms. -/
theorem derivedSquareUnit_localClasses {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G) (q : ℕ)
    (e : (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).obj
        ((schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))) ⟶
      (pushforward g).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (q : ℤ)).obj
          ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))))
    (he : ∀ V : S.Opensᵒᵖ,
      (RingedSpace.topEdgeLocalClass S.toRingedSpace (q : ℤ)
        ((schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)))).app V ≫
        ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map e).hom.app V =
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app V ≫
      (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app V)
    (V : S.Opens) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    (resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V R.sections q ≫ Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V) ≫
      Hom.app (M := ((pushforward f).rightDerived q).obj F)
        (N := (pushforward g).obj (((pushforward k).rightDerived q).obj G))
        ((schemeSingleCohomologyComparison f F q).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).map
            (derivedSquareUnitMap f k g v h F G φ) ≫ e ≫
        (pushforward g).map (schemeSingleCohomologyComparison k G q).hom) V =
      moduleCohomologyFMap (v.resLE (f ⁻¹ᵁ V) (v ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
        (restrictedDirectImageMap v φ (f ⁻¹ᵁ V)) q ≫
      resolutionSectionClass R'.resolution
        (((pushforward k).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
        (g ⁻¹ᵁ V) (R'.sections ≪≫ eqToIso (congrArg (fun U ↦
          ((RingedSpace.openModuleSections Z.toRingedSpace U).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj J.cocomplex) (by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]))) q ≫
      Hom.app (J.isoRightDerivedObj (pushforward k) q).inv (g ⁻¹ᵁ V) := by
  sorry

end AlgebraicGeometry
