/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # K-flat counit connecting-map normalization

Source: Stacks Project, Tag 06YJ, K-flat computation; the supplied-tensorator
normalization of the parent cone node, expanded by the agent.
(blueprint: lem-sc-derived-pullback-kflat-cone-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The K-flat counit identifies the cone connecting map with the comparison
obtained from the supplied inverse tensorator and a single shifted-unit isomorphism.
No distinguishedness or isomorphism of triangles is asserted here.

Source: Stacks Project, Tag 06YJ, K-flat computation of derived pullback;
the supplied-tensorator normalization in step 3 of the parent cone node.
(blueprint: lem-sc-derived-pullback-kflat-cone-counit-normalization).

Proof. The resolving-class construction of derived pullback gives its counit,
invertible on every K-flat representative. Transport the counit from the functor
with the recorded tensor-pullback objects and maps to the actual tensor-pullback
functor. Represent the unit by the structure sheaf in degree zero and its
translate by that complex translated by one. Both are K-flat. Termwise pullback
identifies them with the corresponding complexes on Z. The counit and the supplied
monoidal unit map give e, chosen independently of P, Q and p.
For a K-flat map p, its cone is K-flat. The additive mapping-cone comparison
identifies termwise pullback of its projection with the projection of the pulled-back
cone. Rewrite the translation of P as the shifted unit tensor P by the
first-variable Koszul comparison and translated left unitor. Tensorator naturality
moves the projection through this rewrite. Substitute tensorator associativity
and its unit equations: the source rewrite is F(c_Y inverse), followed by the
supplied inverse tensorator, e tensor identity, and c_Z. The remaining component
of the counit is its component at P translated by one. This is exactly the stated
connecting-map equality. Zero P or Q obey the same identities; on the empty
scheme all maps are unique. The normalization for the supplied monoidal
structure, rather than exactness for an unspecified shift, is essential here. -/
theorem exists_derivedPullback_kFlat_cone_counit_normalization
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z),
        (∀ P : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
        ∀ (P Q : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          CochainComplex.IsKFlat (R := Y.sheaf) Q →
          let C := CochainComplex.mappingCone.triangleh p
          let T := (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y).mapTriangle.obj C
          let W := ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).mapTriangle.obj C
          ε.app C.obj₃ ≫ W.mor₃ =
            (derivedPullback f).map T.mor₃ ≫
              ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
                asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                  ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
                tensorIso e (Iso.refl _) ≪≫
                schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom ≫
                  (ε.app C.obj₁)⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
