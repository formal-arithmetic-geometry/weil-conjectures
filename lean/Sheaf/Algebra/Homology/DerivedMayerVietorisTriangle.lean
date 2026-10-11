module

public import Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

universe u w

namespace AlgebraicGeometry

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

/-! # Distinguished Mayer–Vietoris triangle from extension by zero

Source: literature/stacks-project/cohomology.tex, Tag 08BU
(blueprint: lem-sc-derived-mayer-vietoris-triangle).
-/

set_option maxHeartbeats 1600000 in
/-- The distinguished Mayer–Vietoris triangle for a two-open cover `X = U ∪ V` of a ringed
space, `j_{UV,!}(E|_{U∩V}) → j_{U,!}(E|_U) ⊞ j_{V,!}(E|_V) → E → j_{UV,!}(E|_{U∩V})[1]`.
Here `j_! = extensionByZeroPresheaf ⋙ sheafification` and restriction is
`SheafOfModules.overFunctor`, made derived by `Functor.mapDerivedCategory`; the counit
`j_!(F|_W) → F` is that of the adjunction of `open_restriction_adjunction_exact`.
For every complex `K` with `e : Q K ≅ E`, the maps are tied to `K`: `fK` is the termwise
difference of the two extension-by-zero restriction maps (characterised by its composites
with the counits: `ε_W` on the `U` factor and `-ε_W` on the `V` factor), the second map is
the pair of counits `biprod.desc ε_U ε_V`, the sequence of complexes is short exact, and
the derived triangle is the image of `Q fK`, `Q (desc ε_U ε_V)` and the boundary
`triangleOfSESδ` under the canonical comparison isomorphisms (`e`,
`mapDerivedCategoryFactors`, `Q.mapBiprod`).

Source: literature/stacks-project/cohomology.tex, Tag 08BU
(blueprint: lem-sc-derived-mayer-vietoris-triangle).

Proof: Choose a representative complex and apply the short exact
Mayer–Vietoris sequence degreewise using `lem-sc-derived-open-mayer-vietoris-ses`.
Apply `DerivedCategory.triangleOfSES_distinguished` to obtain the distinguished
triangle and its boundary morphism. Identify the first and second maps with the
difference and counit maps, using exactness and the derived extension-by-zero
adjunction from `lem-sc-derived-open-shriek-derived-adjunction`.
-/
theorem derived_mayer_vietoris_triangle (X : RingedSpace.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over (U ⊓ V)))]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) :
    ∃ (fK : (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ (((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ⊞ ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))))
      (_ : fK ≫ biprod.fst ≫ ((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              U).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)) = ((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X (U ⊓
              V)).2.2.2.2).counit.app (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X (U ⊓
              V)).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)))
      (_ : fK ≫ biprod.snd ≫ ((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              V).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)) = (-𝟙 _) ≫ ((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X (U ⊓
              V)).2.2.2.2).counit.app (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X (U ⊓
              V)).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)))
      (hz : fK ≫ biprod.desc (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              U).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K))) (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              V).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K))) = 0)
      (hS : (ShortComplex.mk (X₃ := K) fK (biprod.desc (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              U).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K))) (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              V).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)))) hz).ShortExact),
      Triangle.mk
        ((((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory.mapIso
                e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓
                  V)).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).hom ≫ DerivedCategory.Q.map fK ≫
                (DerivedCategory.Q.mapBiprod ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).hom ≫
          biprod.map (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.mapIso e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).inv (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory.mapIso e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).inv :
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory.obj E)) ⟶
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj E)) ⊞
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory.obj E)))
        (biprod.map (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.mapIso e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).hom (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory.mapIso e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).hom ≫ (DerivedCategory.Q.mapBiprod
                ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).inv ≫
          DerivedCategory.Q.map (biprod.desc (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              U).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K))) (((HomologicalComplex.Hom.mk
          (fun i => (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2).counit.app
              (K.X i))
          (fun i j _ => ((Classical.choice (open_restriction_adjunction_exact X
              V).2.2.2.2).counit.naturality (K.d i j)).symm) :
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2)))
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ⟶ K)))) ≫ e.hom :
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj E)) ⊞
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X V).2.2.2.2))
          (open_restriction_adjunction_exact X V).2.2.1
          (open_restriction_adjunction_exact X V).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory.obj E)) ⟶ E)
        (e.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ ((((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).mapIso
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory.mapIso
                e.symm ≪≫
              (SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓
                  V)).mapDerivedCategoryFactors.app K) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).app
            (((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))).inv)⟦(1 : ℤ)⟧' :
          E ⟶ (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2))
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.1
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.1).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory.obj
                E)))⟦(1 : ℤ)⟧) ∈ distTriang _ := by
  sorry

end AlgebraicGeometry
