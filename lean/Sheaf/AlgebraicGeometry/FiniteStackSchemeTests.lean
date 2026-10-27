module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Scheme tests for finite morphisms and finite-type DM stacks

Source: Stacks, Morphisms of Stacks, representable morphism conventions,
definition-locally-finite-type and definition-quasi-compact; Algebraic Stacks,
representable diagonal convention (blueprint: def-sfb-finite-stack-scheme-tests).

All equivalences retain the projections. Finiteness of a diagonal is tested over
products of two test schemes, rather than on the two projections separately.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A finite map of fibred groupoids is represented after every scheme test by a
finite scheme over that same test, with the actual first projection identified.
Source: Stacks, representable finite morphism convention; Morphisms of Spaces,
Tag 03ZP (blueprint: def-sfb-finite-stack-scheme-tests). -/
def IsRepresentableFiniteModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : Over S) (p : Z ⟶ T), IsFinite p.left ∧
      ∃ e : BasedFunctor (discreteModuli (yoneda.obj Z)) (moduliTwoFiberProduct t f),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t f))
            (discreteModuliMap (yoneda.map p)))

/-- Finite diagonal: each two-scheme test is a scheme finite over their product.
Both projections of the representing equivalence are identified over the base;
the second comparison is written on total functors, with its identity-base condition.
Source: Stacks, diagonal scheme tests and Morphisms of Spaces, Tag 03ZP
(blueprint: def-sfb-finite-stack-scheme-tests). -/
def HasFiniteModuliDiagonal {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∀ (T U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
      (b : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∃ (Z : Over S) (p : Z ⟶ T) (q : Z ⟶ U), IsFinite (prod.lift p q).left ∧
      ∃ e : BasedFunctor (discreteModuli (yoneda.obj Z)) (moduliTwoFiberProduct a b),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
            (discreteModuliMap (yoneda.map p))) ∧
          ∃ η : e.toFunctor ⋙ ObjectProperty.ι _ ⋙ Comma.snd a.toFunctor b.toFunctor ≅
              (discreteModuliMap (yoneda.map q)).toFunctor,
            ∀ x : (discreteModuli (yoneda.obj Z)).obj,
              (discreteModuli (yoneda.obj U)).p.IsHomLift
                (𝟙 ((discreteModuli (yoneda.obj Z)).p.obj x)) (η.hom.app x)

/-- Finite type for a DM stack over an affine base is expressed by a finite-type
surjective étale scheme atlas. The finite-type scheme condition includes quasi-compactness.
No atlas is chosen as data and no property of the geometric stabilizers is imposed.
Source: Stacks, Morphisms of Stacks, definition-locally-finite-type and
quasi-compact atlas criterion (blueprint: def-sfb-finite-stack-scheme-tests). -/
def HasFiniteTypeEtaleModuliAtlas {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p

end CategoryTheory
