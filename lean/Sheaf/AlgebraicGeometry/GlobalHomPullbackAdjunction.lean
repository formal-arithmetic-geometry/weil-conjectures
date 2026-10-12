/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-!
# Global derived Hom and pullback/direct-image adjunction

Source: Stacks Project, Cohomology, Tags 079W, 08I3 and 0B6A; Duality, Tag 0AA8,
case (1), final compatibility (blueprint: lem-pc-global-hom-pullback-adjunction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- The tensor and derived-unit compatibility equations elaborate many nested functor composites.
/-- The natural global derived Hom adjunction, with its canonical pullback-counit
factorization and its action on zeroth cohomology. The pullback comparison and
adjunction are the shared, normalized constructions. The H⁰ identifications are
fixed by evaluation at 1, K-injective computation and exact scalar restriction.
Source: Stacks Project, Cohomology, Tags 079W, 08I3 and 0B6A; Duality, Tag 0AA8,
case (1), final compatibility (blueprint: lem-pc-global-hom-pullback-adjunction).

Proof, following the node:
1. Apply lem-pc-ringed-spaces-derived-adjoint-general to the ringed-space morphism
   underlying g, obtaining the normalized adjunction and its counit.
2. Apply lem-pc-derived-internal-hom-pullback-adjunction: the evaluation-mate
   pullback comparison followed by postcomposition with the counit is an
   isomorphism of internal Hom objects, natural in both variables.
3. Apply RΓ(S,-), as in def-pc-global-derived-rhom. Two applications of
   lem-pc-ringed-spaces-derived-direct-image-composition identify RΓ(S,Rg_* -)
   with RΓ(T,-) restricted along g.appTop. Restriction of scalars is exact.
   The first factor becomes schemeGlobalDerivedHom_pullback_comparison and
   the second becomes global Hom of the counit.
4. Identify H⁰ with derived Hom using lem-pur-rhom-global-sections on S and T.
   Evaluation at 1 gives bS and bT; K-injective computation gives zS and zT;
   exact scalar restriction gives q. The internal comparison's H⁰ clause gives
   φ ↦ Lg*(φ) followed by the counit, the adjunction bijection. -/
theorem schemeGlobalDerivedHom_pullback_adjunction
    {T S : Scheme.{u}}
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (g : T ⟶ S) :
    ∃ (adj : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (hS : ∀ M N : schemeDerivedCategory S,
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).obj
            ((schemeGlobalDerivedHom S).obj (op M, N))) ≃+ (M ⟶ N))
      (hT : ∀ M N : schemeDerivedCategory T,
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).obj
            (((ModuleCat.restrictScalars.{u}
              (R := (moduleRings S.toRingedSpace).obj.obj (op ⊤))
              (S := (moduleRings T.toRingedSpace).obj.obj (op ⊤))
              g.appTop.hom).mapDerivedCategory).obj
              ((schemeGlobalDerivedHom T).obj (op M, N)))) ≃+ (M ⟶ N))
      (i : (𝟭 (schemeDerivedCategory S)).op.prod (schemeDerivedDirectImage g) ⋙
          schemeGlobalDerivedHom S ≅
        (derivedPullback g).op.prod (𝟭 (schemeDerivedCategory T)) ⋙
          schemeGlobalDerivedHom T ⋙
            (ModuleCat.restrictScalars.{u}
              (R := (moduleRings S.toRingedSpace).obj.obj (op ⊤))
              (S := (moduleRings T.toRingedSpace).obj.obj (op ⊤))
              g.appTop.hom).mapDerivedCategory),
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T),
        i.hom.app (op M, E) =
          schemeGlobalDerivedHom_pullback_comparison g M
            ((schemeDerivedDirectImage g).obj E) ≫
          ((ModuleCat.restrictScalars.{u}
            (R := (moduleRings S.toRingedSpace).obj.obj (op ⊤))
            (S := (moduleRings T.toRingedSpace).obj.obj (op ⊤))
            g.appTop.hom).mapDerivedCategory).map
            ((schemeGlobalDerivedHom T).map
              (((𝟙 ((derivedPullback g).obj M)).op, adj.counit.app E) :
                (op ((derivedPullback g).obj M),
                  (derivedPullback g).obj ((schemeDerivedDirectImage g).obj E)) ⟶
                (op ((derivedPullback g).obj M), E)))) ∧
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T)
        (φ : M ⟶ (schemeDerivedDirectImage g).obj E),
        hT ((derivedPullback g).obj M) E
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).map
              (i.hom.app (op M, E))
                ((hS M ((schemeDerivedDirectImage g).obj E)).symm φ)) =
          (derivedPullback g).map φ ≫ adj.counit.app E) := by
  sorry

end AlgebraicGeometry
