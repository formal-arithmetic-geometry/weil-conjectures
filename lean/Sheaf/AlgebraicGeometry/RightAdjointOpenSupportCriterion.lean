/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Support criterion for restriction of a right adjoint to an open

Source: Stacks Project, Duality for Schemes, Section 48.4, Tag 0E4G,
Lemma 48.4.3, parts (1)--(3)
(blueprint: lem-sc-right-adjoint-open-support-criterion).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the right adjoint is compatible with the open square precisely when
it preserves complexes supported on the closed complements.
Source: Stacks Project, Tag 0E4G, Lemma 48.4.3, parts (1)--(3)
(blueprint: lem-sc-right-adjoint-open-support-criterion).

The isomorphism test uses the first arrow of equation (48.4.1.1), namely the
restriction of `a` applied to the unit `K → Rj_*j^*K`. The remaining two arrows
in that equation are canonical isomorphisms, so this is exactly the test for
invertibility of the entire canonical map to `a_V(j^*K)`, as stated immediately
after that equation. No choice of a map replaces the unit.

Proof:
1. Restriction preserves K-injectives (lem-sc-derived-k-injective-restrict-open).
   Hence restriction commutes with derived direct image. By adjunction this gives
   `a(Rj_*L) ≅ Rj_{U,*}a_V(L)`; restricting kills `Rj_{U,*}`, giving the two
   canonical isomorphisms just described.
2. Use lem-sc-open-restriction-support-triangle to complete the unit to a triangle.
   Its cone is supported on the complement and is bounded below when K is.
   Apply a and restrict: the third term vanishes precisely under the support
   condition. Conversely apply the isomorphism condition to a supported Q, whose
   restriction is zero. The same argument without boundedness proves part (2).
3. If a preserves direct sums, the supported complexes whose image is supported
   form a saturated triangulated subcategory closed under sums and derived colimits.
   By lem-sc-supported-derived-generated-perfect it contains a perfect generator
   (bounded below), hence every supported complex. This proves part (3).
   Restricting the unbounded conditions to bounded-below objects proves the converse.

`hpush` and `hopen` are the proofs needed to lift the shared derived direct image
and the open-unit target into the full quasi-coherent subcategory; they hold for
these qcqs schemes. `adjOpen` is the standard derived open adjunction. -/
theorem rightAdjoint_open_support_criterion
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsCompact (V : Set Y))
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (hpush : ∀ K : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj K.obj))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush ⊣ a)
    (adjOpen : (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
      (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance) ⊣ schemeDerivedDirectImage
          V.ι)
    (hopen : ∀ K : schemeDerivedQCohCategory Y,
      schemeDerivedQCohProperty Y
        ((schemeDerivedDirectImage V.ι).obj ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.overFunctor (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj K.obj))) :
    ((∀ K : schemeDerivedQCohCategory Y,
      (∃ n : ℤ, K.obj.IsGE n) → IsIso ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).map
          ((schemeDerivedQCohProperty X).ι.map
            (a.map (ObjectProperty.homMk
              (X := K)
              (Y := ⟨(schemeDerivedDirectImage V.ι).obj
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
                  (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj K.obj), hopen K⟩)
              (adjOpen.unit.app K.obj)))))) ↔
      (∀ Q : schemeDerivedQCohCategory Y,
      (∃ n : ℤ, Q.obj.IsGE n) →
      IsZero ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj Q.obj) →
      IsZero ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).obj (a.obj Q).obj))) ∧
    ((∀ K : schemeDerivedQCohCategory Y,
      IsIso ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).map
          ((schemeDerivedQCohProperty X).ι.map
            (a.map (ObjectProperty.homMk
              (X := K)
              (Y := ⟨(schemeDerivedDirectImage V.ι).obj
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
                  (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj K.obj), hopen K⟩)
              (adjOpen.unit.app K.obj)))))) ↔
      (∀ Q : schemeDerivedQCohCategory Y,
      IsZero ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj Q.obj) →
      IsZero ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).obj (a.obj Q).obj))) ∧
    ((∀ I : Type u, PreservesColimitsOfShape (Discrete I) a) →
      ((∀ K : schemeDerivedQCohCategory Y,
      (∃ n : ℤ, K.obj.IsGE n) → IsIso ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).map
          ((schemeDerivedQCohProperty X).ι.map
            (a.map (ObjectProperty.homMk
              (X := K)
              (Y := ⟨(schemeDerivedDirectImage V.ι).obj
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
                  (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj K.obj), hopen K⟩)
              (adjOpen.unit.app K.obj)))))) ↔
        (∀ K : schemeDerivedQCohCategory Y,
      IsIso ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))) inferInstance inferInstance).map
          ((schemeDerivedQCohProperty X).ι.map
            (a.map (ObjectProperty.homMk
              (X := K)
              (Y := ⟨(schemeDerivedDirectImage V.ι).obj
                ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (SheafOfModules.overFunctor
                  (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    (Functor.additive_of_preserves_binary_products (SheafOfModules.overFunctor (moduleRings
      Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))) inferInstance inferInstance).obj K.obj), hopen K⟩)
              (adjOpen.unit.app K.obj)))))))) := by
  sorry

end AlgebraicGeometry
