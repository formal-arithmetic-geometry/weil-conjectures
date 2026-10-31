/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed

import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Presentable.Directed

/-!
# The separable generic point as an affine étale inverse limit

Source: literature/stacks-project/etale-cohomology.tex, Tags 04HX and 03QL;
affine pointed-neighbourhood limit and directed reindexing (blueprint:
lem-sf-separable-generic-etale-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- An integral scheme admits an affine étale inverse-limit presentation of the spectrum of
its relative separable generic field. The proof follows Stacks Tags 04HX and 03QL: affine
pointed étale neighbourhoods are made small and cofiltered, their coordinate-ring colimit is
identified with the separable closure, and the affine-spectrum limit is reindexed by a directed
set. (blueprint: lem-sf-separable-generic-etale-presentation)

Proof plan:
1. Choose an affine neighbourhood `Spec A` of the generic point. By
   `lem-sc-integral-function-field-affine-fraction`, its coordinate ring is a domain with
   fraction field `S.functionField`; the prime of the generic point is zero.
2. By `lem-weil-pbc-etale-local-ring-triples`, affine pointed étale neighbourhoods form a
   cofiltered category, and those factoring through `Spec A` are initial. Use
   `lem-weil-pbc-colimit-initial-full-subcategory` and
   `lem-weil-pbc-affine-etale-essentially-small-cover` to choose a small cofiltered
   representative subcategory without changing its coordinate-ring colimit.
3. Apply `lem-weil-pbc-strict-henselization-triples` at the zero prime. The evaluation onto
   the specified relative separable closure is surjective with kernel zero, so it identifies
   that colimit with the field and its coprojections with the residue evaluations.
4. Apply `lem-weil-pbc-spec-small-colimit-limit` to obtain the scheme limit cone. The legs
   compose with the maps to `S` to give the spectrum of the base-field inclusion followed by
   the generic stalk map. Transitions are affine by
   `lem-weil-pbc-morphism-affine-schemes-affine`.
5. Apply `lem-weil-pbc-cofiltered-limit-directed-reindex` in the category of schemes.
   The stages, transitions and legs remain over `S`. The scheme limit is also a limit over
   `S`: compose with one leg, using nonemptiness, to check that the unique lift is over `S`.
-/
theorem exists_separable_generic_etale_presentation {S : Scheme.{u}} [IsIntegral S]
    (Ω : Type u) [Field Ω] [Algebra (S.functionField : Type u) Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic (S.functionField : Type u) Ω] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (D : Iᵒᵈ ⥤ Scheme.{u})
      (v : ∀ i : Iᵒᵈ, D.obj i ⟶ S),
      (∀ i : Iᵒᵈ, IsAffine (D.obj i)) ∧
      (∀ i : Iᵒᵈ, Etale (v i)) ∧
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), D.map f ≫ v j = v i) ∧
      ∃ (c : Cone D) (cS : c.pt ⟶ S) (hc : IsLimit c)
        (g : ∀ i : Iᵒᵈ,
          Spec (.of (separableClosure (S.functionField : Type u) Ω : Type u)) ⟶ D.obj i),
        (∀ {i j : Iᵒᵈ} (f : i ⟶ j), g i ≫ D.map f = g j) ∧
        (∀ i : Iᵒᵈ, c.π.app i ≫ v i = cS) ∧
        (∀ i : Iᵒᵈ,
          g i ≫ v i =
            Spec.map (CommRingCat.ofHom
              (algebraMap (S.functionField : Type u)
                (separableClosure (S.functionField : Type u) Ω : Type u))) ≫
              S.fromSpecStalk (genericPoint S)) ∧
        ∃ e : Spec (.of (separableClosure (S.functionField : Type u) Ω : Type u)) ≅ c.pt,
          (e.hom ≫ cS =
            Spec.map (CommRingCat.ofHom
              (algebraMap (S.functionField : Type u)
                (separableClosure (S.functionField : Type u) Ω : Type u))) ≫
              S.fromSpecStalk (genericPoint S)) ∧
          ∀ i : Iᵒᵈ, e.hom ≫ c.π.app i = g i := by
  sorry

end AlgebraicGeometry
