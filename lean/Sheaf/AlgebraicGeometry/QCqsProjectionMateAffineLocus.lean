/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract

/-! # Closure of the affine projection-mate locus

Source: Stacks Project, Tag 08EU.
(blueprint: lem-pc-qcqs-projection-mate-affine-locus).
-/

@[expose] public section

universe u w wA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
  (X : Scheme.{u})
  [CompactSpace X] [QuasiSeparatedSpace X]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
  (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
  (t : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback f ≅
    (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
  (L : schemeDerivedQCohCategory X)
  (e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)))

/-- The all-shifts isomorphism locus of the supplied projection mate is closed
under coproducts, distinguished triangles, and retracts.

Proof: the mate is natural in M by naturality of t and the counit and of the
adjunction Hom equivalence. The two functors in M are exact. On quasi-coherent
objects they preserve coproducts: e is an equivalence, pullback is a left
adjoint, tensor preserves coproducts, and qcqs direct image preserves
quasi-coherent coproducts. The quasi-coherent inclusion preserves these sums.
Shifts preserve coproducts, so a component on a sum is a sum of invertible
components. For a distinguished triangle use every shift of the triangle.
Apply Hom(T,-) to the two image sequences, for each ambient T. Naturality at
the three maps, including the connecting map, gives a diagram of exact
sequences. The five lemma makes the third component invertible when the
first two are invertible; use Yoneda and then every shift. No compatibility
of t with a chosen shift comparison is required: the sequences have vertices
F(K[n]) and the arrows obtained by applying F to the shifted triangle maps.
Naturality transports an isomorphism component along an object isomorphism
and along a retract. The predicate quantifies over all object isomorphisms,
so it is invariant under isomorphism by composition. The zero object and
empty coproduct are included.
Source: Stacks Project, Tag 08EU.
(blueprint: lem-pc-qcqs-projection-mate-affine-locus). -/
theorem qcqsProjectionMate_affineLocus_closed
    (htri : ∃ (_h : (e.functor ⋙
      (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
      (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated) :
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦
    ∀ (M : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ),
      Nonempty ((e.functor.obj (K⟦n⟧)).obj ≅ M.obj) →
      IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
          (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
            (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)));
    (∀ {I : Type u} (F : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, F i ⟶ S),
      IsColimit (Cofan.mk S ι) → (∀ i, P (F i)) → P S) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
    (∀ {K N : DerivedCategory (ModuleCat.{u} A)}, Retract K N → P N → P K) := by sorry

end AlgebraicGeometry
