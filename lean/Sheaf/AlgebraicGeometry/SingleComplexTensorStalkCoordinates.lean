/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance

/-! # Coordinates for the tensor of a single-complex stalk comparison

Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation of equation-bc.
(blueprint: lem-pc-single-complex-tensor-stalk-coordinates).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Identify the canonical tensor comparison, in any output coordinates, with the
localized mixed-ring comparison of two A-K-flat complexes. This is a comparison-map
identity, without any isomorphism hypothesis on the input comparison.

Source: Stacks Project, perfect.tex, Tag 0DJA(1), the local computation using 0BYJ.
(blueprint: lem-pc-single-complex-tensor-stalk-coordinates).

Proof: choose K-flat representatives of E and K and a K-injective representative of K',
and lift phi through the pullback counit to a chain map, as in nonempty_coordinates.
The stalks of the first two representatives are K-flat over A: exactness of stalks and
termwise skyscraper complexes test tensor-acyclicity locally. The degreewise pullback-stalk
isomorphism identifies the stalk of the lifted map with t below. Stalks commute with
coproducts, so their degreewise tensor isomorphisms totalize to identify the stalk of
E tensor K with the total tensor of these two stalk complexes. Scalar extension has
the pinned tensor comparison gamma on every summand. The canonical predicate for tau
identifies the derived map with this chain comparison followed by 1 tensor t. The
canonical tensor-to-stalk map makes C a localization of A tensor_R B, hence flat.
The counit and action equations of the cohomology models identify the source
comparison after scalar extension with the model M's comparison. These equations are
natural for chain maps and invert quasi-isomorphisms between K-flat representatives;
a common K-flat resolution compares the constructed output coordinates with c.
Their representative isomorphisms and localization maps give a and b below, and
naturality gives the displayed identity. All isomorphisms concern representatives,
not the comparison itself; no assumption that the comparison is invertible is used. -/
theorem singleComplex_tensor_stalk_coordinates
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g').obj (E ⊗ K) ⟶
        (derivedPullback g').obj E ⊗ (derivedPullback g').obj K)
    (hτ : IsCanonicalPullbackTensorComparison g' τ)
    (E K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (c : Coordinates g' (E.obj ⊗ K.obj)
      ((derivedPullback g').obj E.obj ⊗ K'.obj)
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ))) (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    let J := ModuleCat.localizedTensorExtension (R f g' z) (A g' z) (B f' z) (C z)
    ∃ d : Coordinates g' K.obj K'.obj φ,
      ∃ Q : CochainComplex (ModuleCat.{u} (A g' z)) ℤ,
        let P := stalkComplex g' z d.P
        let N := ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).obj d.N
        let t : J.obj P ⟶ N := (tensorStalkIso f f' g g' sq z d.P).hom ≫
          ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
            (.up ℤ)).map d.t
        Module.Flat ((A g' z) ⊗[R f g' z] (B f' z)) (C z) ∧
        (∀ V : CochainComplex (ModuleCat.{u} (A g' z)) ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor Q V (curriedTensor _)).Acyclic) ∧
        (∀ V : CochainComplex (ModuleCat.{u} (A g' z)) ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor P V (curriedTensor _)).Acyclic) ∧
        ∃ γ : J.obj (CochainComplex.mapBifunctor Q P (curriedTensor _)) ≅
            CochainComplex.mapBifunctor (J.obj Q) (J.obj P) (curriedTensor _),
          ModuleCat.IsLocalizedTensorComparison (R f g' z) (A g' z) (B f' z) (C z) Q P γ ∧
          let M := ModuleCat.baseDerivedTensorCohomologyModel
            (R f g' z) (A g' z) (B f' z)
            (CochainComplex.mapBifunctor Q P (curriedTensor _)) (C z)
          ∀ i : ℤ,
            ∃ a : (ModuleCat.extendScalars (tensorMap f f' g g' sq z)).obj
                ((cohomologyModel f f' g g' sq z c.P).cohomology i) ≅
              (ModuleCat.extendScalars (tensorMap f f' g g' sq z)).obj (M.cohomology i),
            ∃ b : (CochainComplex.mapBifunctor (J.obj Q) N (curriedTensor _)).homology i ≅
              (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
                (.up ℤ)).obj c.N).homology i,
              stalkComparison f f' g g' sq c z i = a.hom ≫
                ModuleCat.localizedTensorComparison (R f g' z) (A g' z) (B f' z) (C z) M
                  (γ.hom ≫ HomologicalComplex.mapBifunctorMap (𝟙 _) t
                    (curriedTensor _) (.up ℤ)) i ≫ b.hom := by
  sorry

end AlgebraicGeometry.SingleComplexBaseChange
