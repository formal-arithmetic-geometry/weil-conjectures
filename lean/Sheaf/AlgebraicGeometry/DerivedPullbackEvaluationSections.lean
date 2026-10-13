/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison

/-! # Sections of the normalized pointwise pullback evaluation

Source: Stacks Project, Cohomology, Tags 08I3, 079W, 08DJ and 08JA.
(blueprint: lem-pc-derived-pullback-evaluation-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The pointwise transpose of pulled-back evaluation respects the canonical
identification of zeroth hypercohomology with derived morphisms.
This is a statement about elements, with no bifunctorial mate and no counit composite.

Source: Stacks Project, Cohomology, Remark 08I3, Lemma 079W, Lemma 08DJ and Tag 08JA.
(blueprint: lem-pc-derived-pullback-evaluation-sections).

Proof:
1. Extract the termwise tensor pullback and its left-derived comparison from the
   given monoidal model. Derive its underived pullback/direct-image adjunction on
   K-flat source and K-injective target complexes. Transport the left side by the
   model's left-derived comparison. This supplies a, normalized to that comparison.
2. Compute direct image and global sections on K-injective resolutions. Sections
   of direct image are sections on the source, giving z after zeroth cohomology.
   Identify H0 of the Hom complex with chain maps modulo homotopies, then with
   derived morphisms into the fixed K-injective resolution. These give eS and eT;
   composition of representatives proves both displayed naturality identities.
3. Resolve K and L by K-flat complexes and the target by the fixed K-injective
   resolution. The canonical tensor-Hom predicates identify evaluation with
   componentwise uncurrying. The monoidal-model predicate identifies its tensorator
   with termwise pullback on every total-tensor summand. Transposing evaluation
   after this tensorator and taking its adjoint therefore sends a degree-zero
   Hom cocycle phi to its termwise pullback. The z comparison removes direct image
   without changing that cocycle. Passing to homotopy classes gives the last
   identity. Common resolutions transport this identity to arbitrary K and L.
   No invertibility of an internal-Hom/counit composite is used. For an identity
   morphism the computation is the identity on cocycles; for zero objects or the
   empty scheme both sides are the zero morphism. -/
theorem exists_derivedPullback_evaluation_sections
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal) (hm : IsDerivedPullbackMonoidalModel g m)
    (qS : ∀ A K L : schemeDerivedCategory S,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology S)
        S.toRingedSpace.sheaf).obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hqS : IsCanonicalDerivedTensorHom S qS)
    (qT : ∀ A K L : schemeDerivedCategory T,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology T)
        T.toRingedSpace.sheaf).obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hqT : IsCanonicalDerivedTensorHom T qT) :
    ∃ (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (z : schemeDerivedDirectImage g ⋙
          ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf ≅
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)
      (eS : ∀ P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P)),
        eS P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P)),
        eT P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ (K L : schemeDerivedCategory S)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))),
        eT (op ((derivedPullback g).obj K), (derivedPullback g).obj L)
          ((z.hom.app
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).obj
                  (op ((derivedPullback g).obj K), (derivedPullback g).obj L)))
            ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).map
              (a.homEquiv _ _
                ((qT _ ((derivedPullback g).obj K) ((derivedPullback g).obj L)).symm
                  ((m.μIso _ K).hom ≫
                    (derivedPullback g).map (qS _ K L (𝟙 _))))) x)) =
          (derivedPullback g).map (eS (op K, L) x)) := by sorry

end AlgebraicGeometry
