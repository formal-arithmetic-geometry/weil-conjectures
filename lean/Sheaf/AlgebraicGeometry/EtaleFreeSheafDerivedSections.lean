/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# Free sheaves and derived global sections

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI,
combined with the free-sheaf sections adjunction.
(blueprint: lem-weil-pbc-free-sheaf-derived-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Shifted maps from the free module sheaf on the terminal etale object compute derived
module global sections, naturally in the coefficient sheaf. No compactness, separation,
or torsion hypothesis is needed.

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI; the
identification with derived functors in lem-sp-derived-functor-single-identification.
(blueprint: lem-weil-pbc-free-sheaf-derived-sections).

Proof: For each module sheaf F choose an injective resolution F -> I in degrees >= 0.
The resolution is K-injective. Thus maps from the degree-zero free sheaf to F[q] in
D+ are degree-q cohomology classes of the Hom complex from the degree-zero free sheaf
into I. In every degree, the free-sheaf sections equivalence identifies this Hom
complex with the underlying abelian complex of I evaluated at the terminal object.
The equivalence is additive and commutes with differentials, by naturality of
freeSheafHomEquiv_comp. Evaluation at a terminal object is naturally isomorphic to
module global sections, so the latter complex is the underlying abelian complex of
Gamma(I). The exact forgetful functor from modules to abelian groups preserves
homology. By K-injectivity Gamma(I) computes derived global sections of F[0].
Taking homology gives the required component isomorphism. For a morphism F -> G,
lift it to the injective resolutions; the free-sheaf sections equivalence commutes
with this lift term by term. The induced cohomology maps therefore agree. Lifts are
unique up to homotopy, making the comparison natural and independent of choices.
The bounded-below inclusion is fully faithful, so its Hom computation agrees with
that in the unbounded derived category used on the right. This includes q = 0,
the zero coefficient ring, and the empty scheme. -/
theorem nonempty_freeSheafDerivedSectionsIso (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (q : ℕ) :
    Nonempty
      ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ (q : ℤ) ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.freeSheaf Λ Z).obj
              (MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))))))) ≅
        (DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
          Etale.cohomology (ModuleCat.{u + 1} Λ) Z (q : ℤ) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by sorry

end AlgebraicGeometry.Scheme
