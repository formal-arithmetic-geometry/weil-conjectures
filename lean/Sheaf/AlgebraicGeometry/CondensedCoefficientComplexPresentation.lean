/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Limits.Final

/-! # Complex presentations of condensed coefficient extension

This is the coefficient algebra step of derived Hom descent. It makes no
constructibility assumption on either the source or the target of a morphism.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

/-- Source: archived master `ModuleObject/Colimit/TwoColimit.lean`, the Hom paragraph
of the module docstring; the coefficient complex construction in step 3 of
`prop-weil-pbc-qbar-condensed-two-colimit`.
(blueprint: lem-weil-pbc-condensed-coefficient-complex-presentation)

Proof: represent the bounded-below object `L` by a complex `C` zero below an integer
`a`, using the standard derived t-structure. At index `i`, extend `C` termwise from
`F` to `H.obj i`, then restrict the resulting complex to `E`. A transition map is
induced by the coefficient inclusion, tensor the identity of `C`; its `E`-linearity
follows from the equality of the two coefficient inclusions. Tensor functoriality
proves identities, composition, and the cocone equations. The vertex is the same
construction with the finite-subfield-valued condensed algebraic closure.

The finite coefficient rings have this closure as their colimit, also after the
final functor `H` and after pullback to the scheme. Balanced tensor preserves this
colimit: write it as the coequalizer of the two action maps, use preservation by
ordinary tensor, and commute colimits. Forgetting the `E` action creates colimits,
so this gives the module colimit in every degree. Colimits of complexes are
computed degreewise, giving `IsColimit c`. All terms below `a` are zero because
extension and restriction are additive.

Exactness of these coefficient extensions identifies the total derived functors
with the termwise functors. Together with the representative isomorphism for `L`
this gives `eΩ` and every `ei`. For the displayed equation, first check the
underived extension/restriction adjunction: both sides take a section `m` to
`1 ⊗ m` followed by the same coefficient inclusion and tensor multiplication.
This is an equality of natural transformations of complexes, not a choice of
bijections. Localize it and use the defining factorization equations of
`leftDerivedFunctorCompIso` and `leftDerivedFunctorNatIso`; the resulting
comparisons are precisely `finiteCoefficientDerivedTensorCompIso`. Naturality
then gives the equation for every derived `K` and every `g`.

Edge cases: the zero complex and the empty scheme give zero cocones; no
nonzero-source or bounded-above hypothesis is used. -/
theorem exists_condensed_coefficient_complex_presentation
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : FiniteIntermediateField ℓ)
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (hL : DerivedCategory.TStructure.t.plus L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ FiniteIntermediateField ℓ) [H.Final]
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    ∃ N : I ⥤ CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ,
      ∃ c : Cocone N, Nonempty (IsColimit c) ∧
      (∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)) ∧
      ∃ eΩ : DerivedCategory.Q.obj c.pt ≅
          (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
            ((finiteCoefficientDerivedToAlgCl X ℓ F).obj L),
        ∃ ei : ∀ i : I, DerivedCategory.Q.obj (N.obj i) ≅
            (finiteCoefficientDerivedRestriction X ℓ (he i)).obj
              ((finiteCoefficientDerivedExtension X ℓ (hf i)).obj L),
          ∀ (i : I) (K : DerivedCategory
              (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
            (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
            finiteCoefficientDerivedAlgClHomEquiv X ℓ E K _
              ((finiteCoefficientDerivedTensorCompIso X ℓ (he i)).inv.app K ≫
                (finiteCoefficientDerivedToAlgCl X ℓ (H.obj i)).map
                    ((finiteCoefficientDerivedHomEquiv X ℓ (he i) K _).symm
                        (g ≫ (ei i).hom)) ≫
                  (finiteCoefficientDerivedTensorCompIso X ℓ (hf i)).hom.app L) =
              g ≫ DerivedCategory.Q.map (c.ι.app i) ≫ eΩ.hom := by
  sorry

end AlgebraicGeometry.ProEtale
