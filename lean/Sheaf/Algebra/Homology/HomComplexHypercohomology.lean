/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology
public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Hypercohomology of a sheaf Hom complex with K-injective target

Source: Stacks Project, Tags 08JA, 0A95, and 0A96.
(blueprint: lem-pur-hom-complex-hypercohomology)
-/

@[expose] public section

universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Zeroth hypercohomology of the sheaf Hom complex into K-injectives computes
homotopy classes, naturally in the source and in any functorial K-injective target.

Source: Stacks Project, Lemma 08JA, using Lemmas 0A95 and 0A96.
(blueprint: lem-pur-hom-complex-hypercohomology)

Proof: first suppose the source L is K-flat. The sheaf Hom complex Hom(L,I(M))
is K-injective by Lemma 0A96. The comparison for the right derived global sections
functor therefore computes its hypercohomology by applying Hom(O,-) termwise.
The global-cochain comparison identifies this complex with the ordinary Hom
complex of L and I(M), compatibly with differentials. Its degree-zero cycles
are chain maps and its boundaries are null-homotopic maps; Mathlib's Hom-complex
cohomology comparison identifies H0 with morphisms in the homotopy category.
For arbitrary L choose a K-flat resolution K -> L (Lemma 06YS). Lemma 0A95
makes Hom(L,I(M)) -> Hom(K,I(M)) a quasi-isomorphism. Precomposition by K -> L
also gives a bijection of homotopy classes into I(M), by K-injectivity. Transport
the preceding comparison across these two isomorphisms. Choose the K-flat
augmentations degreewise surjective, as in Lemma 06YS.
For two such resolutions of L their fibre product maps quasi-isomorphically
to both: its projection kernels are the acyclic kernels of the augmentations.
Resolve that fibre product again by Lemma 06YS. Naturality of the K-flat
comparison for the resulting maps proves independence of the resolution.
For a source map L' -> L, pull back a surjective resolution of L to L' and
resolve that pullback. Its map to L' is a quasi-isomorphism, and its map to the
resolution of L yields the naturality square between K-flat sources. Transport
this square back to L and L'. The product-projection map formula makes the
global-cochain comparison commute with pre- and postcomposition; quotienting
by homotopy does too. Postcomposition by I(f) also commutes with the transport.
This proves naturality in both variables. All maps are additive. Products in
the Hom complex allow unbounded L.
For L=0 or I(M)=0 both sides are zero, so no nonzero or boundedness hypothesis
is needed. This theorem computes a complex-level Hom object, and does not use
derived internal Hom or the desired derived-category identification. -/
theorem homComplex_hypercohomology
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hI : ∀ M, (I.obj M).IsKInjective) :
    Nonempty (((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q ⋙ ringedSiteZerothHypercohomology J R) ≅
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).op).prod
          (I ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda) := by sorry

end CategoryTheory
