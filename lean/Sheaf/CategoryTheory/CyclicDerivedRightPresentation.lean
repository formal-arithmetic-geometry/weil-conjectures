/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.CategoryTheory.CyclicDerivedOffDiagonalPresentation

/-! # Right-derived transport of cyclic presentations

Source: Stacks Project, Derived Categories, Tags 070I, 070K, 070Y and 0152;
the right-derived companion proof plan in CyclicDerivedHomExactSequence.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L]
  (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (hC : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ]
  (hσ : NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ)

include hσ in
/-- Right derivation preserves a strict cyclic presentation after replacing its models.

Proof: replace M and N[-1] by K-injective complexes with injective terms, and represent
the underlying morphism by a chain map, using exact forgetting and the K-injective Hom
bijection. Form its triangular extension A → E → J. Since A has injective terms, the
sequence splits in each degree in the fixed-pair category. Hence E and the cone of the
inclusion are K-injective: the degreewise split sequence gives a distinguished homotopy
triangle, and K-injectives form a triangulated subcategory. The cone projection to J is
a quasi-isomorphism between K-injectives, hence a homotopy equivalence. The uniqueness
of strict presentations identifies the original native morphism with this extension's
connecting morphism. Compute the right derived equivariant functor by its unit on these
models. Additivity preserves the degreewise splitting, cones and the homotopy inverse.
Thus the canonical signed formula for the SES connecting morphism, minus the cone
projection inverse followed by the shifted inclusion projection, is preserved. The
unit-normalized forgetting comparison and hσ identify the transported underlying class.
Naturality of e makes the image upper action entry exactly the target diagonal action
composed with P' of the image chain map. The image sequence, splitting, chain map and
endpoint isomorphisms therefore give the required strict presentation. This argument
uses no boundedness of either endpoint and no normalization predicate on a boundary.

Source: the K-injective and cone steps of the parent right-derived companion; Stacks
derived.tex, Tags 070I, 070K, 070Y and 0152, and injectives.tex, Tag 079P.
(blueprint: lem-sf-cyclic-derived-right-presentation). -/
theorem cyclicDerivedOffDiagonalPresentation_mapRightDerived
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)}
    {f : M ⟶ N} (hp : CyclicDerivedOffDiagonalPresentation F u f) :
    CyclicDerivedOffDiagonalPresentation G
      (cyclicDerivedHomTransport F G
        ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
        (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
        (cyclicDerivedRightForgetComparison F G L e hF hC) M N (-1) u)
      (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).map f) := by sorry

end CategoryTheory.Endofunctor.IsoAlgebra
