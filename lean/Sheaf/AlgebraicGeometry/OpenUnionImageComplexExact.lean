/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData

/-! # Exactness of the concrete complex on an arbitrary open union

Source: Stacks Project, Tag 08BV, displayed sequence applied on the union.
(blueprint: lem-pc-open-union-image-complex-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The pair of restrictions from the union and the difference to the overlap
form a short exact sequence for a complex with injective terms.

Source: Stacks Project, Tag 08BV, lemma-exact-sequence-j-star, the displayed
sequence of complexes; Tag 01EB, lemma-mayer-vietoris, its sectionwise proof.
(blueprint: lem-pc-open-union-image-complex-exact).

Proof: In degree n over a test open T, identify the four direct-image terms
with I^n(T intersection (U union V)), I^n(T intersection U),
I^n(T intersection V), and I^n(T intersection U intersection V).
The underived adjunction mate defining each arrow is ordinary restriction:
the nested-restriction comparison identifies iterated restriction, and its
counit cancels the repeated restriction to the larger open. The two iterated
restrictions to the overlap agree, so the pair followed by the difference is
zero. The opens T intersection U and T intersection V cover
T intersection (U union V). Sheaf uniqueness gives injectivity of the first
map; sheaf gluing identifies its image with the kernel of the second map.
Injectivity of I^n makes restriction from T intersection U to the overlap
surjective (injective_restriction_surjective), so pairing a lift with zero
gives surjectivity of the difference. The sectionwise kernel property is
natural in T, hence a kernel in presheaf modules and, by the fully faithful
inclusion, in sheaf modules. Sectionwise injectivity and surjectivity give
monicity and epicity. Evaluation of complexes preserves biproducts; use its
biproduct comparison and HomologicalComplex.shortExact_of_degreewise_shortExact
to conclude. No K-injectivity or derived category is used. Empty opens give
zero summands; repeated opens give the diagonal/difference split sequence. -/
theorem schemeOpenUnionImageComplex_shortExact
    (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    let f := biprod.lift
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
    let g := biprod.desc
      (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
      (-(schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I))
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by sorry

end AlgebraicGeometry
