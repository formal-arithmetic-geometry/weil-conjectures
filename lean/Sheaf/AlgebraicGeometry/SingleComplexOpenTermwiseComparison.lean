/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso

/-! # The normalized comparison on a termwise restricted complex

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-termwise-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange

set_option synthInstance.maxSize 2048

/-- Open restriction transports the normalized tensor comparison on the literal
termwise restriction of the source complex. There is no independently chosen
restricted representative or representing isomorphism.

Proof: put U = f⁻¹V and U' = f'⁻¹V'. The open stalk maps identify the four
local rings with their unrestricted counterparts. The identities stalkMap_comp,
hj, and the restricted cartesian square identify every structure map and the
map from the tensor algebra to the last stalk ring. Restrict P degreewise.
Restriction is tensor pullback along the open immersion and preserves K-flatness.
The universal derived counit is invertible on this K-flat complex; uniqueness of
the left-derived functor transfers that property to the pinned counit hcP0.
The restriction-stalk isomorphism identifies its stalk complex with the
original stalk complex after extension along the open stalk-ring isomorphism.
Transport the universal left-derived scalar extension through these exact ring
equivalences. Its counit-compatible uniqueness identifies the derived tensor
cohomology objects; naturality of multiplication and cohomologyIso_smul make
this identification linear over the identified tensor algebra. Extension to
the last stalk ring gives the source isomorphism l. The natural isomorphism ν is
openDerivedAdditiveStalkIso, constructed from exact restriction and
restrictStalkNatIso by localization and cohomology.
The comparison_eq and localized_eq equations express both comparison maps
by the same transported scalar-extension counit. The factorization identity
for leftDerivedUnique in singleComplexOpenPullbackIso and the pinned composition
comparisons identify the map to restricted derived pullback with the displayed
restricted identity coefficient. Apply cohomology to obtain the stated square.
The representing isomorphism a is the localization factor of actual termwise
restriction; no comparison of arbitrary representatives is part of this lemma.
For empty opens there is no z; top opens, zero complexes and zero rings use
exactly the same isomorphisms. No base flatness or bounds are needed.

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-termwise-comparison). -/
theorem exists_singleComplexOpen_termwise_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let a : DerivedCategory.Q.obj Q ≅
        (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K :=
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactors.symm.app P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (_hP₀ : CochainComplex.IsKFlat (R := (f ⁻¹ᵁ V).toScheme.sheaf) Q),
    ∃ (hcP₀ : IsIso ((counit j).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcP₀ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcP₀ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i) := by sorry


end AlgebraicGeometry
