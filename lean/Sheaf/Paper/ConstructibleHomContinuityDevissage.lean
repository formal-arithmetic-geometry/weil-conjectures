/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Devissage for continuity of derived Hom

Source: blueprint main-20261015, sec-six-functors-basics/
sk-lem-constructible-ext-continuity/sk-lem-constructible-ext-continuity-devissage.md
(blueprint: det-lem-constructible-ext-continuity-devissage).

The comparison is built from the actual cocone by the abelian-group colimit universal
property. The formal assertion imposes no boundedness condition. The final assertion uses
finite constant-model constructibility and the specified two field coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v t a

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The canonical additive comparison, sending a stage morphism h to h followed by the
shifted cocone map. Source: blueprint devissage statement, displayed theta formula
(blueprint: det-lem-constructible-ext-continuity-devissage). -/
def homContinuityComparison {T : Type t} [Category.{v} T] [Preadditive T]
    [HasShift T ℤ] {I : Type v} [SmallCategory I] (D : I ⥤ T) (c : Cocone D)
    (C : T) (q : ℤ) :
    colimit (D ⋙ shiftFunctor T q ⋙ preadditiveCoyoneda.obj (op C)) ⟶
      (preadditiveCoyoneda.obj (op C)).obj (c.pt⟦q⟧) :=
  colimit.desc _ (((shiftFunctor T q) ⋙ preadditiveCoyoneda.obj (op C)).mapCocone c)

/-- The class defined by bijectivity of the canonical comparison in every integer degree.
Source: blueprint devissage statement, definition of C
(blueprint: det-lem-constructible-ext-continuity-devissage). -/
def homContinuityLocus {T : Type t} [Category.{v} T] [Preadditive T]
    [HasShift T ℤ] {I : Type v} [SmallCategory I] (D : I ⥤ T) (c : Cocone D) :
    ObjectProperty T :=
  fun C ↦ ∀ q : ℤ, Function.Bijective (homContinuityComparison D c C q)

/-- Apply the comparison to the images of a diagram of complexes and its termwise
colimit under the ordinary derived localization Q. This is not a derived-category colimit.
Source: blueprint devissage statement, first paragraph and theta formula
(blueprint: det-lem-constructible-ext-continuity-devissage). -/
def complexHomContinuityLocus (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{t} A] {I : Type t} [SmallCategory I]
    (D : I ⥤ CochainComplex A ℤ) [HasColimit D] : ObjectProperty (DerivedCategory A) :=
  homContinuityLocus (D ⋙ DerivedCategory.Q)
    (DerivedCategory.Q.mapCocone (colimit.cocone D))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Hom continuity is closed under shifts, isomorphisms, extensions, and any finite
construction from a supplied collection. Source: blueprint devissage statement, formal
assertion (blueprint: det-lem-constructible-ext-continuity-devissage).

Proof:
1. Associativity and cocone compatibility make the postcomposition maps an additive
cocone, giving theta by def-weil-pbc-category-colimit. The shift equivalence identifies
theta for C[n] in degree q with theta for C in degree q-n. Precomposition with an
isomorphism and its inverse proves isomorphism invariance. Hom out of zero is zero.
2. For a distinguished triangle C' -> C -> C'' -> C'[1], apply Hom(-,W) to obtain
Hom(C'[1],W) -> Hom(C'',W) -> Hom(C,W) -> Hom(C',W) -> Hom(C''[-1],W).
Exactness at the three middle terms follows from lem-weil-pbc-hom-out-of-triangle-exact
and its application to the inverse rotation. TR2 makes that inverse rotation distinguished;
lem-weil-pbc-hom-into-triangle-exact gives the zero composites.
3. Set W=K_i[q] and W=K[q]. Precomposition commutes with postcomposition, including the
negative inverse-rotation arrow. Thus theta gives a commutative ladder. The first row stays
exact under the filtered abelian-group colimit by
lem-weil-pbc-filtered-colimit-abelian-groups-exact; the target row is exact directly.
4. Shift closure and the endpoint assumptions make the four outer vertical maps
isomorphisms. Apply lem-weil-pbc-five-lemma to obtain bijectivity of the middle map in
every degree.
5. Induct on the finite extension construction from G. The shift closure includes
isomorphic shifted generators, and extensionProductIter expresses finite iterated
extensions. Arbitrarily placed shifts and isomorphisms can be moved through distinguished
triangles, so this expresses all finite constructions in the statement. Cone closure also
follows by rotating a triangle and using shift and extension closure. -/
theorem constructibleHomContinuity_devissage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u})
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [HasColimit D] :
    (∀ (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (n : ℤ), complexHomContinuityLocus _ D C →
        complexHomContinuityLocus _ D (C⟦n⟧)) ∧
    (∀ (C B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (_ : C ≅ B), complexHomContinuityLocus _ D C → complexHomContinuityLocus _ D B) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → complexHomContinuityLocus _ D T.obj₁ →
        complexHomContinuityLocus _ D T.obj₃ → complexHomContinuityLocus _ D T.obj₂) ∧
    (∀ G : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      G ≤ complexHomContinuityLocus _ D → ∀ n : ℕ,
        (G.shiftClosure ℤ).extensionProductIter n ≤ complexHomContinuityLocus _ D) := by
  sorry

/-- The constructible specialization for finite E and the finite-subextension condensed
algebraic closure. Source: blueprint devissage statement, last paragraph
(blueprint: det-lem-constructible-ext-continuity-devissage).

Proof: apply det-cor-coefficient-heart-ii-generation to the Noetherian scheme and the
specified field coefficient. Every bounded constant-model constructible complex has a
finite witness using shifted a_!L and cones between earlier entries. The factorization
through the closure of a stratum is among the open-then-closed factorizations quantified
here, and lisse means locally finite free, exactly IsLisseCoefficientModule. The hypothesis
puts every unshifted generator in the continuity locus. Step 1 of the formal devissage
puts its shifts and isomorphic replacements there. Rotate a cone triangle; its middle
object is an extension of the target by the shifted source, so steps 2--4 put the cone
there. Induction along the finite witness proves the conclusion. Empty schemes, rank
zero, and the zero complex are included. No identification with arbitrary local matrix
presentations and no boundedness condition on the filtered diagram are used. -/
theorem constructibleHomContinuity_of_lisseGenerators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X)) ℤ) [HasColimit D]
    (hG : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) S)),
      IsLisseCoefficientModule (coefficientHeartRingObj Λ) L →
      complexHomContinuityLocus _ D
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
            ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) j).obj L)))) :
    constantModelBoundedConstructible (coefficientHeartRingObj Λ) X ≤
      complexHomContinuityLocus _ D := by
  sorry

end AlgebraicGeometry.ProEtale
