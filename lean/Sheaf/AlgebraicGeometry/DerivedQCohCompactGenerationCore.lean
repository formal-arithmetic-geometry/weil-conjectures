module

public import Sheaf.AlgebraicGeometry.PerfectLocalizingClosure
public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Perfect representatives detect zero

Source: Stacks Project, Tag 09IS, and the orthogonal-class argument in
lem-pc-derived-qcoh-compact-generation.
(blueprint: lem-pc-derived-qcoh-representatives-generate).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A family representing every perfect object weakly generates whenever perfect objects
have the whole category as their localizing closure. No compactness is asserted here.
Source: Stacks Project, Tag 09IS; the orthogonal-class reduction in the proof of
lem-pc-derived-qcoh-compact-generation.
(blueprint: lem-pc-derived-qcoh-representatives-generate).

Proof: Suppose every map from the coproduct of P into every shift of K is zero.
A map from a single P i extends to the coproduct by using zero on the other summands,
so every map from P i into every shift of K vanishes. By the representative isomorphisms,
the same holds for every perfect object. Shift adjunction transfers this to vanishing
of maps from every shift of a perfect object into K. In the ambient derived category,
let A consist of quasi-coherent objects whose every shift has only zero maps into K.obj.
This property is invariant under isomorphisms and shifts. It is closed under retracts
by composing with the inclusion and projection. For an ambient distinguished triangle
with first two terms in A, exactness of Hom into K.obj makes every map from a shift of
the third term factor through a shift of the first term, so it is zero. For an ambient
coproduct of objects in A, shifts preserve its universal property, and a map into K.obj
is zero because its restrictions to all summands are zero. Thus A is one of the
properties defining perfectLocalizingClosure X. The assumed equality with top implies
K lies in A. Taking its identity in shift zero shows that K.obj is zero. Fullness of the
inclusion then implies K is zero in the full subcategory. Contraposition gives the weak
generator condition. For an empty family, the representative hypothesis and closure
assumption force the category to be zero, and the same argument applies. -/
theorem schemeDerivedQCoh_representatives_generate (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (htri : (schemeDerivedQCohProperty X).IsTriangulated)
    {I : Type u} (P : I → schemeDerivedQCohCategory X)
    (hrepresentatives : ∀ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj →
      ∃ i : I, Nonempty (E ≅ P i))
    (hclosure : perfectLocalizingClosure X =
      (⊤ : ObjectProperty (schemeDerivedQCohCategory X))) :
    letI := htri
    letI := derivedQCohDirectSums X
    IsTriangulatedGeneratingFamily P := by
  sorry

end AlgebraicGeometry
