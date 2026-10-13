/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Naturality of the source-open comparison with respect to adjunction units

Source: Stacks Project, Tags 08HY and 0D5S, applied to the source-open comparison
of Tag 0DJ9. (blueprint: lem-pc-single-complex-open-unit-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The source-open comparison intertwines restriction units, including its given
coefficient morphism. This is an equality, without any invertibility hypothesis.
Source: Stacks Project, Tag 08HY, adjoint counit description, and Tag 0D5S,
composition of derived pullbacks; the restricted map in Tag 0DJ9.
(blueprint: lem-pc-single-complex-open-unit-naturality).

Proof: Write t = U.ι, p = pullback.fst g' t and v = pullback.snd g' t.
The right-adjoint comparisons k are the mates of the selected pullback
composition isomorphisms c. Transpose the equation under the composite
adjunction for p followed by f'. The definition of k converts transposition
under p ≫ f' into this composite transposition. The unit for p cancels with
its counit by the triangle identity. On the left, expand the counit formula
for base change and the definition of the restricted coefficient morphism.
Naturality of c moves the unit of t past its pullback, and associativity of c
for v,t,f and p,g',f identifies the two ways of composing pullbacks; the
pullback equation v ≫ t = p ≫ g' supplies the intervening equality transport.
The composite-adjunction counit formula for t ≫ f then cancels the unit of t.
The remaining composite on both sides is the transpose of the original
base-change map followed by φ. Naturality of the p-unit moves φ to the right
end. Injectivity of the composite Hom equivalence proves the equality.
All steps are natural transformation identities: zero coefficients, the empty
open and the whole open require no exceptions. -/
theorem singleComplexOpenComparison_unit_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (U : X.Opens) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    let p := pullback.fst g' U.ι
    let k := conjugateIsoEquiv (a (U.ι ≫ f)) ((a f).comp (a U.ι)) (c U.ι f)
    let k' := conjugateIsoEquiv (a (p ≫ f')) ((a f').comp (a p)) (c p f')
    (derivedPullback g).map
        ((schemeDerivedDirectImage f).map ((a U.ι).unit.app K) ≫
          k.inv.app ((derivedPullback U.ι).obj K)) ≫
      singleComplexOpenComparison f f' g g' h K K' φ U =
    (schemeDerivedBaseChangeMap f f' g g' h K ≫
        (schemeDerivedDirectImage f').map φ) ≫
      ((schemeDerivedDirectImage f').map ((a p).unit.app K') ≫
        k'.inv.app ((derivedPullback p).obj K')) := by sorry

end AlgebraicGeometry
