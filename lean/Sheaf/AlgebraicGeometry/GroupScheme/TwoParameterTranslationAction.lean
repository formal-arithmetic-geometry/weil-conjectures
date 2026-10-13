/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients

/-!
# Section operators of two-parameter right translations

Source: the invariant-extension and mixed-coefficient steps in the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean` (blueprint `sk-d-tangent`).
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- Right translation of the universal point by a point over `S[ε][δ]`. -/
noncomputable def twoParameterRightTranslation (z : Scheme.dualNumbers₂Over S ⟶ G) :
    G.left.dualNumbers.dualNumbers ⟶ G.left :=
  let X := Over.mk
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom)
  let p : X ⟶ G := Over.homMk
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj) (Category.assoc _ _ _)
  let q : X ⟶ G := Over.homMk (G.hom.dualNumbers.dualNumbers ≫ z.left) (by
    rw [Category.assoc, Over.w z]
    change G.hom.dualNumbers.dualNumbers ≫
      S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj =
        G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom
    rw [Scheme.Hom.dualNumbers_comp_proj_assoc, Scheme.Hom.dualNumbers_comp_proj])
  (p * q).left

/-- The coefficientwise operator `1 + εD` on a double square-zero extension. -/
def epsilonSectionAction {R : Type u} [CommRing R] (D : AddMonoid.End R)
    (x : DualNumber (DualNumber R)) : DualNumber (DualNumber R) :=
  ⟨⟨x.fst.fst, x.fst.snd + D x.fst.fst⟩,
    ⟨x.snd.fst, x.snd.snd + D x.snd.fst⟩⟩

/-- The coefficientwise operator `1 + δD` on a double square-zero extension. -/
def deltaSectionAction {R : Type u} [CommRing R] (D : AddMonoid.End R)
    (x : DualNumber (DualNumber R)) : DualNumber (DualNumber R) :=
  ⟨x.fst, ⟨x.snd.fst + D x.fst.fst, x.snd.snd + D x.fst.snd⟩⟩

/-- The section map of the right-translation commutator is the composition of its four
coefficientwise square-zero operators, before extracting any mixed coefficient.

Source: the invariant-extension and mixed-coefficient steps of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`.
(blueprint: lem-ag-two-parameter-translation-action)

Proof: Base change right translation by v from S[ε] to S[ε][δ], keeping δ fixed.
On each open its comorphism is 1+εD_v. Indeed reduction along ε=0 is the identity,
the ε coefficient on constants is the defining invariantCoefficient, and compatibility
with the projection to S[ε][δ] fixes both parameters. The same argument for w fixes ε
and gives 1+δD_w. These descriptions act coefficientwise on all four components of
Γ(U,𝒪_G)[ε][δ]. The inverse translations have the inverse operators 1-εD_v and
1-δD_w: multiplication cancels the linear terms and the quadratic terms vanish.
Right translation by the product v_ε w_δ v_ε⁻¹ w_δ⁻¹ is the successive composition
of these four translations. Contravariance gives the displayed order on functions,
namely the operator for v_ε outermost. Apply these operators to the constant section
a. Since all translations reduce to the identity, their underlying maps are identity
maps of G; appLE therefore evaluates them on the same open U, independently of its
proof argument e. This proves the equality without extracting the mixed coefficient.
The argument is sheafwise, works on an empty scheme, and uses only square-zero
identities, with no division or smoothness hypothesis. -/
theorem twoParameterRightTranslation_commutator_app
    (v w : infPoints G) (U : G.left.Opens)
    (e : U ≤ (twoParameterRightTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹)) ⁻¹ᵁ U)
    (a : Γ(G.left, U)) :
    (twoParameterRightTranslation G
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹)).appLE U U e a =
      epsilonSectionAction (invariantCoefficient G v U)
        (deltaSectionAction (invariantCoefficient G w U)
          (epsilonSectionAction (-invariantCoefficient G v U)
            (deltaSectionAction (-invariantCoefficient G w U) (inl (inl a))))) := by sorry

end AlgebraicGeometry.GrpObj
