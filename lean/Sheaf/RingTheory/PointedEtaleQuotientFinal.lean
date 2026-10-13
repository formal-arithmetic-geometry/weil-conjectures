/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Sheaf.RingTheory.SurjectiveQuotientBaseChange
public import Mathlib.CategoryTheory.Limits.Final

/-! # Finality of pointed etale base change

Source: Stacks Project, Tag 05WS, with the pointed-algebra argument of
`IsStrictHenselization.surjective_quotient`.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Base change of pointed etale algebras along a surjective local map is final.
Source: Stacks Project, Tag 05WS; pointed-colimit proof as recorded in
lem-sbc-strict-henselization-surjective-quotient.
(blueprint: lem-sbc-pointed-etale-quotient-final)

Proof: Surjectivity identifies B with A/ker π. The induced residue-field map is an
isomorphism. Transport K across it and identify it with the chosen separable closure
L; separable closures are isomorphic over the residue field. Extension of scalars
sends an etale A-algebra S pointed in K to B tensor_A S, pointed in L, and preserves
etaleness. On morphisms use extension of scalars. This defines F and the comparison
isomorphism of underlying diagrams. Identify B with A/ker π and apply the existing
etale-algebra lifting result (blueprint node lem-exc-etale-algebra-lift) to the pointed
etale B-algebra T. It supplies an etale A-algebra S and its specified reduction
isomorphism. Compose the reduction with T -> L and the residue-compatible isomorphism
L -> K to point S. The inverse reduction isomorphism gives T -> F(S), supplying an
object of (T down F). For two
objects of this comma category, tensor their A-algebras and multiply their K-points.
The resulting two maps from T agree at the distinguished point. The diagonal of the
etale B-algebra T is open, so they agree on a principal neighbourhood of that point.
Lift its denominator to the A-tensor product and invert it; it remains nonzero at
the K-point. This gives a common refinement equalizing the arrows. Thus the comma
category is nonempty and connected, which is the finality criterion. No strict
henselization C or colimit hypothesis is needed for this statement. -/
theorem pointedEtaleQuotient_final
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) :
    let P : ObjectProperty (Over (CommAlgCat.of A K)) := fun X ↦ Etale A X.left
    let Q : ObjectProperty (Over (CommAlgCat.of B L)) := fun X ↦ Etale B X.left
    ∃ F : P.FullSubcategory ⥤ Q.FullSubcategory, F.Final ∧
      Nonempty ((P.ι ⋙ Over.forget (CommAlgCat.of A K)) ⋙ quotientBaseChange π ≅
        F ⋙ (Q.ι ⋙ Over.forget (CommAlgCat.of B L))) := by sorry

end Algebra
