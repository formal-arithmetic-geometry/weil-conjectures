/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.CurveCoefficientPair
public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-!
# Constructible torsion sheaves on a curve

Source: the blueprint of the Weil conjectures, chapter `sec-proper-base-change`, unit
`sk-curve-calculations-pbc-for-the-projective-line--remark-1`, definition
(blueprint: def-weil-pbc-constructible-torsion); Stacks Project, Tags 03RW and 095E.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.CurveCoefficientPair

/-- The torsion abelian sheaf of a curve coefficient pair is constructible if its underlying
sheaf of sets admits a finite partition into constructible locally closed subschemes on which
its inverse-image restriction is locally constant with finite geometric stalks. The curve and
its torsion coefficient sheaf are the data of `P`; constructibility is the recorded set-sheaf
notion, applied after forgetting the group structure. Source: blueprint
`sec-proper-base-change/sk-curve-calculations-pbc-for-the-projective-line--remark-1`, definition;
Stacks Project, Definition 59.71.1 (Tag 03RW), Lemma 59.71.2 (Tag 095E)
(blueprint: def-weil-pbc-constructible-torsion). -/
def IsConstructible {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k) : Prop :=
  Scheme.IsConstructibleEtaleSheafOfSets
    ((sheafCompose P.C.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj P.F)

end AlgebraicGeometry.CurveCoefficientPair
