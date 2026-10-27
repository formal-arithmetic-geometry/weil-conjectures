/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.RingTheory.CotangentTransitivityTriangle
public import Sheaf.RingTheory.CotangentFlatBaseChange

/-!
# Canonical cotangent square constructions

Source: Stacks Project, cotangent.tex, Tags 08PN, 08QL and 08QS;
sites-cohomology.tex, Tag 07A6
(blueprint: def-trf-cotangent-square-constructions).

These reducible aliases register existing constructions under a definition node.
No transitivity or base-change theorem is invoked to define them.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace Algebra.CotangentResolution.SquareData

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]

/-- The specified standard differential complex, with alternating differential.
Source: Stacks, Tag 08PN
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev standardComplex (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) :=
  Algebra.CotangentResolution.standardComplex C f

/-- The standard semilinear chain map associated to a ring square.
Source: Stacks, Tag 08QL
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev standardComplexMap (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :=
  Algebra.CotangentResolution.standardComplexMap C q

/-- The termwise ordinary tensor/restriction adjunction.
Source: Stacks, Tag 08QS
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev tensorComplexAdj {B B' : CommRingCat.{u}} (b : B ⟶ B') :=
  Algebra.CotangentResolution.tensorComplexAdj b

/-- The termwise tensor of the standard complex for a triple.
Source: Stacks, Tag 08QS
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev transitivityFirstComplex (C : Coherence.{u}) {A B D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) :=
  Algebra.CotangentResolution.transitivityFirstComplex C f g

/-- The first standard functoriality arrow, the tensor adjunct of the square map.
Source: Stacks, Tag 08QS
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev transitivityFirstMap (C : Coherence.{u}) {A B D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) :=
  Algebra.CotangentResolution.transitivityFirstMap C f g

/-- The second standard functoriality arrow, changing the base of a triple.
Source: Stacks, Tag 08QS
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev transitivitySecondMap (C : Coherence.{u}) {A B D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) :=
  Algebra.CotangentResolution.transitivitySecondMap C f g

/-- The existing universal K-flat derived scalar-extension functor.
Source: Stacks, Tag 06Y6
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev baseChangeExtension {B B' : CommRingCat.{u}} (b : B ⟶ B') :=
  Algebra.CotangentResolution.baseChangeExtension b

/-- The existing derived tensor/restriction adjunction with its normalized unit.
Source: Stacks, Tag 07A6
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev baseChangeAdjunction {B B' : CommRingCat.{u}} (b : B ⟶ B') :=
  Algebra.CotangentResolution.baseChangeAdjunction b

/-- The canonical cotangent comparison, the normalized adjunct of the standard square map.
Source: Stacks, Tag 08QL
(blueprint: def-trf-cotangent-square-constructions). -/
abbrev cotangentBaseChange (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :=
  Algebra.CotangentResolution.cotangentBaseChange C q

end Algebra.CotangentResolution.SquareData
