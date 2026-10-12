module

import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
public import Sheaf.AlgebraicGeometry.DerivedCategory

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The ambient derived category of sheaves of modules has coproducts
(blueprint: lem-pc-derived-ambient-has-coproducts). The proof chooses representatives
for each derived object, forms the termwise coproduct complex, and applies
`derivedAmbientDirectSums`; the resulting coproduct cocone is transported along the
chosen representative isomorphisms.
Source: Stacks Project, Lemma 08DT. Proof: choose representatives for each derived
object, form the termwise coproduct complex, and apply `derivedAmbientDirectSums` to
obtain the coproduct cocone and its universal property; choice of representatives
assembles these cocones for every small discrete diagram. -/
theorem derivedAmbientHasCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    HasCoproducts.{u} (schemeDerivedCategory X) := by sorry

/-- Quasi-coherent cohomology is closed under ambient derived coproducts
(blueprint: lem-pc-derived-qcoh-closed-coproducts). The proof identifies cohomology of
the ambient coproduct with direct sums, writes each direct sum as a filtered colimit of
finite sums, and applies finite-sum and filtered-colimit quasi-coherence closure.
Source: Stacks Project, Lemma 08DT. Proof: `derivedAmbientDirectSums` identifies each
cohomology sheaf of the ambient coproduct with the direct sum of the input cohomology
sheaves. Express that direct sum as the filtered colimit of finite partial sums;
`isQuasicoherent_biprod` proves the finite case and
`quasiCoherentModuleColimitAffineSections` proves closure under the filtered colimit. -/
theorem schemeDerivedQCohClosedUnderCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) :
    (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) := by sorry

end AlgebraicGeometry
