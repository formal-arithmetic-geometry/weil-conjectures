/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.CoefficientRingedSequenceSite

/-! # Shift compatibility of the open adjunction on coefficient systems

Source: blueprint `sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`,
paragraph 2, adjunction units and counits among the coherence maps
(blueprint: lem-pur-open-adjunction-shift).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.IntegralSystemRealization

/-- The restriction functor uses the existing termwise exact-functor shift comparison.
This exposes that canonical structure through the recorded derived-pullback definition.
Source: blueprint `fix-prop-coherence.proof.md`, paragraph 2
(blueprint: lem-pur-open-adjunction-shift). -/
noncomputable instance openRestrictionCommShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] :
    (pull l E j).CommShift ℤ :=
  inferInstanceAs ((pullbackTensorSequenceInverse l E j).mapDerivedCategory.CommShift ℤ)

/-- The unit and counit of exact termwise open extension and restriction commute with
all integer shifts, as natural transformations on the ordinary unbounded derived
categories of strict semilinear coefficient systems, before evaluation or total limit.
The shift structures are the existing exact-functor structures, induced on cochains.
`o` names the simultaneous operations of the recorded integral realization; the
conclusion holds for every such presentation and its localized ordinary adjunction.

Source: blueprint `fix-prop-coherence.proof.md`, paragraph 2
(blueprint: lem-pur-open-adjunction-shift).

Proof:
1. The open immersion is etale, so its source is an object of the target pro-etale
site. Apply `lem-pur-site-restriction-module-adjunction-exact` at each coefficient
level, not at a nonexistent simultaneous open object of the sequence site.
Extension is the direct-sum extension presheaf followed by module sheafification.
Restriction and extension commute with quotient restriction of scalars: their
underlying abelian presheaves, and the underlying abelian sheafifications, agree.
Thus the levelwise functors, units, counits and triangle identities assemble into
strict system functors and maps. These are the ordinary exact adjunction whose
localization is `Open.adj` in `lem-sf-integral-compactification-system-realization`.
2. For shift a, in degree m both termwise comparison maps identify the same module
in degree m+a. Additivity identifies the differentials, including the sign (-1)^a.
These comparisons respect zero and addition of shifts. By
`lem-sf-exact-functor-derived-triangulated`, their localizations are the fixed
shift structures of the two derived functors. The unit in degree m of the shifted
complex is the ordinary unit in degree m+a, so the unit shift square holds already
on cochain complexes. Localizing gives the unit square in the system derived category.
The counit follows by `lem-weil-pbc-adjunction-shift-compatibility-unique`, part (i),
or by the identical degreewise calculation. Parts (ii) and (iii) identify the right
comparison with the unique compatible shift structure.
3. These are equalities of system transformations themselves. Finite evaluation
and total limit merely transport them; neither is used to detect equality.
The class `Adjunction.CommShift` records exactly the unit and counit squares,
naturally for every complex and every integer shift. -/
theorem openAdjunctionShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {U W : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (j : U ⟶ W) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (o : Operations l E) :
    ((o.extension j.left).adj).CommShift ℤ := by
  sorry

end WeilConjectures.IntegralSystemRealization
