/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import Mathlib.Algebra.Category.ModuleCat.Free
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Additivity of the Euler defect on an integral proper curve

Source: Stacks Project, Varieties, Tag 0AYV, proof of condition (1)
(blueprint: lem-trf-curve-euler-defect-additivity).

The auxiliary definitions spell out the generic stalk with its transported residue-field
scalars, its rank, and the integer defect. The theorem identifies the transporting
isomorphism with the canonical residue quotient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing stalk of `H`, with scalars transported from the local ring to its residue
field along an isomorphism `e`. The theorem below requires `e` to be the canonical residue
quotient, so this is exactly the generic stalk as a residue-field vector space.
Source: Stacks Project, Varieties, Tag 0AYV, the rank in the displayed formula
(blueprint: lem-trf-curve-euler-defect-additivity). -/
noncomputable def curveResidueStalk {C : Scheme.{u}} (ξ : C)
    (e : C.presheaf.stalk ξ ≃+* C.residueField ξ) (H : C.Modules) :
    ModuleCat.{u} (C.residueField ξ) :=
  (ModuleCat.restrictScalars e.symm.toRingHom).obj
    ((RingedSpace.moduleStalkFunctor C.toRingedSpace ξ).obj H)

/-- The rank `r(H) = dim_{κ(ξ)} H_ξ`, using the transported stalk above.
Source: Stacks Project, Varieties, Tag 0AYV, the rank in the displayed formula
(blueprint: lem-trf-curve-euler-defect-additivity). -/
noncomputable def curveGenericRank {C : Scheme.{u}} (ξ : C)
    (e : C.presheaf.stalk ξ ≃+* C.residueField ξ) (H : C.Modules) : ℕ :=
  Module.finrank (C.residueField ξ) (curveResidueStalk ξ e H)

/-- The integer `D_L(H) = χ(C,L ⊗ H) - χ(C,H) - r(H) deg_k(L)`.
Source: Stacks Project, Varieties, Tag 0AYV, proof of condition (1)
(blueprint: lem-trf-curve-euler-defect-additivity). -/
noncomputable def curveEulerDefect (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] (L : C.Modules) (ξ : C)
    (e : C.presheaf.stalk ξ ≃+* C.residueField ξ) (H : C.Modules) : ℤ :=
  (L ⊗ H).eulerChar k - H.eulerChar k - (curveGenericRank ξ e H : ℤ) * L.degree k

/-- Noetherianity, the generic residue-field identification, coherence and finite generic
rank, vanishing at zero, and additivity of the Euler defect for coherent short exact sequences.
The final three implications express vanishing for any third term when two terms vanish.
Source: Stacks Project, Varieties, Tag 0AYV, proof of condition (1)
(blueprint: lem-trf-curve-euler-defect-additivity).

Proof for stage 3:
1. `lem-trf-proper-field-invertible-coherent` makes `C` locally Noetherian and compact
and makes `L` and the structure sheaf coherent. No smoothness or geometric integrality is
needed. `lem-sc-rational-functions-generic-stalks` makes the generic local ring a field.
Its maximal ideal is zero, so its residue quotient is an isomorphism
(`def-weil-residue-field`); take this as `e`.
2. Trivialize `L` on open neighborhoods (`def-sc-invertible-module`). There `L ⊗ H` is
`H`, with mutually inverse maps `a ⊗ h ↦ a h` and `h ↦ 1 ⊗ h`, also after sheafification
(`def-pur-sheaf-tensor-product`). Finite type and the finite-type-kernel condition of
`pqf-def-coherent` are local, proving coherence of the tensor.
3. A finite local presentation surjects onto `H` near `ξ`. Apply the exact stalk functor
`def-sc-open-module-stalk-functor`: the finitely many standard germs span `H_ξ`.
The stalk of a finite free sheaf is finite free, by intersecting the finitely many
representative neighborhoods (`def-weil-pbc-module-stalk`). Delete dependent generators
to get a finite basis, and transport along `e`.
4. `lem-pc-euler-characteristic-well-defined` gives finite-dimensional cohomology and
finite support for the coherent sheaves in the formula; thus the recorded Euler
characteristic and `def-pc-degree-line-bundle` give integers. The stalk functor preserves
kernels and cokernels. After transport along `e`,
`lem-trf-finite-dimensional-short-exact-dimension` gives additivity of generic rank.
5. Invertibility is finite local freeness of rank one. `lem-sc-ext-tensor-exact` preserves
the short exact sequence under tensoring with `L`. Apply `lem-pc-euler-additive` to this
coherent sequence and the original sequence.
6. Substitute the two Euler-characteristic equalities and rank additivity into the defect
formula and distribute in the integers. The zero sheaf is coherent by `pqf-def-coherent`;
its stalk and tensor are zero and its dimension is zero. Euler additivity on the zero
sequence implies `χ(C,0) = 0`, giving zero defect. Finally solve `D₂ = D₁ + D₃` for any
term when the other two vanish. -/
theorem curve_euler_defect_additivity (k : Type u) [Field k] (C : Scheme.{u})
    [IsIntegral C] [C.Over (Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = 1) (ξ : C) (hξ : IsGenericPoint ξ Set.univ)
    (L : C.Modules) [L.IsInvertible] :
    IsLocallyNoetherian C ∧ CompactSpace C ∧ IsField (C.presheaf.stalk ξ) ∧
    ∃ e : C.presheaf.stalk ξ ≃+* C.residueField ξ,
      e.toRingHom = (C.residue ξ).hom ∧
      (∀ H : C.Modules, RingedSpace.IsCoherent C.toRingedSpace H →
        RingedSpace.IsCoherent C.toRingedSpace (L ⊗ H) ∧
        FiniteDimensional (C.residueField ξ) (curveResidueStalk ξ e H)) ∧
      curveEulerDefect k L ξ e (0 : C.Modules) = 0 ∧
      (∀ S : ShortComplex C.Modules, S.ShortExact →
        RingedSpace.IsCoherent C.toRingedSpace S.X₁ →
        RingedSpace.IsCoherent C.toRingedSpace S.X₂ →
        RingedSpace.IsCoherent C.toRingedSpace S.X₃ →
        curveGenericRank ξ e S.X₂ = curveGenericRank ξ e S.X₁ +
          curveGenericRank ξ e S.X₃ ∧
        curveEulerDefect k L ξ e S.X₂ = curveEulerDefect k L ξ e S.X₁ +
          curveEulerDefect k L ξ e S.X₃ ∧
        (curveEulerDefect k L ξ e S.X₁ = 0 ∧ curveEulerDefect k L ξ e S.X₂ = 0 →
          curveEulerDefect k L ξ e S.X₃ = 0) ∧
        (curveEulerDefect k L ξ e S.X₁ = 0 ∧ curveEulerDefect k L ξ e S.X₃ = 0 →
          curveEulerDefect k L ξ e S.X₂ = 0) ∧
        (curveEulerDefect k L ξ e S.X₂ = 0 ∧ curveEulerDefect k L ξ e S.X₃ = 0 →
          curveEulerDefect k L ξ e S.X₁ = 0)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
