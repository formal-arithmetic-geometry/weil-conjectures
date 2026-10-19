/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.FiniteTypeExceptionalInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
/-! # The pro-etale section invariant

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: def-pur-section-invariant).

Its data are the actual derived inverse image of the relative dualizing object.
No orientation or Tate identification is chosen. The finite coefficient stage is
used here, as stipulated by the purity conventions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The section invariant C(g,s) = Ls* Rg! A_B on the small pro-etale site.
The definition makes sense for any map s; its geometric and invertibility
properties below apply to closed sections of smooth separated finite-type maps.
Source: blueprint def-pur-section-invariant, displayed definition
(blueprint: def-pur-section-invariant). -/
noncomputable def sectionInvariant (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (s : B ⟶ V) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) s).leftDerivedFunctor.obj
    (P.dualizing g aB)

/-- The section invariant and an inverse belong to D^b_ctf, with both tensor products
isomorphic to the coefficient unit. The section is closed, smoothness is allowed to
have locally varying relative dimension, and no orientation is part of the conclusion.
Source: blueprint def-pur-section-invariant, invertibility paragraph
(blueprint: def-pur-section-invariant).
Proof: partition V into its finitely many clopen smooth dimension loci. Apply
thm-pur-cohomological-smoothness on each locus; finite products reassemble their
invertible dualizing objects. Pull back the two inverse isomorphisms along s.
Derived pullback preserves the coefficient unit and tensor products. Its exactness
preserves constructibility, and s*g*=id tests the same uniform Tor interval after
pullback. These facts put both pulled-back objects in D^b_ctf, including the empty case. -/
theorem sectionInvariant_invertible (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] [Smooth g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} P.Coefficient) B (P.sectionInvariant g aB s) ∧
      ∃ Q : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} P.Coefficient) B Q ∧
        Nonempty (P.sectionInvariant g aB s ⊗ Q ≅ 𝟙_ _) ∧
        Nonempty (Q ⊗ P.sectionInvariant g aB s ≅ 𝟙_ _) := by
  sorry

end WeilConjectures.PurityFiniteSetting
