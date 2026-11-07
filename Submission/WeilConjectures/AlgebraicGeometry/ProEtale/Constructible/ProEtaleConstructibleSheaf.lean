/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Constructible finite-coefficient module sheaves on the pro-etale site

Source: Weil blueprint, `def-weil-finite-torsion-constructibility`, second paragraph
(blueprint: def-weil-proetale-constructible-sheaf).

The global finite partition convention is retained, including a positive number of strata.
The coefficient pullback is the existing tensor extension along the canonical
constant-section comparison, with no independently chosen coefficient identification.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A sheaf of modules over a finite commutative constant ring is constructible if
some finite partition into locally closed constructible immersed subschemes has
locally constant restrictions with finite geometric stalks. The restriction is
`proEtaleConstantModulePullback`: inverse image followed by tensor extension along
`proEtaleCoefficientInverseImageMap`, the canonical comparison of constant ring sheaves.
Finiteness is imposed on the underlying set of the module stalk, equivalently finite
module generation since the coefficient ring is finite. The coefficient ring itself
may be the zero ring, and the empty scheme is allowed.
Source: Weil blueprint, `def-weil-finite-torsion-constructibility`, second paragraph;
compare Stacks Tag 09AJ, whose affine-local convention differs from this global one
(blueprint: def-weil-proetale-constructible-sheaf). -/
noncomputable def IsConstructibleProEtaleModuleSheaf
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) : Prop :=
  ∃ S : Stratification Y, 0 < S.n ∧
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A F))

end AlgebraicGeometry.Scheme
