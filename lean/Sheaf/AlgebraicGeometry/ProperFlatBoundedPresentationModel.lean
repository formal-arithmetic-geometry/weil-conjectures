/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded perfect cohomology models before lower truncation -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded finite-presentation flat model computing every base change, with no
prescribed termwise lower bound. Its base changes have zero negative homology.
Source: Stacks Project, Tags 0B91(2), 0A1H and 08EB.
(blueprint: lem-pc-proper-flat-bounded-presentation-model).

Proof: Restrict the proper finitely presented morphism and its relatively flat
finitely presented sheaf to U. Tag 0B91(2), proved by Noetherian approximation in
Tag 0A1H, makes the derived direct image perfect and compatible with arbitrary
base change. Identify U with Spec of its global-section ring. Tag 08EB represents
this perfect object by a bounded complex of finite projective modules. Associate
sheaves termwise and transport back to U; its terms are quasi-coherent, flat and
finitely presented. Choose an integer lower bound a and enlarge its upper bound
to a natural number b. Bounded flat complexes compute derived pullback by ordinary
pullback. Derived base change and the comparison of derived direct-image homology
with higher direct images give the displayed isomorphisms. All negative homology
vanishes after every base change because the pulled-back coefficient sheaf sits
in degree zero and derived direct image is left t-exact. This vanishing does not
require choosing injective resolutions in the statement: the derived construction
has standard categories, and negative cohomology vanishes intrinsically. Transport
from a standard fibre product to any supplied cartesian square by its canonical
isomorphism. For empty U or zero coefficients take the zero complex and a = b = 0.
No truncation or flatness assertion about an opcycle is made here. -/
theorem exists_proper_flat_boundedPresentation_model {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme) :
    ∃ (C : CochainComplex U.toScheme.Modules ℤ) (a : ℤ) (b : ℕ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (C.X n).IsFinitePresentation) ∧
      (∀ {S : Scheme.{u}} (g : S ⟶ U.toScheme) (i : ℤ), i < 0 →
        IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
