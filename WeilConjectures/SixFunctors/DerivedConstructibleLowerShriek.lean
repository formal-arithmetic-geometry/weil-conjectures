/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleLowerShriekOfPreserves

/-!
# Lower shriek on bounded constructible complexes and its ambient compatibility

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-sf-existence/det-def-sfb-dc-lower-shriek.md`
(blueprint: det-def-sfb-dc-lower-shriek).

The lower shriek `Rf_!^c = Rp_* ∘ i_!` on bounded constructible complexes, for an arbitrary
commutative condensed coefficient ring whose derived pushforwards preserve bounded
constructibility, and the chosen `Rf_! = Rf_!^{c_f}`, are the landed declarations
`boundedConstructibleLowerShriekOfCompactificationOfPreserves` and
`boundedConstructibleLowerShriekOfPreserves` of
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleLowerShriekOfPreserves`
(blueprint: det-def-sfb-dc-lower-shriek-definition), built on the preservation hypothesis
`PreservesBoundedConstructiblePushforwards`. This file adds the compatibility of these functors
with the ambient lower shriek `R(p_*) ∘ D(i_!)` for the same compactification.

## Main definitions

* `boundedConstructibleLowerShriekOfCompactificationOfPreservesCompatibility`:
  `ι_Y ∘ Rf_!^c ≅ Rf_!^c ∘ ι_X` for a given compactification `c`.
* `boundedConstructibleLowerShriekOfPreservesCompatibility`: the same at the chosen
  compactification `AlgebraicGeometry.compactificationOverField`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k)

/-- The lower shriek attached to a compactification `c = (i, p)` is compatible with the ambient
lower shriek `R(p_*) ∘ D(i_!)` for the same `c`: `ι_Y ∘ Rf_!^c ≅ R(p_*) ∘ D(i_!) ∘ ι_X`.
Following the proof: with `F = i_!`, `G = Rp_*` the two restrictions, `a : ι_Z F ≅ D(i_!) ι_X`
and `b : ι_Y G ≅ R(p_*) ι_Z` their inclusion compatibilities, the component at `K` is
`R(p_*)(a_K) ∘ b_{F K}`; it is a natural isomorphism by pasting `b` (whiskered by `F`) and
`a` (whiskered by `R(p_*)`), with inverse and naturality those of the pasted isomorphisms.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-sf-existence/det-def-sfb-dc-lower-shriek.md`, compatibility paragraph
(blueprint: det-def-sfb-dc-lower-shriek). -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationOfPreservesCompatibility
    {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationOfPreserves Λ ℓ H c ⋙
        (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c.obj.obj :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerStarOfPreservesCompatibility Λ H c.obj.obj.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.obj.obj.overI) _ ≪≫
    Functor.associator _ _ _

/-- The chosen lower shriek `Rf_! = Rf_!^{c_f}` on bounded constructible complexes is compatible
with the ambient lower shriek attached to the same chosen compactification
`c_f = AlgebraicGeometry.compactificationOverField k f.left`: this is the preceding isomorphism
evaluated at `c_f`, so no comparison between different compactifications is involved.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-sf-existence/det-def-sfb-dc-lower-shriek.md`, final sentence (the case `c = c_f`)
(blueprint: det-def-sfb-dc-lower-shriek). -/
noncomputable def boundedConstructibleLowerShriekOfPreservesCompatibility (f : X ⟶ Y) :
    letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
    letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
    letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
    letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
    letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
    boundedConstructibleLowerShriekOfPreserves Λ ℓ H f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ
        (AlgebraicGeometry.compactificationOverField k f.left).obj.obj :=
  letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  boundedConstructibleLowerShriekOfCompactificationOfPreservesCompatibility Λ ℓ H
    (AlgebraicGeometry.compactificationOverField k f.left)

end AlgebraicGeometry.ProEtale.CondensedRing
