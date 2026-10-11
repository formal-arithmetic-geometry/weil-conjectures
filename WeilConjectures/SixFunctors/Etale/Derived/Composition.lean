/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The composition law for `Rf_!` and its mate

Two statements of the six-functor bookkeeping that the purity chapter uses: the
identification `Rf_! ≅ Rf_*` for proper `f`, and the mate of the composition isomorphism,
`R(g ∘ f)^! ≅ Rf^! Rg^!`. The composition isomorphism `R(g ∘ f)_! ≅ Rf_! ⋙ Rg_!` itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.

The compactification-independence that makes `Rf_!` well defined is already in the
repository, as
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Implementation notes

On the unbounded derived categories the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`, built from the chosen
compactifications; its mate is `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso`, and
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction_comp_eq` says that the unit and
counit of the composite adjunction are the pasted ones. The older existential form
`AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq` is kept as a
corollary. The canonical composition isomorphism on the
bounded below derived categories, with its unit and associativity laws, is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso`, with
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction_comp_eq`
- `AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- Blueprint `sk-prop-sf-comp-proper`: Proper coincidence

**Proper coincidence.** For `f : X ⟶ Y` proper the identity is a compactification of `f`, and
the resulting canonical identification

`Rf_! ≅ Rf_*`

is independent of the compactification.

At the level of sheaves this is `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`, which
states that the *canonical comparison* `f_! ⟶ f_*` is an isomorphism; the derived comparison
map has not been constructed, so only the existence of the derived isomorphism is recorded
here. -/
theorem nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (f : X ⟶ Y)
    [HasCompactification f] [IsProper f] :
    Nonempty (R(f)_![A] ≅ R((f)_*[A])) := by
  let c := HasCompactification.compactification f
  -- the open immersion of the compactification is proper, so it has closed range and `j_! ≅ j_*`
  have := Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  let ι := asIso (Etale.openImmersionLowerShriekToLowerStar A c.i)
  have : PreservesFiniteColimits (c.i)_*[A] := preservesFiniteColimits_of_natIso ι
  have : PreservesFiniteLimits (c.i)_*[A] := preservesFiniteLimits_of_natIso ι
  exact ⟨Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso ι) R((c.g)_*[A]) ≪≫
    Functor.isoWhiskerRight ((c.i)_*[A].rightDerivedFunctorIsoMapDerivedCategory).symm
      R((c.g)_*[A]) ≪≫ rightDerivedLowerStarComp A c.i c.g ≪≫
    rightDerivedLowerStarCongr A c.comm.symm⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

Clause (b), étale form: for composable `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications
and torsion coefficients, there is a composition isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(`sk-thm-sf-comp-composition`) whose mate `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` under the adjunctions
`Rf_! ⊣ Rf^!` on the unbounded derived categories of the small étale sites carries the
adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^!` to the composite adjunction `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`:
the unit and counit of the composite adjunction are the pasted ones. The mate statement is
formal (`CategoryTheory.Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv`). This is the
existential corollary of `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction_comp_eq`, for
the composition isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`.
The constructible form, on the small pro-étale sites, is
`AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq`. -/
theorem exists_rightDerivedUpperShriekAdjunction_comp_eq (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    ∃ e : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
        R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
      ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e).ofNatIsoRight
        (conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))
          (rightDerivedUpperShriekAdjunction _ (f ≫ g)) e).symm =
        (rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g) :=
  ⟨rightDerivedLowerShriekCompIso Λ f g,
    Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ _⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

Clause (b), étale form: **the mate of the composition isomorphism**. For composable `f : X ⟶ Y`
and `g : Y ⟶ S` admitting compactifications and torsion coefficients, the isomorphism
`R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` of the right adjoints on the unbounded derived categories of the small
étale sites which is mate, under `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and the composite adjunction
`Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, to the composition isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` (`sk-thm-sf-comp-composition`). -/
noncomputable def rightDerivedUpperShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f ≫ g)^![ModuleCat.{u + 1} Λ] ≅
      R(g)^![ModuleCat.{u + 1} Λ] ⋙ R(f)^![ModuleCat.{u + 1} Λ] :=
  (conjugateIsoEquiv
    ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))
    (rightDerivedUpperShriekAdjunction _ (f ≫ g)) (rightDerivedLowerShriekCompIso Λ f g)).symm

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

Clause (b), étale form: transporting the adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^!` along the
composition isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` and its mate
`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso` gives the composite adjunction
`Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`: the unit and counit of the composite adjunction are the pasted
ones. The componentwise forms are
`AlgebraicGeometry.Etale.unit_comp_rightDerivedUpperShriekCompIso_inv_app` and
`AlgebraicGeometry.Etale.map_rightDerivedUpperShriekCompIso_inv_app_counit`. This is also
clause (3) of blueprint `fix-prop-adjunctions` for the exceptional pair. -/
theorem rightDerivedUpperShriekAdjunction_comp_eq (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft
        (rightDerivedLowerShriekCompIso Λ f g)).ofNatIsoRight
        (rightDerivedUpperShriekCompIso Λ f g) =
      (rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g) :=
  Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ _

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`, units: under the mate
`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso` of the composition isomorphism, the
pasted unit `K ⟶ Rf^! Rg^! Rg_! Rf_! K` corresponds to the unit of
`R(f ≫ g)_! ⊣ R(f ≫ g)^!`. -/
lemma unit_comp_rightDerivedUpperShriekCompIso_inv_app (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g)).unit.app
        K ≫ (rightDerivedUpperShriekCompIso Λ f g).inv.app _ =
      (rightDerivedUpperShriekAdjunction _ (f ≫ g)).unit.app K ≫
        R(f ≫ g)^![ModuleCat.{u + 1} Λ].map ((rightDerivedLowerShriekCompIso Λ f g).hom.app K) := by
  rw [rightDerivedUpperShriekCompIso, Iso.symm_inv, conjugateIsoEquiv_apply_hom]
  exact unit_conjugateEquiv _ _ _ K

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`, counits: under the mate
`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso` of the composition isomorphism, the
counit of `R(f ≫ g)_! ⊣ R(f ≫ g)^!` corresponds to the pasted counit
`Rg_! Rf_! Rf^! Rg^! L ⟶ L`. -/
lemma map_rightDerivedUpperShriekCompIso_inv_app_counit (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)]
    (L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ].map ((rightDerivedUpperShriekCompIso Λ f g).inv.app L) ≫
        (rightDerivedUpperShriekAdjunction _ (f ≫ g)).counit.app L =
      (rightDerivedLowerShriekCompIso Λ f g).hom.app _ ≫
        ((rightDerivedUpperShriekAdjunction _ f).comp
          (rightDerivedUpperShriekAdjunction _ g)).counit.app L := by
  rw [rightDerivedUpperShriekCompIso, Iso.symm_inv, conjugateIsoEquiv_apply_hom]
  exact conjugateEquiv_counit _ _ _ L

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

**The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S` and
torsion coefficients,

```
  R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!           (left adjoints, sk-thm-sf-comp-composition)
        ⊣              ⊣
  R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!           (right adjoints, the mate)
```

the mate of the composition isomorphism is an isomorphism `R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`: right
adjoints of isomorphic functors are isomorphic, and the right adjoint of a composite is the
composite of the right adjoints. The isomorphism is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso`, the mate of the composition isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` of the lower shrieks, which needs torsion
coefficients.

This is clause (b) of `sk-lem-sf-mate` in its étale form, for morphisms admitting a
compactification (`sk-prop-sf-existence`(a)); that it is the mate, with the pasted unit and
counit, is `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction_comp_eq`. Clause
(a), the pro-étale ambient form, is the theorem
`ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` in the namespace
`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`.
The hypothesis `HasCompactification (f ≫ g)` is redundant over a quasi-compact
quasi-separated base, by Nagata's theorem; it is kept because no composition instance for
`HasCompactification` is available in general. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    Nonempty (R(f ≫ g)^![ModuleCat.{u + 1} Λ] ≅
      R(g)^![ModuleCat.{u + 1} Λ] ⋙ R(f)^![ModuleCat.{u + 1} Λ]) :=
  ⟨rightDerivedUpperShriekCompIso Λ f g⟩

end Etale

end AlgebraicGeometry
