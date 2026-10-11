/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Meromorphic modules

Source: Stacks Project, Divisors, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module).

We sheafify the localizations of module sections at sections regular at every stalk.
For an invertible module this is canonically the tensor product with the meromorphic sheaf.
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing Mathlib submonoid of sections whose germs are non-zero-divisors.
Source: Stacks, Tag 01X2 (blueprint: def-sc-meromorphic-module). -/
noncomputable abbrev meromorphicDenominators (X : Scheme.{u}) (U : X.Opens) :=
  (X.presheaf.submonoidPresheafOfStalk fun x ↦ nonZeroDivisors (X.presheaf.stalk x)).obj (op U)

/-- Restriction in Mathlib's existing submonoid presheaf. Source: Stacks, Tag 01X2
(blueprint: def-sc-meromorphic-module). -/
noncomputable def restrictMeromorphicDenominator (X : Scheme.{u}) {U V : X.Opens}
    (i : V ⟶ U) (b : meromorphicDenominators X U) : meromorphicDenominators X V :=
  ⟨X.presheaf.map i.op b.val,
    (X.presheaf.submonoidPresheafOfStalk fun x ↦ nonZeroDivisors (X.presheaf.stalk x)).map
      i.op b.property⟩

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: restriction preserves regular denominators. The localization universal property extends
restriction uniquely, sending m/b to res(m)/res(b); equality of fractions is preserved since
its annihilating denominator restricts to a regular denominator. -/
theorem exists_meromorphicRestriction (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    ∃ f : LocalizedModule (meromorphicDenominators X U) Γ(M, U) →ₛₗ[
        (X.presheaf.map i.op).hom]
        LocalizedModule (meromorphicDenominators X V) Γ(M, V),
      ∀ (m : Γ(M, U)) (b : meromorphicDenominators X U),
        f (LocalizedModule.mk m b) =
          LocalizedModule.mk (M.presheaf.map i.op m) (restrictMeromorphicDenominator X i b) := by
  sorry

/-- The canonical restriction of localized sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicRestriction (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (exists_meromorphicRestriction X M i).choose

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: on m/b, restriction by the identity fixes numerator and denominator; every localized
section is a fraction. -/
theorem meromorphicRestriction_id (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (z : LocalizedModule (meromorphicDenominators X U) Γ(M, U)) :
    meromorphicRestriction X M (𝟙 U) z = z := by
  sorry

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: both maps send m/b to its iterated restriction, by the presheaf laws for M and O_X;
every localized section is a fraction. -/
theorem meromorphicRestriction_comp (X : Scheme.{u}) (M : X.Modules)
    {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (z : LocalizedModule (meromorphicDenominators X U) Γ(M, U)) :
    meromorphicRestriction X M (j ≫ i) z =
      meromorphicRestriction X M j (meromorphicRestriction X M i z) := by
  sorry

/-- The presheaf of localized module sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicPresheaf (X : Scheme.{u}) (M : X.Modules) :
    X.PresheafOfModules where
  obj U := ModuleCat.of Γ(X, U.unop)
    (LocalizedModule (meromorphicDenominators X U.unop) Γ(M, U.unop))
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, U.unop)
      (LocalizedModule (meromorphicDenominators X U.unop) Γ(M, U.unop)))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(X, V.unop)
        (LocalizedModule (meromorphicDenominators X V.unop) Γ(M, V.unop))))
    { toFun := meromorphicRestriction X M i.unop
      map_add' := (meromorphicRestriction X M i.unop).map_add
      map_smul' := (meromorphicRestriction X M i.unop).map_smul' }
  map_id U := by
    ext z
    exact meromorphicRestriction_id X M U.unop z
  map_comp i j := by
    ext z
    exact meromorphicRestriction_comp X M i.unop j.unop z

/-- The meromorphic module is the associated sheaf of localized sections.
Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicModule (X : Scheme.{u}) (M : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (meromorphicPresheaf X M)

/-- Fractions map into the associated sheaf. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicFraction (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    LocalizedModule (meromorphicDenominators X U) Γ(M, U) →ₗ[Γ(X, U)]
      Γ(meromorphicModule X M, U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (meromorphicPresheaf X M)).app (op U) |>.hom

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: restriction sends m/1 to res(m)/1, by the defining fraction formula. Thus localization
of ordinary sections is a natural transformation of presheaves of modules. -/
theorem meromorphicLocalization_natural (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    meromorphicRestriction X M i (LocalizedModule.mkLinearMap _ _ m) =
      LocalizedModule.mkLinearMap _ _ (M.presheaf.map i.op m) := by
  sorry

/-- Ordinary sections as meromorphic presheaf sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicLocalization (X : Scheme.{u}) (M : X.Modules) :
    M.val ⟶ meromorphicPresheaf X M where
  app U := ModuleCat.ofHom (X := M.val.obj U) (Y := (meromorphicPresheaf X M).obj U)
    { toFun := LocalizedModule.mkLinearMap (meromorphicDenominators X U.unop) Γ(M, U.unop)
      map_add' := (LocalizedModule.mkLinearMap
        (meromorphicDenominators X U.unop) Γ(M, U.unop)).map_add
      map_smul' := (LocalizedModule.mkLinearMap
        (meromorphicDenominators X U.unop) Γ(M, U.unop)).map_smul' }
  naturality i := by
    ext m
    exact (meromorphicLocalization_natural X M i.unop m).symm

/-- The canonical map from ordinary to meromorphic sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def toMeromorphicModule (X : Scheme.{u}) (M : X.Modules) :
    M ⟶ meromorphicModule X M :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage
    (meromorphicLocalization X M ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (meromorphicPresheaf X M))

/-- Source: Stacks, Tag 01X4 (blueprint: def-sc-meromorphic-module).
Proof: on a trivializing open for M, both sides are the meromorphic sheaf. The identification
sends (a/b) tensor m to (am)/b and commutes with restriction. These local identifications
and their inverses therefore glue. -/
theorem meromorphicModule_tensor_iso (X : Scheme.{u}) (M : X.Modules) [M.IsInvertible] :
    Nonempty ((meromorphicModule X (unit X) ⊗ M) ≅ meromorphicModule X M) := by
  sorry

/-- Source: Stacks, Tags 01X4 and 02OX (blueprint: def-sc-meromorphic-module).
Proof: locally a meromorphic scalar is a/b. Send it to a times s divided by b in the
localized module. This is independent of representatives, because b acts invertibly there.
The local maps agree under restriction and glue. Uniqueness follows since multiplication
by every regular denominator is invertible in the meromorphic module. -/
theorem exists_meromorphicSectionMap (X : Scheme.{u}) (M : X.Modules)
    (s : unit X ⟶ meromorphicModule X M) :
    ∃! f : meromorphicModule X (unit X) ⟶
        meromorphicModule X M,
      toMeromorphicModule X (unit X) ≫ f = s := by
  sorry

/-- Multiplication by a meromorphic section, extended from ordinary scalars by localization.
Source: Stacks, Tags 01X4 and 02OX (blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicSectionMap (X : Scheme.{u}) (M : X.Modules)
    (s : unit X ⟶ meromorphicModule X M) :
    meromorphicModule X (unit X) ⟶ meromorphicModule X M :=
  (exists_meromorphicSectionMap X M s).exists.choose

end AlgebraicGeometry.Scheme.Modules
