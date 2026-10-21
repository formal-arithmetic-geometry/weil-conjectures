/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Finite-power coordinates detect preservation of finite limits

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, final sentence
(blueprint: lem-sfb-scalar-coordinate-limit-criterion).

Finite powers use the same constant-diagram/limit expression as the finite-free scalar
coordinate theorem. In particular the zeroth power is terminal, hence a zero object.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Mod

/-- The scalar-coordinate criterion in an abelian monoidal category. The first conjunct
records the additivity infrastructure supplied by the sheaf tensor dependency; the
universal quantifier over its proof permits the finite products of internal modules to
be used without a file-local instance. It imposes no additional hypothesis on the site.
The functor `Functor.const (Discrete (Fin n)) ⋙ lim` is the componentwise n-th power.

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, final sentence
(blueprint: lem-sfb-scalar-coordinate-limit-criterion).
-/
def ScalarCoordinateLimitCriterion
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  ∀ [MonoidalPreadditive H]
    (R B : H) [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (φ : R ⟶ B) [IsMonHom φ] (n : ℕ)
    (T : Mod H R ⥤ Mod H B)
    (_α : T ⋙ comap φ ≅ Functor.const (Discrete (Fin n)) ⋙ lim),
    PreservesFiniteLimits T

/-- A functor between internal module categories of abelian sheaves preserves finite
limits if, after scalar restriction, it is naturally a finite-power functor.
This includes the zeroth power and the empty limit diagram.

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, final sentence
(blueprint: lem-sfb-scalar-coordinate-limit-criterion).

Proof:
1. The canonical sheaf tensor is closed by `sfbSheafTensor_properties`, hence additive
by `sfbSheafTensor_monoidalPreadditive`. Work with the arbitrary monoidal-additivity
instance quantified in the criterion.
2. Internal-module forgetful functors create limits by the source library's
`CategoryTheory.Mod.createsLimit`. Thus they preserve and reflect finite limits,
and finite powers exist without passage to sectionwise module sheaves.
3. The constant-diagram functor preserves limits. The limit functor is a right adjoint,
so it also preserves limits. Their composite, the n-th power functor, therefore
preserves finite limits, including n = 0. Transport preservation across α inverse.
4. Restriction followed by forgetting is definitionally the original forgetful functor.
Consequently T followed by the B-module forgetful functor preserves finite limits.
Cancel that forgetful functor, which reflects finite limits by step 2. This also
handles empty diagrams.
-/
theorem sheaf_scalarCoordinateLimitCriterion
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @ScalarCoordinateLimitCriterion (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  let : HasSheafify J Ab.{w} := hasSheafifyEssentiallySmallSite J Ab.{w}
  let t := sfbSheafTensorStructure (A := Ab.{w}) J
  let : MonoidalCategory (Sheaf J Ab.{w}) := t.monoidal
  let : SymmetricCategory (Sheaf J Ab.{w}) := t.symmetric
  obtain ⟨closed⟩ := (sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0} (A := Ab.{w}) J).2.1
  let : MonoidalClosed (Sheaf J Ab.{w}) := closed
  refine ⟨⟨sfbSheafTensor_monoidalPreadditive⟩, ?_⟩
  intro h R B _ _ _ _ φ _ n T α
  have : PreservesFiniteLimits (Functor.const (Discrete (Fin n)) ⋙
      (lim : (Discrete (Fin n) ⥤ Mod (Sheaf J Ab.{w}) R) ⥤ _)) := inferInstance
  have : PreservesFiniteLimits (T ⋙ comap φ) :=
    preservesFiniteLimits_of_natIso α.symm
  have : PreservesFiniteLimits (forget R : Mod (Sheaf J Ab.{w}) R ⥤ _) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (T ⋙ (forget B : Mod (Sheaf J Ab.{w}) B ⥤ _)) :=
    inferInstanceAs (PreservesFiniteLimits ((T ⋙ comap φ) ⋙ forget R))
  have : ReflectsFiniteLimits (forget B : Mod (Sheaf J Ab.{w}) B ⥤ _) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves T (forget B)

end CategoryTheory.Mod
