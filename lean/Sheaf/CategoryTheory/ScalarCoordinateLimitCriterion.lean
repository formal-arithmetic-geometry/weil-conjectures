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
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
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
1. The sheaf tensor dependency supplies additivity. Use
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` to compute internal-module
limits as limits of sectionwise module sheaves. By
`lem-weil-pbc-module-sheaves-limits-sectionwise`, their sections are compatible families
with componentwise action. The empty compatible-family module is zero and terminal.
2. Put V = Res_φ. By `def-sfb-modobj-restriction`, V leaves the underlying sheaf and
maps unchanged and precomposes the action with φ tensor identity. A limit and the
limit of its restriction have the same compatible-family sheaf and projections.
Joint monicity of the projections shows that the canonical comparison respects the
R-action. Its inverse is R-linear too, so V preserves finite limits, including the
empty one.
3. If a B-linear f becomes invertible under V, its underlying inverse g is B-linear:
from f γ_M = γ_N (B tensor f), compose with g and B tensor g to get
`g γ_N = γ_M (B tensor g)`. Thus V reflects isomorphisms.
4. Finite limits exist by step 1. Apply
`lem-sfb-conservative-left-exact-reflects-finite-limits` to steps 2 and 3: V reflects
finite limits.
5. For a limit cone (L,p_j) and a cone (Q,q_j) over the n-th powers, take its k-th
coordinates. For each k the limit of the original diagram gives a unique map Q → L.
Their product gives the unique map Q → L^n with the required composites. For n = 0,
all powers are terminal and the unique map is the lift. For the empty diagram, L is
terminal, and the same coordinatewise uniqueness applies. Thus the power functor
preserves finite limits.
6. Naturality of α transports every cone over V composed with T to a cone over the
power diagram. Compose its unique lift with α_L inverse to obtain the unique lift
for V composed with T. This is `lem-sfb-finite-exactness-nat-iso` applied to α inverse.
7. Apply `lem-sfb-finite-limit-preservation-cancellation` to T and V: the composite
preserves finite limits by step 6 and V reflects them by step 4. Hence T preserves
each finite limit cone, including the empty cone.
-/
theorem sheaf_scalarCoordinateLimitCriterion
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @ScalarCoordinateLimitCriterion (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  sorry

end CategoryTheory.Mod
