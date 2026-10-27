/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.FlatSingleScalarInterface

/-! # The ordinary action-preserving scalar comparison

Source: Stacks Project, Modules on Sites, Tag 03EK, and the module-object
coequalizer in blueprint change of scalars (2).
(blueprint: lem-sfb-ordinary-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped ChangeOfRings
namespace SheafOfModules.FlatSingleScalar
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]

/-- The ordinary extension comparison retains the given ring and module actions
and sends the balancing projection on local pure tensors to the canonical
sectionwise scalar-extension tensor.

Source: Stacks Project, Modules on Sites, Tag 03EK, and blueprint
change of scalars (2) (blueprint: lem-sfb-ordinary-scalar-comparison).

Proof: Construct the monoid B in R-module sheaves from its sectionwise
multiplication and the unit φ, using the binary tensor universal property.
Associativity and commutativity follow from the same identities in B, tested
on local pure triples and pairs. A sectionwise B-module gives an internal action
by the same binary universal property. Conversely, evaluate an internal action
on b tensor n to obtain its sectionwise B-action. Unit and associativity of the
internal action give the module laws, and restriction compatibility gives a
B-module presheaf with the original underlying abelian sheaf. These two
constructions are inverse on maps and objects up to the identity on underlying
R-modules. Modules over the tensor unit have the forced unitor action.
These constructions preserve addition of maps, so the transported extension
is additive.

For extension from the tensor unit, the two balancing arrows are equal by the
monoid right-unit law, the module left-unit law and the triangle identity.
Thus the actual coequalizer projection is an isomorphism. Its induced B-action
is multiplication on the first factor, by the defining equation after tensoring
the projection with B. On the section side, restricted changeOfRings sheafifies
the identical presheaf U maps to B(U) tensor over R(U) M(U). Restriction of
scalars commutes with sheafification since their underlying abelian sheafification
is the same. The identity of this presheaf therefore induces the comparison.
It is B-linear by its first-factor action; tensor generation and sheafification
uniqueness prove naturality. Finally transport through s.obj_eq and s.map_eq.
The sheafification unit gives exactly the displayed formula. This proof uses
no flatness assumption and no derived category. -/
theorem ordinary_scalar_comparison :
    ∃ d : Identifications φ, ∀ s : DerivedChangeOfRingsCochainModel φ,
      ∃ e : monExtension φ d ≅ s.E,
        ∀ (M : Modules R) (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
          ((eqToHom (s.obj_eq M)).val.app U)
            ((e.hom.app M).val.app U
              ((projection φ d M).val.app U
                (tensorSection (scalarAlgebra φ) M U b m))) =
          (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
            (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) := by sorry

end SheafOfModules.FlatSingleScalar
