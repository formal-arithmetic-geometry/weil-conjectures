/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.CategoryTheory.BraidedSheafTensorGenerators
import Sheaf.CategoryTheory.SheafTensorUnitComparison

/-!
# Regular scalar extension and multiplication

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-change-of-scalars/`,
`def-sfb-modobj-extension.md` and its proof, regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)

/-- The specified sheafified tensor, specialized to abelian sheaves.
Source: blueprint `sk-def-sfb-sheaf-tensor`, as used in the regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbMonoidal : MonoidalCategory (Sheaf J Ab.{w}) :=
  (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal

/-- The symmetry of the specified tensor on abelian sheaves.
Source: blueprint `sk-def-sfb-sheaf-tensor`, regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbSymmetric : SymmetricCategory (Sheaf J Ab.{w}) :=
  (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric

/-- Left tensor preserves the small colimits used for balancing.
Source: blueprint `sk-def-sfb-sheaf-tensor`, clause 2
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbTensorLeft (F : Sheaf J Ab.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
  ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 F).1

/-- Right tensor preserves the small colimits used for balancing.
Source: blueprint `sk-def-sfb-sheaf-tensor`, clause 2
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbTensorRight (F : Sheaf J Ab.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
  ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 F).2.1

/-- The canonical presheaf-to-sheaf tensor generator map.
Source: blueprint `def-sfb-modobj-extension`, local generator interpretation
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable def sfbRegularTensorGenerators (F G : Sheaf J Ab.{w}) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify J (F.obj ⊗ G.obj) ≫ (sfbSheafTensor_comparison J F G).inv.hom

/-- Evaluate a map from the tensor unit as a compatible family of sections.
The integer 1 first enters the sheafified constant integer sheaf by its actual unit map.
Source: blueprint `def-sfb-modobj-extension`, global-section interpretation
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable def sfbRegularSection (F : Sheaf J Ab.{w})
    (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) (U : Cᵒᵖ) : F.obj.obj U :=
  t.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ Ab.{w}))).app U (ULift.up (1 : ℤ)))

/-- Normalization of extension on regular modules, including multiplication by every
compatible global section. Source: blueprint `def-sfb-modobj-extension.md` and its proof,
regular-module specialization (blueprint: lem-sfb-regular-scalar-extension-multiplication).

Proof, following the node:
1. Abelian sheaf coequalizers are sheafifications of the objectwise cokernels of the
parallel difference. Their projections are epimorphisms; so are their tensors, since
both tensor functors preserve colimits (`sk-def-sfb-sheaf-tensor`,
`def-weil-pbc-sheafification`, `def-weil-pbc-category-colimit`).
2. The right R-action on S is S tensor phi followed by multiplication. Its unit,
associativity and compatibility with the left S-action follow from the ring-object
axioms. The balancing pair is exactly that of `def-sfb-modobj-extension` on regular R.
3. Apply `lem-sfb-mixed-bimodule-right-unitor` to this S-R-bimodule. Its forward map
composed with the balancing projection is the right action. Its inverse inserts the
unit of R. Uniqueness of the coequalizer factorization identifies this with the specified
extension object and its first-factor S-action, even if coequalizer choices differ.
4. Precompose with the presheaf tensor generators of
`lem-sfb-braided-sheaf-tensor-generators`. The forward formula becomes b phi(a).
The right-unitor comparison of `lem-sfb-sheaf-tensor-unit-comparison`, with
`det-def-sfb-sheaf-tensor-structure`, identifies the inverse with b tensor 1.
These tests assert equalities of sheaf maps, not pure-tensor generation of sections.
5. The left-unitor comparison identifies `extendUnitHom` with a mapped to 1 tensor a.
The left unit law of S and the multiplication compatibility of phi give q iota = phi.
6. Maps from the sheafified constant integers are compatible families, by the unit Hom
bijection in `lem-sfb-braided-sheaf-tensor-generators`. Multiplication by such a map t
is left-unitor inverse, followed by t tensor R and multiplication. Its section formula
is multiplication by t_U. Associativity and commutativity of R give R-linearity;
the same argument for S gives S-linearity for t followed by phi.
7. The induced map under extension is characterized after the balancing projection by
S tensor m_t. Precomposing the desired conjugation with that projection reduces it to
r(S tensor m_t) = m_phi(t) r. This follows from phi preserving multiplication and the
S-linearity in step 6. Cancel the epimorphic projection. No flatness, invertibility,
or final object of the site is used.
-/
theorem sfbRegularScalarExtensionMultiplication
    (R S : Sheaf J Ab.{w}) [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    ∃! q : (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S,
      Mod.extendπ φ (Mod.regular R) ≫ q.hom.hom = S ◁ φ ≫ μ[S] ∧
      q.inv.hom = (ρ_ S).inv ≫ S ◁ η[R] ≫ Mod.extendπ φ (Mod.regular R) ∧
      Mod.extendUnitHom φ (Mod.regular R) ≫ q.hom.hom = φ ∧
      (∀ (U : Cᵒᵖ) (b : S.obj.obj U) (a : R.obj.obj U),
        q.hom.hom.hom.app U
            ((Mod.extendπ φ (Mod.regular R)).hom.app U
              ((sfbRegularTensorGenerators J S R).app U (TensorProduct.tmul ℤ b a))) =
          μ[S].hom.app U ((sfbRegularTensorGenerators J S S).app U
            (TensorProduct.tmul ℤ b (φ.hom.app U a)))) ∧
      (∀ (U : Cᵒᵖ) (b : S.obj.obj U),
        q.inv.hom.hom.app U b =
          (Mod.extendπ φ (Mod.regular R)).hom.app U
            ((sfbRegularTensorGenerators J S R).app U
              (TensorProduct.tmul ℤ b (sfbRegularSection J R η[R] U)))) ∧
      (∀ (U : Cᵒᵖ) (a : R.obj.obj U),
        (Mod.extendUnitHom φ (Mod.regular R)).hom.app U a =
          (Mod.extendπ φ (Mod.regular R)).hom.app U
            ((sfbRegularTensorGenerators J S R).app U
              (TensorProduct.tmul ℤ (sfbRegularSection J S η[S] U) a))) ∧
      ∀ t : 𝟙_ (Sheaf J Ab.{w}) ⟶ R,
        ∃ mR : Mod.regular R ⟶ Mod.regular R,
        ∃ mS : Mod.regular S ⟶ Mod.regular S,
          mR.hom = (λ_ R).inv ≫ t ▷ R ≫ μ[R] ∧
          mS.hom = (λ_ S).inv ≫ (t ≫ φ) ▷ S ≫ μ[S] ∧
          (∀ (U : Cᵒᵖ) (a : R.obj.obj U),
            mR.hom.hom.app U a =
              μ[R].hom.app U ((sfbRegularTensorGenerators J R R).app U
                (TensorProduct.tmul ℤ (sfbRegularSection J R t U) a))) ∧
          (∀ (U : Cᵒᵖ) (b : S.obj.obj U),
            mS.hom.hom.app U b =
              μ[S].hom.app U ((sfbRegularTensorGenerators J S S).app U
                (TensorProduct.tmul ℤ (φ.hom.app U (sfbRegularSection J R t U)) b))) ∧
          (Mod.extendScalars φ).map mR ≫ q.hom = q.hom ≫ mS := by
  sorry

end CategoryTheory
