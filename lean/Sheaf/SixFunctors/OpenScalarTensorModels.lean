/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.OpenScalarTensorData

/-! # Scalar tensor models compatible with open restriction 

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0D6D and 0GL1;
sites-modules.tex, Tag 0E8I
(blueprint: lem-sp-canonical-open-scalar-tensor-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The two scalar tensor facts needed to compare projection adjuncts.
Source: Stacks 07A4 and 07A6
(blueprint: lem-sp-canonical-open-scalar-tensor-models). -/
structure TensorCompatibility (m : Models.{u}) (c : Choices m) where
  scalar_projection_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A), IsIso (scalarProjection m c φ T K)
  lambda_tensor : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F Q : proEtaleDerivedCategory X A),
    (tensor m B U).map
        (Prod.mkHom ((lambda m φ j).inv.app F) ((lambda m φ j).inv.app Q)) ≫
      (restrictionTensor m B j).inv.app ((scalar m φ X).obj F, (scalar m φ X).obj Q) ≫
      (constantPullback (A := B) j).map ((c.scalarTensor φ X).iso.inv.app (F, Q)) =
    (c.scalarTensor φ U).iso.inv.app
        ((constantPullback (A := A) j).obj F, (constantPullback (A := A) j).obj Q) ≫
      (scalar m φ U).map ((restrictionTensor m A j).inv.app (F, Q)) ≫
      (lambda m φ j).inv.app ((tensor m A X).obj (F, Q))

/-- Canonical scalar tensor models compatible with open inverse image.
Source: Stacks, sites-cohomology.tex, Tags 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-canonical-open-scalar-tensor-models).

Proof: choose the closed symmetric monoidal structures with their representative
coherence from `ringedDerived_closed_symmetric_monoidal`, and the normalized
extension/restriction derived pairs. The normalized scalar tensor comparison gives
`scalarTensor`. For open inverse image, descend the sectionwise tensor and unit
comparisons along flat-term K-flat resolutions. Associativity and the two unit
laws hold on pure-tensor summands, hence after descent. This gives `openMonoidal`
with its prescribed tensorator. To compare scalar extension with tensoring by the
restricted B unit, resolve the first factor by a K-flat complex. The scalar
adjunct in `scalarProjection` sends x tensor b to b tensor x. Its inverse is
x tensor b in the same representative model, so the displayed map is invertible.
Finally both factorizations of pullback along (U,B) to (X,A) send a pure tensor
to the same balanced tensor. Their totalized maps preserve each bidegree, so no
additional sign occurs. Fully faithful restriction to resolving representatives
makes the two inverse tensorator composites equal on arbitrary derived objects.
The construction applies to empty opens, zero rings and nonflat ring maps. -/
theorem open_scalar_tensor_models :
    ∃ m : Models.{u}, ∃ c : Choices m, Nonempty (TensorCompatibility m c) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenScalarTensor
