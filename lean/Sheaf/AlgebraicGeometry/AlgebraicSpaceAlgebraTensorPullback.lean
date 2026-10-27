/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization

/-!
# Tensor pullback of commutative algebra sheaves on algebraic spaces

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03D8; More on Morphisms of Spaces,
Tag 082E (blueprint: def-sfb-space-algebra-tensor-pullback).

The underlying module is the existing tensor pullback, with its specified local tensors.
Unit and multiplication on these tensors determine the algebra structure. The normalized
uniqueness assertion rules out an arbitrary functor or an arbitrary algebra structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The local tensor viewed in a commutative algebra via its underlying-module comparison.
Source: Stacks, Modules on Sites, Tags 03D7 and 03D8
(blueprint: def-sfb-space-algebra-tensor-pullback). -/
def algebraPullbackTensor (f : X ⟶ Y) (F : Y.CommAlgebraSheaf ⥤ X.CommAlgebraSheaf)
    (e : F ⋙ algebraModuleFunctor X ≅ algebraModuleFunctor Y ⋙ moduleTensorPullback f)
    (A : Y.CommAlgebraSheaf) (V : Y.EtaleSite) (q : ModuleChart f V)
    (b : X.structureSheaf.obj.obj (op q.left)) (a : A.right.obj.obj (op V)) :
    (F.obj A).right.obj.obj (op q.left) :=
  (e.inv.app A).val.app (op q.left) (moduleTensorSection f A.toModule V q b a)

/-- Algebra tensor pullback, with its canonical underlying module and tensor multiplication.
Source: Stacks, Modules on Sites, Tags 03D7 and 03D8; More on Morphisms of Spaces, Tag 082E
(blueprint: def-sfb-space-algebra-tensor-pullback). -/
structure AlgebraTensorPullbackModel (f : X ⟶ Y) where
  /-- Pullback on commutative algebra sheaves. -/
  functor : Y.CommAlgebraSheaf ⥤ X.CommAlgebraSheaf
  /-- The underlying module is the already specified tensor pullback, naturally in algebras. -/
  moduleIso : functor ⋙ algebraModuleFunctor X ≅
    algebraModuleFunctor Y ⋙ moduleTensorPullback f
  /-- The algebra unit is the local tensor of the two units. -/
  tensor_one (A : Y.CommAlgebraSheaf) (V : Y.EtaleSite) (q : ModuleChart f V) :
    algebraPullbackTensor f functor moduleIso A V q 1 1 = 1
  /-- Multiplication is the ordinary multiplication of local tensor factors. -/
  tensor_mul (A : Y.CommAlgebraSheaf) (V : Y.EtaleSite) (q : ModuleChart f V)
      (b c : X.structureSheaf.obj.obj (op q.left)) (a d : A.right.obj.obj (op V)) :
    algebraPullbackTensor f functor moduleIso A V q b a *
        algebraPullbackTensor f functor moduleIso A V q c d =
      algebraPullbackTensor f functor moduleIso A V q (b * c) (a * d)

/-- The algebra tensor construction exists and is determined up to the unique isomorphism
which preserves its comparison with the specified module pullback.
Source: Stacks, Modules on Sites, Tags 03D7 and 03D8; More on Morphisms of Spaces, Tag 082E
(blueprint: def-sfb-space-algebra-tensor-pullback).

Proof: use the enlarged ringed-site tensor realization of
lem-trf-space-chart-adjunction-tensor-realization. Before sheafification, the inverse
image of a commutative algebra is a commutative algebra over the inverse-image ring.
Extension of scalars has product (b tensor a)(c tensor d) = bc tensor ad and unit
1 tensor 1. Balanced multilinearity makes these operations well-defined; they commute
with restrictions and hence descend through sheafification. The same construction on
algebra maps gives a functor. Its underlying module is the existing scalar extension;
transport through the normalized chart comparison gives moduleIso and the displayed
local tensor formulas. For two models, moduleIso followed by the inverse comparison
is the unique possible underlying-module isomorphism. Locally all sections are sums of
local tensor generators, possibly after refining the etale cover. The two tensor laws
therefore make this map preserve multiplication and unit; linearity preserves scalars.
It is an algebra isomorphism and is natural by the naturality of the module comparisons.
Faithfulness of the underlying-module functor proves its asserted uniqueness. -/
theorem algebraTensorPullbackModel_exists (f : X ⟶ Y) :
    ∃ D : AlgebraTensorPullbackModel f, ∀ E : AlgebraTensorPullbackModel f,
      ∃! e : D.functor ≅ E.functor,
        ∀ A : Y.CommAlgebraSheaf,
          (algebraModuleFunctor X).map (e.hom.app A) ≫ E.moduleIso.hom.app A =
            D.moduleIso.hom.app A := by
  sorry

/-- The canonical algebra pullback, chosen only through its normalized uniqueness property.
Source: Stacks, Modules on Sites, Tags 03D7 and 03D8
(blueprint: def-sfb-space-algebra-tensor-pullback). -/
def algebraTensorPullbackModel (f : X ⟶ Y) : AlgebraTensorPullbackModel f :=
  (algebraTensorPullbackModel_exists f).choose

end AlgebraicGeometry.AlgebraicSpace
