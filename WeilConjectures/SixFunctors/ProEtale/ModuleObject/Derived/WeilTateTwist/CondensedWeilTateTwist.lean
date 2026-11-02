/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-! # Tate twists of ordinary condensed Weil pairs

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/def-wf-tate-twist.md
(blueprint: def-wf-tate-twist).

All coefficient lines and their root-normalized structures are the published ones.
The functors assemble them by the existing transport of invertible endofunctor algebras.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist

open PurityTransport StrictWeilCondensed

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
  {T : Scheme.{u}} (g : T ≅ T) [∀ x : T, Invertible (ell : T.residueField x)]

/-- Tensor with the signed Tate module. The structure uses the inverse tensorator
and the root-normalized Tate structure; maps tensor with the identity.
Source: def-wf-tate-twist.md, displayed tensor Weil map and morphism formula
(blueprint: def-wf-tate-twist). -/
def moduleTwist (m : ℤ) : WeilModule (c.obj ell) g ⥤ WeilModule (c.obj ell) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((Functor.Monoidal.commTensorRight (upperStar (c.obj ell) g.hom)
        (tateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (upperStar (c.obj ell) g.hom)
        ((tensoringRight _).mapIso (tatePull ell c g m)))

/-- Derived tensor with the actual Tate line in degree zero, with the two Weil
structures composed after the inverse derived tensorator.
Source: def-wf-tate-twist.md, K(m) and the displayed Weil map
(blueprint: def-wf-tate-twist). -/
def ambientTwist (m : ℤ) :
    CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g) ⥤
      CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((Functor.Monoidal.commTensorRight (action (c.obj ell) g)
        (derivedTateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (action (c.obj ell) g)
        ((tensoringRight _).mapIso (tateDatum ell c g m)))

/-- Tate tensor preserves constructibility and is exact on Weil modules.
Source: def-wf-tate-twist.md, final sentence (blueprint: def-wf-tate-twist).
Proof: the common root cover trivializes the signed Tate line, including its
negative powers by duality. On this cover, tensor by the line is isomorphic to
the identity on module carriers, so preserves constructibility, kernels and
cokernels. These properties descend. Weil-module kernels and cokernels are
computed on carriers with the induced tensor structure. Hence the functor
preserves finite limits and colimits. -/
theorem moduleTwist_properties (m : ℤ) :
    (∀ M : WeilModule (c.obj ell) g,
      IsConstructibleModuleObject (condensedRingObj (c.obj ell) T) M.carrier →
      IsConstructibleModuleObject (condensedRingObj (c.obj ell) T)
        (((moduleTwist ell c g m).obj M).carrier)) ∧
    PreservesFiniteLimits (moduleTwist ell c g m) ∧
    PreservesFiniteColimits (moduleTwist ell c g m) := by
  sorry

/-- Derived Tate tensor preserves bounded constructibility and cohomological bounds.
Source: def-wf-tate-twist.md, preservation and t-exactness clause
(blueprint: def-wf-tate-twist).
Proof: a locally free line is flat, so derived tensor by its single complex is
ordinary exact tensor on complexes. Its cohomology is the input cohomology
tensored with the same line, in the same degree. This preserves both bounds,
and constructibility is preserved locally on the common root cover. The Weil
structure equips these carriers with the specified tensor isomorphism. -/
theorem ambientTwist_properties (m : ℤ)
    (K : CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g)) :
    (boundedConstructible (condensedRingObj (c.obj ell) T) K.carrier →
      boundedConstructible (condensedRingObj (c.obj ell) T)
        (((ambientTwist ell c g m).obj K).carrier)) ∧
    (∀ n : ℤ, K.carrier.IsGE n → (((ambientTwist ell c g m).obj K).carrier).IsGE n) ∧
    (∀ n : ℤ, K.carrier.IsLE n → (((ambientTwist ell c g m).obj K).carrier).IsLE n) := by
  sorry

/-- The restriction to constructible Weil sheaves retains the ambient tensor maps.
Source: def-wf-tate-twist.md, constructible Weil heart
(blueprint: def-wf-tate-twist). -/
def heartTwist (m : ℤ) :
    WeilConjectures.condensedConstructibleWeilSheaves (c.obj ell) g.hom ⥤
      WeilConjectures.condensedConstructibleWeilSheaves (c.obj ell) g.hom :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ moduleTwist ell c g m)
    (fun M ↦ (moduleTwist_properties ell c g m).1 M.obj M.property)

/-- Tate twisting in the bounded constructible strict-pair category.
Source: def-wf-tate-twist.md, twist of a Weil complex
(blueprint: def-wf-tate-twist). -/
def strictTwist (m : ℤ) :
    WeilConjectures.condensedStrictWeilComplex (c.obj ell) g.hom ⥤
      WeilConjectures.condensedStrictWeilComplex (c.obj ell) g.hom :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ambientTwist ell c g m)
    (fun K ↦ (ambientTwist_properties ell c g m K.obj).1 K.property)

/-- The restriction of Tate tensor is exact on the constructible Weil heart.
Source: def-wf-tate-twist.md, final sentence (blueprint: def-wf-tate-twist).
Proof: constructible Weil sheaves form an abelian full subcategory with kernels
and cokernels computed on carriers. The ambient exactness and preservation of
constructibility in moduleTwist_properties therefore restrict to this heart. -/
theorem heartTwist_exact (m : ℤ) :
    PreservesFiniteLimits (heartTwist ell c g m) ∧
    PreservesFiniteColimits (heartTwist ell c g m) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist
