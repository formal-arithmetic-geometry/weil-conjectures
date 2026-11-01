/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs

/-!
# The root-normalized Tate-twist functor

Source: latest blueprint, def-wf-tate-twist, signed lines, Weil structure, and
exactness paragraphs (blueprint: def-wf-tate-twist).

The coefficient presentation runs through the six published admissible coefficient
rings. The signed line, including its finite-root, inverse-limit, scalar-extension,
and dual constructions, is the published line of sk-def-sp-tate-twist. Its Weil
map is the published root-normalized map. These definitions only assemble tensor
with that specified line; they choose no line or Weil isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist

open StrictWeilCondensed

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)
  {T : Scheme.{u}} (g : T ≅ T)
  [∀ x : T, Invertible (ell : T.residueField x)]

/-- The inverse tensorator followed by the root-normalized Tate map.
Source: def-wf-tate-twist, displayed Weil structure (blueprint: def-wf-tate-twist). -/
def ordinaryComparison (m : ℤ) :
    tensorRight (tateLine ell c T m) ⋙ upperStar (c.obj ell) g.hom ≅
      upperStar (c.obj ell) g.hom ⋙ tensorRight (tateLine ell c T m) :=
  (Functor.Monoidal.commTensorRight (upperStar (c.obj ell) g.hom)
    (tateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (upperStar (c.obj ell) g.hom)
        ((tensoringRight _).mapIso (tatePull ell c g m))

/-- Ordinary tensor with the actual signed Tate line on Weil modules.
On objects the Weil map is the inverse tensorator followed by phi tensor tau;
on arrows the carrier map is h tensor id.
Source: def-wf-tate-twist, displayed formula and morphisms
(blueprint: def-wf-tate-twist). -/
def ordinary (m : ℤ) : WeilModule (c.obj ell) g ⥤ WeilModule (c.obj ell) g :=
  Endofunctor.IsoAlgebra.mapOfNatIso (ordinaryComparison ell c g m)

/-- The same comparison in the ordinary unbounded derived category.
Source: def-wf-tate-twist, derived tensor formula (blueprint: def-wf-tate-twist). -/
def derivedComparison (m : ℤ) :
    tensorRight (derivedTateLine ell c T m) ⋙ action (c.obj ell) g ≅
      action (c.obj ell) g ⋙ tensorRight (derivedTateLine ell c T m) :=
  (Functor.Monoidal.commTensorRight (action (c.obj ell) g)
    (derivedTateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (action (c.obj ell) g)
        ((tensoringRight _).mapIso (tateDatum ell c g m))

/-- Derived tensor with the signed Tate line, with its specified Weil datum.
Source: def-wf-tate-twist, K(m) and its Weil structure
(blueprint: def-wf-tate-twist). -/
def derived (m : ℤ) :
    Endofunctor.IsoAlgebra (action (c.obj ell) g) ⥤
      Endofunctor.IsoAlgebra (action (c.obj ell) g) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (derivedComparison ell c g m)

/-- The signed line is locally free of rank one, so tensor with it preserves
constructibility and lisseness, and is exact on the ambient Weil-module category.
Source: def-wf-tate-twist, final paragraph (blueprint: def-wf-tate-twist).
Proof: compatible primitive-root covers trivialize the finite root line and its
inverse limit. Scalar extension trivializes E and Qbar lines on the same covers.
The coefficient unit, tensor powers and duals remain rank one. After a common
refinement, tensor with this line preserves each finite constant local model.
It preserves kernels and cokernels since locally it is tensor with the coefficient
unit. Pullback by the automorphism is exact, and the Weil-module forgetful functor
creates kernels and cokernels, so the same exactness holds for Weil modules. -/
theorem ordinary_properties (m : ℤ) :
    PreservesFiniteLimits (ordinary ell c g m) ∧
    PreservesFiniteColimits (ordinary ell c g m) ∧
    ∀ F : WeilModule (c.obj ell) g,
      (IsConstantModelConstructible (c.obj ell) T F.carrier →
        IsConstantModelConstructible (c.obj ell) T
          ((ordinary ell c g m).obj F).carrier) ∧
      (IsLisseCoefficientModule (c.obj ell) F.carrier →
        IsLisseCoefficientModule (c.obj ell) ((ordinary ell c g m).obj F).carrier) := by
  sorry

/-- Restriction to constructible Weil sheaves uses the proved carrier predicate.
Source: def-wf-tate-twist, exact heart restriction (blueprint: def-wf-tate-twist). -/
def heart (m : ℤ) :
    (ObjectProperty.FullSubcategory (fun F : WeilModule (c.obj ell) g ↦
      IsConstantModelConstructible (c.obj ell) T F.carrier)) ⥤
    (ObjectProperty.FullSubcategory (fun F : WeilModule (c.obj ell) g ↦
      IsConstantModelConstructible (c.obj ell) T F.carrier)) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ordinary ell c g m)
    (fun F ↦ ((ordinary_properties ell c g m).2.2 F.obj).1 F.property)

/-- Derived twisting preserves bounded constructible inputs and the standard
cohomological bounds, expressing t-exactness without a new category of complexes.
Source: def-wf-tate-twist, bounded constructibility and t-exactness
(blueprint: def-wf-tate-twist).
Proof: the signed line is flat of rank one. Tensor with it has no higher Tor,
commutes with homology, and preserves finite constant local models on each stratum.
It therefore preserves bounded constructibility and every upper and lower bound. -/
theorem derived_properties (m : ℤ)
    (K : Endofunctor.IsoAlgebra (action (c.obj ell) g)) :
    (constantModelBoundedConstructible (c.obj ell) T K.carrier →
      constantModelBoundedConstructible (c.obj ell) T ((derived ell c g m).obj K).carrier) ∧
    (∀ n : ℤ, (K.carrier.IsLE n → ((derived ell c g m).obj K).carrier.IsLE n) ∧
      (K.carrier.IsGE n → ((derived ell c g m).obj K).carrier.IsGE n)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist
