/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-! # The category of flat finitely presented modules with proper support

Source: Stacks Project, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli).

The objects, pullback-isomorphism arrows, identities and composites have concrete data.
Proper support is a property, expressed by a closed-pushforward presentation. Only the
category-law proof for the canonical tensor-pullback operations is postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The objects of the coherent-family category over schemes over `S`.
Source: Stacks, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli). -/
structure FlatCoherentModuli {X S : Scheme.{u}} (f : X ⟶ S) where
  base : Over S
  module : (pullback f base.hom).Modules
  quasiCoherent : module.IsQuasicoherent
  finitePresentation : module.IsFinitePresentation
  flat : ∀ x : ↥(pullback f base.hom),
    Module.Flat (base.left.presheaf.stalk ((pullback.snd f base.hom) x))
      ((ModuleCat.restrictScalars ((pullback.snd f base.hom).stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor (pullback f base.hom).toRingedSpace x).obj module))
  properSupport : ∃ (Z : Scheme.{u}) (i : Z ⟶ pullback f base.hom),
    IsClosedImmersion i ∧ IsProper (i ≫ pullback.snd f base.hom) ∧
      ∃ G : Z.Modules, G.IsQuasiCoherentFiniteType ∧
        Nonempty ((Scheme.Modules.pushforward i).obj G ≅ module)

namespace FlatCoherentModuli

/-- An arrow over `u` is the specified isomorphism `u_X^* F₁ ≅ F`.
Source: Stacks, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli). -/
structure Hom {X S : Scheme.{u}} {f : X ⟶ S} (A B : FlatCoherentModuli f) where
  base : A.base ⟶ B.base
  iso : (Scheme.Modules.moduleBaseChange f base).obj B.module ≅ A.module

/-- The identity arrow uses the canonical identity tensor-pullback comparison.
Source: Stacks, quot.tex, Situation 08KB; Sheaves, Tag 0097
(blueprint: def-sfb-flat-coherent-moduli). -/
def identity {X S : Scheme.{u}} {f : X ⟶ S} (A : FlatCoherentModuli f) : Hom A A where
  base := 𝟙 A.base
  iso := eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj A.module)
      (baseChangeMap_id f A.base)) ≪≫
    (Scheme.Modules.tensorPullbackSectionId _).app A.module

/-- Compose the actual isomorphisms by the normalized composite-pullback comparison.
Source: Stacks, quot.tex, Situation 08KB; Sheaves, Tag 0097
(blueprint: def-sfb-flat-coherent-moduli). -/
def composition {X S : Scheme.{u}} {f : X ⟶ S} {A B C : FlatCoherentModuli f}
    (a : Hom A B) (b : Hom B C) : Hom A C where
  base := a.base ≫ b.base
  iso := eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj C.module)
      (baseChangeMap_comp f a.base b.base)) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp
      (baseChangeMap f a.base) (baseChangeMap f b.base)).app C.module ≪≫
    (Scheme.Modules.moduleBaseChange f a.base).mapIso b.iso ≪≫ a.iso

/-- The specified operations obey the category laws.
Source: Stacks, quot.tex, Situation 08KB; Sheaves, Tag 0097
(blueprint: def-sfb-flat-coherent-moduli).
Proof: the base components satisfy the category laws in `Over S`. On the module
components, evaluate the normalized adjunction comparisons on `1 tensor m`.
The two identity comparisons act identically, and both associations of three
pullbacks send a pure tensor to the same iterated tensor. Such tensors locally
generate the sheaves, so these maps agree. The inverse maps then agree too.
Together with baseChangeMap_id and baseChangeMap_comp this gives the three laws.
Only proof fields of the explicitly constructed category are postponed. -/
theorem category_laws {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ {A B : FlatCoherentModuli f} (a : Hom A B),
      composition (identity A) a = a) ∧
    (∀ {A B : FlatCoherentModuli f} (a : Hom A B),
      composition a (identity B) = a) ∧
    (∀ {A B C D : FlatCoherentModuli f} (a : Hom A B) (b : Hom B C) (c : Hom C D),
      composition (composition a b) c = composition a (composition b c)) := by
  sorry

/-- The category structure with the actual identity and composition just specified.
Source: Stacks, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli). -/
instance {X S : Scheme.{u}} {f : X ⟶ S} : Category (FlatCoherentModuli f) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := (category_laws f).1
  comp_id := (category_laws f).2.1
  assoc := (category_laws f).2.2

/-- Projection retaining the base arrow of each pullback isomorphism.
Source: Stacks, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli). -/
def forget {X S : Scheme.{u}} (f : X ⟶ S) : FlatCoherentModuli f ⥤ Over S where
  obj A := A.base
  map a := a.base

/-- The concrete category over `S`-schemes of flat finitely presented modules with
proper support. Source: Stacks, quot.tex, Situation 08KB
(blueprint: def-sfb-flat-coherent-moduli). -/
def category {X S : Scheme.{u}} (f : X ⟶ S) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forget f)

end FlatCoherentModuli

end AlgebraicGeometry
