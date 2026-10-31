/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Geometric single-complex base-change condition
Source: Stacks Project, spaces-perfect.tex, equation-bc before Tag 0DKG.
(blueprint: def-sfb-space-single-complex-stalk-condition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex
variable {S : Scheme.{u}}
variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]

variable {X X' Y Y' : AlgebraicSpace S}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- The base geometric stalk ring, using the compositional path through X.
Source: Stacks equation-bc before 0DKG
(blueprint: def-sfb-space-single-complex-stalk-condition). -/
abbrev R {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :=
  stalkRing s ((x ≫ g'.hom.hom) ≫ f.hom.hom)

/-- The R-algebra structure on the original geometric stalk ring.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
@[instance_reducible] def leftAlgebra {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :
    Algebra (R f g' s x) (stalkRing s (x ≫ g'.hom.hom)) :=
  (stalkMap f s (x ≫ g'.hom.hom)).toAlgebra

include sq in
/-- The two paths around a cartesian square define the same geometric point.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition).
Proof: apply the underlying natural-transformation map to the square equation,
precompose with x, and use associativity of composition. -/
theorem point_square {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :
    (x ≫ g'.hom.hom) ≫ f.hom.hom = (x ≫ f'.hom.hom) ≫ g.hom.hom := by
  sorry

/-- The R-algebra structure on the new base stalk, transported along the square equation.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
@[instance_reducible] def rightAlgebra {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :
    Algebra (R f g' s x) (stalkRing s (x ≫ f'.hom.hom)) :=
  ((stalkMap g s (x ≫ f'.hom.hom)).comp
    (CommRingCat.Hom.hom (eqToHom (congrArg (stalkRing s)
      (point_square f f' g g' sq s x))))).toAlgebra

/-- The tensor-to-stalk map is uniquely determined by the two projection stalk maps.
Source: Stacks equation-bc before 0DKG
(blueprint: def-sfb-space-single-complex-stalk-condition).
Proof: the germ normalization makes stalk ring maps functorial. The square equation
therefore makes their composites from R equal. The universal property of the
commutative algebra tensor product gives the unique map with these restrictions. -/
theorem tensorMap_existsUnique {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :
    letI := leftAlgebra f g' s x
    letI := rightAlgebra f f' g g' sq s x
    ∃! h : stalkRing s (x ≫ g'.hom.hom) ⊗[R f g' s x]
        stalkRing s (x ≫ f'.hom.hom) →+* stalkRing s x,
      h.comp (algebraMap _ _) = stalkMap g' s x ∧
        h.comp Algebra.TensorProduct.includeRight.toRingHom = stalkMap f' s x := by
  sorry

/-- The canonical ring map A tensor-over-R B to C.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
def tensorMap {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) :=
  letI := leftAlgebra f g' s x
  letI := rightAlgebra f f' g g' sq s x
  Classical.choose (tensorMap_existsUnique f f' g g' sq s x)

/-- The complex of geometric stalks of P, with its actual A-action.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
def stalkComplex {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) (P : CochainComplex X.SmallModules ℤ) :=
  ((stalk s (x ≫ g'.hom.hom)).mapHomologicalComplex (.up ℤ)).obj P

/-- Ordinary scalar extension of this stalk complex along the projection map A to C.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
def extendedStalkComplex {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj)
    (P : CochainComplex X.SmallModules ℤ) :=
  ((ModuleCat.extendScalars (stalkMap g' s x)).mapHomologicalComplex (.up ℤ)).obj
    (stalkComplex g' s x P)

/-- The normalized tensor pullback-stalk chain isomorphism.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
def tensorStalkIso {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) (P : CochainComplex X.SmallModules ℤ) :
    extendedStalkComplex g' s x P ≅
      ((stalk s x).mapHomologicalComplex (.up ℤ)).obj
        (((pullback g').mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex (smallPullbackStalkIso g' s x) (.up ℤ)).app P

/-- The existing base-derived tensor cohomology model with these geometric stalk rings.
Source: Stacks equation-bc before 0DKG, More on Algebra 06Y6 and 08IB
(blueprint: def-sfb-space-single-complex-stalk-condition). -/
def cohomologyModel {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) (P : CochainComplex X.SmallModules ℤ) :=
  letI := leftAlgebra f g' s x
  letI := rightAlgebra f f' g g' sq s x
  letI := (tensorMap f f' g g' sq s x).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' s x))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (stalkRing s (x ≫ f'.hom.hom)))
  ModuleCat.baseDerivedTensorCohomologyModel (R f g' s x)
    (stalkRing s (x ≫ g'.hom.hom)) (stalkRing s (x ≫ f'.hom.hom))
    (stalkComplex g' s x P) (stalkRing s x)

/-- The tensor-map restriction equation gives the canonical complex identification.
Source: Stacks 0DKG (blueprint: def-sfb-space-single-complex-stalk-condition). -/
def extendedStalkCongr {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj)
    (P : CochainComplex X.SmallModules ℤ) :
    letI := leftAlgebra f g' s x
    letI := rightAlgebra f f' g g' sq s x
    ((ModuleCat.extendScalars ((tensorMap f f' g g' sq s x).comp
      (algebraMap _ _))).mapHomologicalComplex (.up ℤ)).obj (stalkComplex g' s x P) ≅
        extendedStalkComplex g' s x P :=
  letI := leftAlgebra f g' s x
  letI := rightAlgebra f f' g g' sq s x
  eqToIso (congrArg (fun h : stalkRing s (x ≫ g'.hom.hom) →+* stalkRing s x ↦
    ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj (stalkComplex g' s x P))
      (Classical.choose_spec (tensorMap_existsUnique f f' g g' sq s x)).1.1)

/-- The equation-bc comparison: derived-to-ordinary base scalar extension on cohomology,
followed by the specified tensor-stalk isomorphism and the stalk of the given chain map.
Source: Stacks equation-bc before 0DKG
(blueprint: def-sfb-space-single-complex-stalk-condition). -/
def comparison {K : X.DerivedModules} {K' : X'.DerivedModules}
    {φ : (derivedPullback g').obj K ⟶ K'} (c : Coordinates g' K K' φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) (i : ℤ) :=
  letI := leftAlgebra f g' s x
  letI := rightAlgebra f f' g g' sq s x
  letI := (tensorMap f f' g g' sq s x).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' s x))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (stalkRing s (x ≫ f'.hom.hom)))
  (cohomologyModel f f' g g' sq s x c.P).localizedComparison i ≫
    HomologicalComplex.homologyMap (extendedStalkCongr f f' g g' sq s x c.P).hom i ≫
    HomologicalComplex.homologyMap (tensorStalkIso g' s x c.P).hom i ≫
    HomologicalComplex.homologyMap
      (((stalk s x).mapHomologicalComplex (.up ℤ)).map c.t) i

/-- The comparison is invertible at every geometric point in every integer degree.
All flat-term K-flat coordinates are allowed; their counit equation fixes the same
canonical map, and they exist by coordinates_nonempty.
Source: Stacks equation-bc before 0DKG
(blueprint: def-sfb-space-single-complex-stalk-condition). -/
def StalkCondition (K : X.DerivedModules) (K' : X'.DerivedModules)
    (φ : (derivedPullback g').obj K ⟶ K') : Prop :=
  ∀ (c : Coordinates g' K K' φ) (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj) (i : ℤ),
    IsIso (comparison f f' g g' sq c s x i)

end AlgebraicGeometry.AlgebraicSpace.SingleComplex
