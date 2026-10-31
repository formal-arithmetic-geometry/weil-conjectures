/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Intrinsic system triangle projection normal form

Source: blueprint composition/refinement sentence, intrinsic system repetition
(blueprint: lem-sf-triangle-projection-system-normal-form).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

/-- Finite type over the fixed field supplies local Noetherianity.
Source: Stacks 01T6 (blueprint: lem-sf-triangle-projection-system-normal-form). -/
instance spaceLocallyNoetherian (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    IsLocallyNoetherian X.obj.left :=
  @LocallyOfFiniteType.isLocallyNoetherian _ _ X.obj.hom X.property.1 inferInstance

/-- Finite type over the fixed field supplies compactness as well.
Source: Stacks 01T6 (blueprint: lem-sf-triangle-projection-system-normal-form). -/
instance spaceNoetherian (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    IsNoetherian X.obj.left where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := @QuasiCompact.compactSpace_of_compactSpace _ _ X.obj.hom
    X.property.2 inferInstance

end AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace WeilConjectures.IntegralSystemRealization.TriangleProjection

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : WeilConjectures.FiniteFieldDatum.{u})
  (o : Operations l E) (z : Realizations l E F o)
  {X V B Y D Z : AlgebraicGeometry.ProEtale.AmbientProperOpen.Spaces F}
  (j : X ⟶ V) (b : V ⟶ B) (i : Y ⟶ D)
  (q : V ⟶ Y) (p : B ⟶ D) (s : D ⟶ Z)
  [IsOpenImmersion j.hom.left] [IsOpenImmersion b.hom.left]
  [IsOpenImmersion i.hom.left]
  [IsProper q.hom.left] [IsProper p.hom.left] [IsProper s.hom.left]
  (h : b ≫ p = q ≫ i)

/-- The system object K', retaining every quotient transition.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-system-normal-form). -/
def systemInput (K : System l E X.obj.left) (L : System l E Z.obj.left) :=
  (calculus l E X.obj.left).systemClosed.tensor.obj
    (K, (pull l E j.hom.left).obj ((pull l E q.hom.left).obj
      ((pull l E i.hom.left).obj ((pull l E s.hom.left).obj L))))

/-- The system C, from the conjugate direct-image and open compositors.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-system-normal-form). -/
def systemC (N : System l E X.obj.left) :=
  (z.compositors.pushComp l E p.hom.left s.hom.left).hom.app
      ((Operations.shriek l E o b.hom.left).obj ((Operations.shriek l E o j.hom.left).obj N)) ≫
    (Operations.push l E o (p.hom.left ≫ s.hom.left)).map
      ((z.compositors.openComp l E j.hom.left b.hom.left).hom.app N)

/-- The intrinsic system triangle word, without evaluation or total limit.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-system-normal-form). -/
def systemLeft (K : System l E X.obj.left) (L : System l E Z.obj.left) :=
  ((properProjection l E o s.hom.left).app
    ((Operations.shriek l E o i.hom.left).obj
      ((Operations.push l E o q.hom.left).obj
        ((Operations.shriek l E o j.hom.left).obj K)))).app L ≫
    (Operations.push l E o s.hom.left).map
      ((z.openComparisons.projection i.hom.left).hom.app
        ((Operations.push l E o q.hom.left).obj
          ((Operations.shriek l E o j.hom.left).obj K), (pull l E s.hom.left).obj L)) ≫
    (Operations.push l E o s.hom.left).map ((Operations.shriek l E o i.hom.left).map
      (((properProjection l E o q.hom.left).app
        ((Operations.shriek l E o j.hom.left).obj K)).app
          ((pull l E i.hom.left).obj ((pull l E s.hom.left).obj L)) ≫
      (Operations.push l E o q.hom.left).map
        ((z.openComparisons.projection j.hom.left).hom.app
          (K, (pull l E q.hom.left).obj
            ((pull l E i.hom.left).obj ((pull l E s.hom.left).obj L)))))) ≫
    (Operations.push l E o s.hom.left).map
      ((z.properOpen.gamma b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h)).app
          ((Operations.shriek l E o j.hom.left).obj (systemInput l E F j i q s K L))) ≫
    systemC l E F o z j b p s (systemInput l E F j i q s K L)

/-- The intrinsic system normal word, including the canonical inverse square transport.
Only the pullback comparison is inverted.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-system-normal-form). -/
def systemRight (K : System l E X.obj.left) (L : System l E Z.obj.left) :=
  (calculus l E Z.obj.left).systemClosed.tensor.map
    (Prod.mkHom ((Operations.push l E o s.hom.left).map
      ((z.properOpen.gamma b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h)).app
          ((Operations.shriek l E o j.hom.left).obj K))) (𝟙 L)) ≫
    ((properProjection l E o s.hom.left).app
      ((Operations.push l E o p.hom.left).obj
        ((Operations.shriek l E o b.hom.left).obj
          ((Operations.shriek l E o j.hom.left).obj K)))).app L ≫
    (Operations.push l E o s.hom.left).map
      (((properProjection l E o p.hom.left).app
        ((Operations.shriek l E o b.hom.left).obj
          ((Operations.shriek l E o j.hom.left).obj K))).app ((pull l E s.hom.left).obj L)) ≫
    (Operations.push l E o s.hom.left).map ((Operations.push l E o p.hom.left).map
      ((z.openComparisons.projection b.hom.left).hom.app
        ((Operations.shriek l E o j.hom.left).obj K,
          (pull l E p.hom.left).obj ((pull l E s.hom.left).obj L)) ≫
      (Operations.shriek l E o b.hom.left).map
        ((calculus l E V.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 ((Operations.shriek l E o j.hom.left).obj K))
            ((z.compositors.square l E b.hom.left q.hom.left p.hom.left i.hom.left
              (congrArg (fun f ↦ f.hom.left) h)).inv.app ((pull l E s.hom.left).obj L)))) ≫
      (Operations.shriek l E o b.hom.left).map
        ((z.openComparisons.projection j.hom.left).hom.app
          (K, (pull l E q.hom.left).obj
            ((pull l E i.hom.left).obj ((pull l E s.hom.left).obj L)))))) ≫
    systemC l E F o z j b p s (systemInput l E F j i q s K L)

end WeilConjectures.IntegralSystemRealization.TriangleProjection

namespace WeilConjectures.IntegralSystemRealization

end WeilConjectures.IntegralSystemRealization
