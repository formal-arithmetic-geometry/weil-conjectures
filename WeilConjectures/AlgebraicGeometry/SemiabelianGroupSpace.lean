/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularGroupSpace
public import WeilConjectures.AlgebraicGeometry.RelativeTorus
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Semiabelian group algebraic spaces over an algebraically closed field

Source: Deligne, Le lemme de Gabber, Section 1.1, p.131, specialized to a field;
Milne, Algebraic Groups, Section 12, for the split torus
(blueprint: def-sfb-semiabelian-group-space).

The space is the project's algebraic space with its natural commutative group law
(`AlgebraicSpace.CommutativeSpaceGroup`). Smoothness, separatedness and finite type are the
existing étale-chart and diagonal tests on the structure map to the base.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonObj

namespace AlgebraicGeometry

/-- The additive notation for the group of points of a commutative group scheme.
This is the usual group-valued Yoneda presheaf, with its commutativity retained.
Source: Deligne, Section 1.1, p.131 (blueprint: def-sfb-semiabelian-group-space). -/
def commutativeGroupSchemeAdditivePoints {S : Scheme.{u}} (A : Over S)
    [GrpObj A] [IsCommMonObj A] : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  { obj := fun U ↦ CommGrpCat.of (U.unop ⟶ A)
    map := fun f ↦ CommGrpCat.ofHom ((yonedaGrpObj A).map f).hom } ⋙
      CommGrpCat.toAddCommGrp

/-- The functor of points of an algebraic space with a natural commutative group law, valued in
commutative groups: on a test scheme it is the given group of points, and restriction is the
given restriction map, a group homomorphism by the law's naturality.
Source: Deligne, Section 1.1, p.131 (blueprint: def-sfb-semiabelian-group-space). -/
def commutativeSpaceGroupPoints {S : Scheme.{u}} {G : AlgebraicSpace S}
    (g : AlgebraicSpace.CommutativeSpaceGroup G) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := @CommGrpCat.of (G.obj.obj.obj T) (g.group T)
  map {T U} f :=
    letI := g.group T
    letI := g.group U
    CommGrpCat.ofHom
      { toFun := G.obj.obj.map f
        map_one' := g.map_one f
        map_mul' := g.map_mul f }
  map_id T := by
    let _ := g.group T
    ext x
    exact ConcreteCategory.congr_hom (G.obj.obj.map_id T) x
  map_comp {T U V} f h := by
    let _ := g.group T
    let _ := g.group V
    ext x
    exact ConcreteCategory.congr_hom (G.obj.obj.map_comp f h) x

/-- A smooth separated finite-type commutative group algebraic space over `k` which is an exact
fppf extension of an abelian variety by a split torus. Smoothness, separatedness and finite type
are the étale-chart and closed-diagonal tests on the structure map to `Spec k`. Pointwise
injectivity and exactness identify the torus with the sheaf kernel; local surjectivity is the
fppf lifting condition. Rank zero is allowed.
Source: Deligne, Le lemme de Gabber, Section 1.1, p.131, over an algebraically closed field
(blueprint: def-sfb-semiabelian-group-space). -/
def IsSemiabelianGroupSpace {k : Type u} [Field k] [IsAlgClosed k]
    {G : AlgebraicSpace (Spec (.of k))} (g : AlgebraicSpace.CommutativeSpaceGroup G) : Prop :=
  AlgebraicSpace.MapIsLocally @Smooth (AlgebraicSpace.groupSpaceProjection G) ∧
  AlgebraicSpace.MapIsSeparated (AlgebraicSpace.groupSpaceProjection G) ∧
  AlgebraicSpace.MapIsFiniteType (AlgebraicSpace.groupSpaceProjection G) ∧
  ∃ (r : ℕ) (A : Over (Spec (.of k))) (_ : GrpObj A)
    (_ : IsCommMonObj A) (_ : IsAbelianVariety A)
    (i : relativeSplitTorusFunctor (Spec (.of k)) r ⟶
      commutativeSpaceGroupPoints g ⋙ forget₂ CommGrpCat GrpCat)
    (q : commutativeSpaceGroupPoints g ⋙ CommGrpCat.toAddCommGrp ⟶
      commutativeGroupSchemeAdditivePoints A),
    (∀ U : (Over (Spec (.of k)))ᵒᵖ,
      Function.Injective (i.app U).hom ∧
      ∀ x : (commutativeSpaceGroupPoints g ⋙ CommGrpCat.toAddCommGrp).obj U,
        (q.app U).hom x = 0 ↔
          ∃ t : (relativeSplitTorusFunctor (Spec (.of k)) r).obj U,
            (i.app U).hom t = Additive.toMul x) ∧
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (Functor.whiskerRight q (forget AddCommGrpCat))

/-- A semiabelian `k`-group algebraic space: an algebraic space over `Spec k` with its natural
commutative group law, satisfying `IsSemiabelianGroupSpace`.
Source: Deligne, Le lemme de Gabber, Section 1.1, p.131
(blueprint: def-sfb-semiabelian-group-space). -/
structure SemiabelianGroupSpace (k : Type u) [Field k] [IsAlgClosed k] where
  /-- The underlying algebraic space over `Spec k`. -/
  space : AlgebraicSpace (Spec (.of k))
  /-- Its natural commutative group law. -/
  group : AlgebraicSpace.CommutativeSpaceGroup space
  /-- The semiabelian conditions. -/
  isSemiabelian : IsSemiabelianGroupSpace group

/-- The abelian-group-valued functor of points of a semiabelian group space, in additive
notation. Its natural transformations are exactly the morphisms of the underlying algebraic
spaces which preserve the group laws, with pointwise addition.
Source: Deligne, Section 1.1, p.131 (blueprint: def-sfb-semiabelian-group-space). -/
def SemiabelianGroupSpace.additivePoints {k : Type u} [Field k] [IsAlgClosed k]
    (G : SemiabelianGroupSpace k) : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  commutativeSpaceGroupPoints G.group ⋙ CommGrpCat.toAddCommGrp

end AlgebraicGeometry
