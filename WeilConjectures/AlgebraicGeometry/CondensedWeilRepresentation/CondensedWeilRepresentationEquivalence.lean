/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # The condensed lisse Weil sheaf--representation equivalence

Source: latest blueprint, sec-purity-real-sheaves/sk-d-real-weil,
prop-wf-weil-sheaf-representation-equivalence.md and its proof
(blueprint: prop-wf-weil-sheaf-representation-equivalence).

The source category consists of actual condensed module sheaves with invertible
Frobenius descent. Geometric groups and normalized fibre paths are the existing
finite-etale and condensed constructions. All auxiliary declarations below merely
spell out the clauses of the equivalence; none assumes the equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedWeilRepresentation

/-- Lisse objects in the existing ordinary condensed Weil module category.
Source: the proposition, lisse Weil sheaf paragraph
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev Lisse (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X) :=
  ObjectProperty.FullSubcategory
    (fun F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ell) g.hom ↦
      RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell) F.carrier)

/-- Forget the Weil structure, retaining the actual underlying module.
Source: the proposition, exactness paragraph
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev forget (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X) :
    Lisse ell g ⥤ RealCondensedFibre.Modules (Profinite.padicAlgClRingObj ell) X :=
  ObjectProperty.ι
    (fun F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ell) g.hom ↦
      RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell) F.carrier) ⋙
    WeilConjectures.condensedWeilModuleForget (Profinite.padicAlgClRingObj ell) g.hom

/-- Tensor two actual Weil pairs, using the inverse pullback tensorator.
Source: the proposition, tensor assertion
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def pairTensor (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X)
    (F H : Lisse ell g) :
    WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ell) g.hom :=
  Endofunctor.IsoAlgebra.mk (F.obj.carrier ⊗ H.obj.carrier)
    ((Functor.Monoidal.μIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom)
      F.obj.carrier H.obj.carrier).symm ≪≫ (F.obj.str ⊗ᵢ H.obj.str))

/-- The unit Weil pair with its canonical coefficient pullback comparison.
Source: the proposition, tensor assertion
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def pairUnit (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X) :
    WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ell) g.hom :=
  Endofunctor.IsoAlgebra.mk (𝟙_ (RealCondensedFibre.Modules
    (Profinite.padicAlgClRingObj ell) X))
      (Functor.Monoidal.εIso
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom)).symm

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (N : RealCondensedFibre.Context.{u}) (j : N.X ≅ (D.geometricFiber C₀).left)

/-- The original geometric-to-arithmetic projection in the chosen geometric coordinates.
Source: the proposition, C = C_0 times k
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev projection : N.X ⟶ C₀.left :=
  j.hom ≫ pullback.fst C₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Geometric Frobenius transported to those same coordinates.
Source: the proposition, geometric Frobenius normalization
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def frobenius : N.X ≅ N.X := j ≪≫ D.geometricFrobenius C₀ ≪≫ j.symm

variable [ConnectedSpace C₀.left]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ N.X)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D C₀ N j)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D C₀ N j)) G]

/-- The recorded constant-cover construction of the Weil group, with its original topology.
Source: def-wf-weil-group and the proposition's standing conventions
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev Group :=
  (FiniteEtale.constantCoverAction C₀.hom (t ≫ projection D C₀ N j) G).weilGroup
    (FiniteEtale.geometricFrobenius C₀.hom (t ≫ projection D C₀ N j))

/-- The degree homomorphism with geometric Frobenius of degree +1.
Source: def-wf-weil-group and the proposition's standing conventions
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev degree : Group D C₀ N j t G →* Multiplicative ℤ :=
  (FiniteEtale.constantCoverAction C₀.hom (t ≫ projection D C₀ N j) G).weilGroupDeg
    (FiniteEtale.geometricFrobenius C₀.hom (t ≫ projection D C₀ N j))

/-- Coordinates identify the geometric fundamental group with precisely the degree kernel.
Both the group inclusion and degree-one path are pinned on finite arithmetic covers.
Source: the proposition's Frobenius descent paragraph and def-wf-fundamental-representation
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
structure Coordinates (γ : Group D C₀ N j t G) where
  P : ProfiniteGrp.{u}
  [action : ∀ Q, MulAction P ((FiniteEtale.fiber t).obj Q)]
  [fundamental : PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber t) P]
  geometric : P ≃ₜ* (degree D C₀ N j t G).ker
  arithmetic : ∀ a : P,
    PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D C₀ N j)) G
        (geometric a).val.val.1 =
      FiniteEtale.pullbackPathIso (projection D C₀ N j)
        (PreGaloisCategory.toAut (FiniteEtale.fiber t) P a)
  point_eq : (t ≫ (frobenius D C₀ N j).hom) ≫ projection D C₀ N j =
    t ≫ projection D C₀ N j
  path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ (frobenius D C₀ N j).hom)
  path_arithmetic : FiniteEtale.pullbackPathIso (projection D C₀ N j) path ≪≫
      eqToIso (congrArg FiniteEtale.fiber point_eq) =
    PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D C₀ N j)) G γ.val.1

attribute [instance] Coordinates.action Coordinates.fundamental

variable (ell : ℕ) [Fact ell.Prime] (γ : Group D C₀ N j t G)
  (A : Coordinates D C₀ N j t G γ)

/-- The actual geometric fibre, forgetting only the Weil isomorphism.
Source: the proposition's displayed stalk functor
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
abbrev fibre :=
  forget ell (frobenius D C₀ N j) ⋙ LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) t

set_option maxHeartbeats 0 in
-- The canonical tensor categories have large elaborated types.
set_option maxHeartbeats 0 in
-- The expanded fibre and tensor assertions require a larger elaboration budget.
end AlgebraicGeometry.ProEtale.CondensedWeilRepresentation
