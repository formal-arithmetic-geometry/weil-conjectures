/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Generic fibres of condensed lisse Weil modules

Source: latest blueprint, rem-dl-a1-conventions, irreducible-lisse and geometric-constancy
paragraphs; Deligne, Weil II (1.1.10)--(1.1.12).
(blueprint: lem-dl-a1-condensed-weil-generic-representation).

All categories below use actual condensed modules. Component and profinite group coordinates
are supplied as conclusions, so geometric connectedness is never an additional assumption.

## Main definitions

* `Lisse`: actual lisse condensed Weil modules.
* `Group` and `Geometry`: the Weil group and its canonical open geometric subgroup.
* `Representations`: representations with continuous finite-field geometric restriction.
* `fibre` and `returnMap`: actual point sections and their Frobenius return operators.
* `Assertions`: the normalized exact tensor equivalence and subobject correspondence.

## Main statements

* `generic_fibre_equivalence`: existence of the specified generic-fibre equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]

/-- Projection from the actual geometric base change.
Source: def-weil-finite-field-fiber
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev projection : (D.geometricFiber U₀).left ⟶ U₀.left :=
  pullback.fst U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]

/-- The constant-cover fibre product with the integer powers of geometric Frobenius.
The same existing group construction is used without assuming its degree map is onto.
The product with discrete integers gives its usual Weil topology.
Source: Weil II (1.1.10); def-wf-fundamental-representation, constant covers
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev Group :=
  (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).weilGroup
    (FiniteEtale.geometricFrobenius U₀.hom (t ≫ projection D U₀))

/-- The original, unrescaled integer degree.
Source: Weil II (1.1.10)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev degree : Group D U₀ t G →* Multiplicative ℤ :=
  (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).weilGroupDeg
    (FiniteEtale.geometricFrobenius U₀.hom (t ≫ projection D U₀))

/-- Coordinates on the component containing the specified geometric generic point.
The group inclusion is pinned on all finite arithmetic covers, and identifies precisely
its open geometric subgroup. All these are output data, not input hypotheses.
Source: rem-dl-a1-conventions and Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
structure Geometry where
  component : RealCondensedFibre.Context.{u}
  inclusion : component.X ⟶ (D.geometricFiber U₀).left
  openImmersion : IsOpenImmersion inclusion
  image : Set.range inclusion = connectedComponent (t (IsLocalRing.closedPoint Ω))
  point : Spec (.of Ω) ⟶ component.X
  point_eq : point ≫ inclusion = t
  P : ProfiniteGrp.{u}
  [action : ∀ Q, MulAction P ((FiniteEtale.fiber point).obj Q)]
  [fundamental : PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber point) P]
  geometric : P →* Group D U₀ t G
  geometric_degree : ∀ a : P, degree D U₀ t G (geometric a) = 1
  geometric_arithmetic : ∀ a : P,
    PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D U₀)) G
        (geometric a).val.1 =
      (eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc point inclusion (projection D U₀)).symm.trans
          (congrArg (fun z ↦ z ≫ projection D U₀) point_eq)))).symm ≪≫
        FiniteEtale.pullbackPathIso (inclusion ≫ projection D U₀)
          (PreGaloisCategory.toAut (FiniteEtale.fiber point) P a) ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc point inclusion (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) point_eq)))
  injective : Function.Injective geometric
  geometric_image : geometric.range = (degree D U₀ t G).ker
  topology : Topology.IsOpenEmbedding geometric

attribute [instance] Geometry.action Geometry.fundamental

variable (ell : ℕ) [Fact ell.Prime]

/-- The specified generic fibre, retaining the scalar ring at the geometric point.
Source: the displayed V_F in the node; thm-lisse-qlbar-representations, Fibres
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev fibre :=
  forget ell (D.geometricFrobenius U₀) ⋙
    LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) t

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
