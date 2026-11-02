/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Mathlib.RepresentationTheory.Basic

/-! # Constant Weil lines with condensed coefficients

Source: latest blueprint, part-weights-riemann-hypothesis/sec-weights-deligne-theorem/
sec-wdef-weights/sk-r-real-linear/def-wf-constant-weil-twist.md, full definition
(blueprint: def-wf-constant-weil-twist).

The scalar automorphism is pulled back from multiplication on the actual condensed
coefficient module. The line is the coefficient unit with its canonical Frobenius
followed by that automorphism. Tensoring uses the inverse tensorator of Frobenius.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ConstantWeil

variable (ell : ℕ) [Fact ell.Prime]

/-- Multiplication by a nonzero scalar on the condensed coefficient unit, with its actual
inverse. Source: the scalar b in the definition (blueprint: def-wf-constant-weil-twist). -/
@[irreducible] def coefficientScalar (b : (PadicAlgCl ell)ˣ) :
    Aut (Mod.regular (Profinite.padicAlgClRingObj.{u} ell)) :=
  Aut.unitsEndEquivAut _
    (Units.map (Mod.regularEndRingHom.comp (Profinite.PadicAlgCl.constRingHom ell)).toMonoidHom b)

/-- Multiplication by b on p_X^* Qbar_l, transported through the canonical unit comparison
of p_X^*. Source: underlying constant module and scalar structure
(blueprint: def-wf-constant-weil-twist). -/
@[irreducible] def scalar (X : Scheme.{u}) (b : (PadicAlgCl ell)ˣ) :
    Aut (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X))) :=
  let F := (upperStarFromPoint X).mapMod (Profinite.padicAlgClRingObj ell)
  let e : F.obj (Mod.regular (Profinite.padicAlgClRingObj ell)) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) X) :=
    Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  e.symm ≪≫ F.mapIso (coefficientScalar ell b) ≪≫ e

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- B_b is the actual coefficient unit with structure b times its canonical Frobenius.
The underlying module is globally free on 1, including on disconnected and empty schemes.
Source: first two sentences (blueprint: def-wf-constant-weil-twist). -/
def lineModule (_hEll : ell ≠ D.p) [IsSeparated X₀.hom] (b : (PadicAlgCl ell)ˣ) :
    WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (𝟙_ _)
    ((StrictWeilCondensed.unitWeilModule (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀)).str ≪≫ scalar ell (D.geometricFiber X₀).left b)

/-- The constant line as a constructible Weil sheaf. Constructibility uses the rank-one
coefficient unit and the trivial stratification, rather than a chosen realization.
Source: rank-one Weil sheaf clause (blueprint: def-wf-constant-weil-twist). -/
def line (hEll : ell ≠ D.p) [IsSeparated X₀.hom] (b : (PadicAlgCl ell)ˣ) :
    WeilConjectures.condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom :=
  ⟨lineModule ell D X₀ hEll b,
    (isLocallyFree_tensorUnit (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber X₀).left).isConstructibleModuleObject⟩

/-- Constant Weil twist: tensor with B_b, with Frobenius given by the inverse tensorator
followed by the two structure isomorphisms. Source: final sentence
(blueprint: def-wf-constant-weil-twist). -/
def twist (hEll : ell ≠ D.p) [IsSeparated X₀.hom] (b : (PadicAlgCl ell)ˣ)
    (M : WeilConjectures.condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom) :
    WeilConjectures.condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom :=
  ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk
    (M.obj.carrier ⊗ (line ell D X₀ hEll b).obj.carrier)
    ((Functor.Monoidal.μIso
      (upperStar (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom)
      M.obj.carrier (line ell D X₀ hEll b).obj.carrier).symm ≪≫
      (M.obj.str ⊗ᵢ (line ell D X₀ hEll b).obj.str)),
    M.property.of_iso (ρ_ M.obj.carrier).symm⟩

section Character

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X₀.left)
  (G : Type u) [Group G]
  [∀ P : X₀.left.FiniteEtale, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [GeometricallyConnected X₀.hom]

/-- The geometric connectedness hypothesis supplies the connected base needed by the
finite-etale fibre functor. Source: the domain of W(X_0)
(blueprint: def-wf-constant-weil-twist). -/
local instance modelConnected : ConnectedSpace X₀.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton (f := X₀.hom)

end Character

end AlgebraicGeometry.ProEtale.CondensedRing.ConstantWeil
