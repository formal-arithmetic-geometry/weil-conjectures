/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-! # Native integral biduality for coefficient transport

This module states integral biduality in the condensed coefficient derived category.
The scalar-transport theorem consumes this native evaluation map.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- The specified integral biduality map is invertible if its native residue
biduality map is invertible.

Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, integral case (ii).
Proof: the integral constructibility comparison and finite-Tor criterion put the
inputs in the listed scalar internal-Hom theorem. Lift the residue carrier and
factor its actual coefficient map through the listed finite presentation. The
canonical scalar tower is monoidal; evaluation naturality and scalar transport
along the coefficient isomorphism prove invertibility of the native Hom mate.
Apply this to L and RHom(L,W). The braided double-dual comparison identifies the
image of the actual integral biduality map with residue biduality through these
invertible comparisons. Both integral duals remain bounded constructible.
First-reduction Nakayama applied to this specified morphism proves the result.
No exceptional-image property of W or geometric finite biduality is asserted.
(blueprint: lem-pd-integral-biduality-residue-detection) -/
theorem isIso_biduality_integral_of_residue
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (W L : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))
    (hδ : let F :=
      (Mod.extendScalars (padicIntegersToResidueField X.left ℓ E)).leftDerivedFunctor
      IsIso (toIhomIhom (F.obj W.obj) (F.obj L.obj))) :
    IsIso (toIhomIhom W.obj L.obj) := by
  sorry

/-- Integral Verdier evaluation is invertible for the native condensed integral model.

This is the native integral premise consumed by constructible coefficient transport.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.18--6.7.20; latest blueprint
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`.
Proof in words: normalize the integral dualizing complex by the structure map.
Its reductions are finite exceptional pullbacks of the coefficient unit.  Reduction
of internal Hom commutes with evaluation.  Applying this twice identifies each
reduction of the displayed arrow with finite-stage Verdier biduality.  The cone is
derived complete and all its reductions vanish, so derived Nakayama kills it.
For a nonclosed base field, check the finite assertion after algebraic closure;
the geometric pullback and internal-Hom comparison preserve evaluation and are
conservative.  This is integral biduality, before either rationalization or Qbar
extension, and includes zero and torsion lattices.
(blueprint: lem-pd-constructible-sheaf-biduality-integral) -/
theorem isIso_biduality_integral_constructible
    [IsIso S.hom] (a : X ⟶ S)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)) :
    IsIso (toIhomIhom
      ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)).obj
      L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
