/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.Paper.ZlImmersionWeilLocalData
public import Sheaf.Paper.WeilIndSheafCategory

/-! # Simultaneous normalized immersion restrictions
Source: the Restriction paragraph of the open--closed reduction blueprint.
(blueprint: lem-zl-immersion-restriction-assembly). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  {W₀ X₀ U₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]

/-- Assemble only restriction, for two immersions with one common target.
Source: lem-zl-morphism-open-closed-reduction.proof.md, Restriction;
lem-zl-residue-compatible-pullback-frobenius and
lem-zl-texact-fixed-pair-heart-cohomology.
(blueprint: lem-zl-immersion-restriction-assembly).

Proof: use the signed integral pullback shifts and their scalar descents for all
three Frobenius functors. Their canonical truncation comparisons give dX, dW, dU.
The local operators are the cohomology images of the three-factor
localQbarClosedFrobenius. Naturality follows from naturality of the point transport,
return compositors and iterated Weil maps. At each literal finite stage the
specified scalar comparisons identify this operator with localClosedFrobenius,
giving the required HEq normalization. Apply residueCompatiblePullbackFrobenius
to each immersion. Its immersion_residue gives closed_image and residue_iso;
equality of finite residue degrees gives degree_eq. Its inverse-compositor fibre
comparison and cohomology equation give the normalized stalks and their Frobenius
equations. The canonical truncation comparisons and the fixed-pair heart theorem
give each exact Weil operation. The normalizations of zlPullComp and
localQbarPullbackComposition identify the second comparison with
zlFrobeniusSquare. Use the same dX and local operator construction both times;
the two sources have no dependence on one another. No open extension is asserted.
The empty source and the identity immersion use the same constructions. -/
theorem zlImmersionRestrictionAssembly
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    ∃ (dX : ZlFrobeniusComparison D c X₀) (dW : ZlFrobeniusComparison D c W₀)
      (dU : ZlFrobeniusComparison D c U₀)
      (FX : ZlWeilLocalOperators D c X₀) (FW : ZlWeilLocalOperators D c W₀)
      (FU : ZlWeilLocalOperators D c U₀)
      (Rh : ZlImmersionPullback D c h₀ dX dW FX FW)
      (Rj : ZlImmersionPullback D c j₀ dX dU FX FU),
      Rj.equivariance = zlFrobeniusSquare D c.l c.different c.Qbar j₀ := by sorry

end WeilConjectures
