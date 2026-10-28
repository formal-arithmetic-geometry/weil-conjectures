/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicTensorPresentationComparison
public import Sheaf.Paper.ReindexingSystemHomReductionSquare

/-! # The ordinary scalar tensor reindexing square

Source: BS Remark 6.8.15; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- Ordinary scalar extension commutes with the normalized tensor reindexing.
There are no completion maps or constructible inputs in this equation.
Source: BS Remark 6.8.15; Stacks 03EL and 07A4.
(blueprint: lem-sf-adic-ordinary-scalar-tensor-reindexing).

Proof: choose flat-term K-flat complexes representing M and N. Substitute the
representative equations of NX, NY, V and W, and the representative characterization
of podCompletedAmbientTensor. The presentation comparison cancels the supplied
ordinary tensor models, so all four sides are computed by signed total tensors.
On a scalar multiple of a homogeneous pure tensor, NY.balance_sections separates
its factors; V.sections applies B.iso to the scalar, and W.pure preserves both
sections. The other route first reindexes the two integral sections and applies
NX.balance_sections, giving the identical scalar and sections. Balancing and local
pure-tensor generation extend this identity to module tensors; coproduct
extensionality extends it to each total degree. All maps preserve the bidegree,
so the Koszul differential is unchanged. Localize this chain identity and cancel
the K-flat counits and tensor representative isomorphisms using their recorded
normalization equations. Naturality transports the resulting equation along the
isomorphisms from the representatives to M and N. No completeness, rationalization,
nonzero-input or quasi-compactness assumption enters this ordinary calculation. -/
theorem ordinary_scalar_tensor_reindexing
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S C E)
    (V : IntegralReindex l X g B E) (W : ReindexTensor l X g A C B)
    (M N : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := derivedPull l X g B
    let H := podCompletedDerivedInverseImage l k g
    F.map ((finiteAmbientScalarTensor l Y S C E NY).inv.app (M, N)) ≫
        V.derived.hom.app ((pullbackTensorCalculus l k Y).integralClosed.tensor.obj (M, N)) ≫
        EX.map ((podCompletedAmbientTensor l k g).hom.app (M, N)) =
      W.tensor.hom.app (EY.obj M, EY.obj N) ≫
        A.closed.tensor.map (Prod.mkHom (V.derived.hom.app M) (V.derived.hom.app N)) ≫
        (finiteAmbientScalarTensor l X R A E NX).inv.app (H.obj M, H.obj N) := by sorry

end WeilConjectures.AdicQbarRealization
