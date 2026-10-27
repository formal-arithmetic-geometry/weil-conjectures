/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteProperProductMaps

/-! # The two ordinary exchange/projection leg transposes

Source: Stacks Project, sites-cohomology.tex, Tag 0E48,
`remark-compatible-with-diagram` and the preceding `equation-projection-formula-map`;
blueprint main-20261015, `lem-sf-kunneth-coherence.proof.md`, two-counit paragraph
(blueprint: lem-pur-ordinary-derived-product-leg-transposes).

The existing finite product definitions name precisely the ordinary operations and
maps in this statement. None of those definitions assumes properness. Their reuse
retains the canonical tensor, signed symmetry, square comparison, and adjunction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteProperProduct

/-- The two ordinary leg transposes, with the actual source tensor comparisons.
Source: Stacks Project, sites-cohomology.tex, Tag 0E48 and the preceding
`equation-projection-formula-map`; blueprint main-20261015,
`lem-sf-kunneth-coherence.proof.md`, two-counit paragraph
(blueprint: lem-pur-ordinary-derived-product-leg-transposes).

Proof: (1) Under the recorded pullback/direct-image adjunction, the inverse Hom
bijection sends d to eta followed by R(d), and its inverse sends h to P(h)
followed by epsilon. Counit naturality and the triangle identity cancel these
operations. Thus exchange transposes to theta followed by P_r(epsilon_a), and
projection transposes to mu followed by epsilon tensor identity. The finite mu
of lem-pur-derived-pullback-tensor-iso is exactly the ambient ringed-topos mu used
by def-exchange-projection.
(2) Expand v as exchange tensor identity followed by projection. Naturality of
mu in the exchange arrow moves P_t(x tensor identity) across mu. The exchange
transpose from (1) leaves (P_r(epsilon_a) theta) tensor identity after mu.
(3) Expand w with both signed symmetries. Counit naturality moves R_b of the
final symmetry through transposition. Apply the projection transpose from (1),
then the signed-braiding compatibility of lem-pur-derived-pullback-tensor-iso.
Naturality of signed symmetry moves epsilon_b to the second tensor factor;
involutivity cancels the two swaps, leaving identity tensor epsilon_b after mu.
All objects are arbitrary unbounded derived objects, and no exchange or
projection arrow is inverted. -/
theorem ordinaryDerivedProductLegTransposes (P : PurityFiniteSetting.{u})
    (B Y Z : Over (Spec (.of P.field.k))) (a : Y ⟶ B) (b : Z ⟶ B)
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated a.left] [LocallyOfFiniteType a.left] [QuasiCompact a.left]
    [IsSeparated b.left] [LocallyOfFiniteType b.left] [QuasiCompact b.left]
    (H : D P Y.left) (J : D P Z.left) :
    ((adj P (pullback.snd a.left b.left)).homEquiv _ _).symm
        (v P a.left b.left Z.hom H J) =
      (mu P (pullback.snd a.left b.left) (pullback.snd a.left b.left ≫ Z.hom)
        Z.hom _ J).hom ≫
      (tensor P (pullback a.left b.left)).map
        (Prod.mkHom
          ((theta P a.left b.left).hom.app ((push P a.left).obj H) ≫
            (pull P (pullback.fst a.left b.left)).map ((adj P a.left).counit.app H))
          (𝟙 _)) ∧
    ((adj P b.left).homEquiv _ _).symm (w P a.left b.left B.hom Z.hom H J) =
      (mu P b.left Z.hom B.hom _ _).hom ≫
        (tensor P Z.left).map (Prod.mkHom (𝟙 _) ((adj P b.left).counit.app J)) := by
  sorry

end WeilConjectures.FiniteProperProduct
