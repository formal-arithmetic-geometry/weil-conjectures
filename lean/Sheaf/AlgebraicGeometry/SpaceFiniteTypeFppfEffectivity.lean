/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.AlgebraicGeometry.BoundedAffineLocallyFiniteTypeCoproduct
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Limits

/-!
# Effective fppf descent of finite-type algebraic spaces

Source: Stacks Project, bootstrap.tex, Tag 0ADV(2), scheme-base specialization,
and Tag 04U0 (blueprint: lem-sfb-space-finite-type-fppf-effectivity).

The local objects are sheaves on the actual big fppf slice sites. Their descent datum
contains the overlap isomorphisms and their cocycle, including the diagonal identity.
An isomorphism of descent data in the conclusion preserves precisely these comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fppf descent data for finite-type algebraic spaces over schemes are effective,
with no countability condition on the covering index.
Source: Stacks, bootstrap.tex, Tag 0ADV(2), using Tag 04U0
(blueprint: lem-sfb-space-finite-type-fppf-effectivity).

The unique map to the Yoneda presheaf of the identity object of `Over (Tᵢ i)`
is the structure map to `Tᵢ i`. Its quasi-compactness is `MapIsQuasiCompact`;
local finite type is the existing test on all representable étale scheme charts.
`DescentData.hom_self` and `hom_comp` encode the diagonal identity and cocycle.
`DescentData.iso` makes the overlap maps isomorphisms. The descent-data isomorphism
in the conclusion includes compatibility with all these specified maps.

Proof:
1. Apply lem-pe-set-sheaf-cover-descent on a small model of the big fppf site.
   Glue the local sheaves with their given comparisons to a sheaf F over T.
2. Refine the covering by affine opens. Their images are open by
   lem-weil-pbc-flat-lfp-open. Define B(T) to be the set of affine opens of T,
   and choose one affine covering piece whose image contains each basis open
   contained in some image. These selected images cover T. Their index J has
   cardinality at most |B(T)|. By lem-sfb-stack-chartwise-smooth-etale-calculus,
   the pieces are locally of finite type over T; the one-member case of
   lem-sfb-bounded-affine-lft-coproduct places them in the fixed big site.
   If T is empty use the empty family.
3. Set P_j = F ×_T V_j. It is a base change of the original local space, hence
   algebraic by lem-trf-space-fibre-products-etale-covers and finite type by
   lem-sfb-stack-finite-type-calculus. Since V_j is affine, P_j is quasi-compact.
4. By lem-sfb-qc-space-affine-etale-atlas choose an affine surjective étale
   atlas W_j of P_j. Its map to V_j is locally of finite type by the chart
   meaning of finite type. Its composite to T is locally of finite type by
   lem-sfb-stack-chartwise-smooth-etale-calculus.
5. Form E = coproduct W_j by lem-weil-pbc-scheme-coproduct-family. The bound on
   J and lem-sfb-bounded-affine-lft-coproduct place E in the fixed site.
   Transport its coproduct maps along the representing isomorphism, extending
   maps by precomposition with its inverse. Then lem-trf-algebraic-space-coproduct
   gives the algebraic-space coproduct P of the P_j with atlas E, also for J empty.
6. Likewise represent D = coproduct V_j in the fixed site. Transport its structure
   map by the inverse representing isomorphism and its component maps by the
   isomorphism itself. The disjoint open components cover D, so locality gives
   flatness and local finite presentation of D → T. The map is surjective because
   the selected images cover T.
7. The summands induce P → F. For every scheme test Z → F,
   lem-trf-fppf-sheaf-coproduct-partition identifies a section of Z ×_F P with
   a clopen partition into pieces mapping to the V_j. The scheme coproduct
   property identifies these with maps to D over T. These identifications are
   natural and preserve Z, hence Z ×_F P is represented by Z ×_T D over Z.
8. The test projections are surjective, flat and locally finitely presented by
   base-change stability in lem-sfb-stack-chartwise-smooth-etale-calculus.
   Apply lem-sfb-fppf-space-atlas-bootstrap to P → F to obtain algebraicity of F.
9. Regard F as X. The original sheaf-descent isomorphisms identify its restrictions
   with the X_i and induce exactly the original comparisons. The bounded
   refinement was used only to prove algebraicity, imposing no restriction on I. -/
theorem finiteType_fppf_descent_effective
    {I : Type w} (T : Scheme.{u}) (Tᵢ : I → Scheme.{u})
    (p : ∀ i : I, Tᵢ i ⟶ T)
    (hcov : Presieve.ofArrows Tᵢ p ∈ Scheme.fppfPrecoverage T)
    (D : (Scheme.fppfTopology.pseudofunctorOver (Type u)).DescentData p)
    (hAlg : ∀ i : I, IsAlgebraicSpace (D.obj i))
    (hft : ∀ i : I,
      MapIsQuasiCompact
        ((Over.mkIdTerminal.isTerminalObj yoneda _).from (D.obj i).obj) ∧
      MapToSchemeIsLocally (@LocallyOfFiniteType) ⟨D.obj i, hAlg i⟩
        (Over.mk (𝟙 (Tᵢ i)))
        ((Over.mkIdTerminal.isTerminalObj yoneda _).from (D.obj i).obj)) :
    ∃ X : AlgebraicSpace T,
      Nonempty (D ≅
        ((Scheme.fppfTopology.pseudofunctorOver (Type u)).toDescentData p).obj X.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
