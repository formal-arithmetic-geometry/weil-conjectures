module

public import Sheaf.AlgebraicGeometry.RelativeExternalSections
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # External invertible global sections over a DVR

Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`;
its degree-zero two-equalizer argument over a DVR, using Stacks Tag 0539.
(blueprint: lem-sfb-dvr-external-invertible-global-sections)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.RelativeExternalSections

/-- The canonical external-section map is an isomorphism, specified on every pure tensor.
Source: Stacks 0BED, degree-zero DVR extension using 0539.
(blueprint: lem-sfb-dvr-external-invertible-global-sections)

Proof: (1) Choose finite affine covers of the two quasi-compact schemes; separatedness
makes their pairwise intersections affine. The affine rectangles cover the product.
(2) On each rectangle the affine pullback and tensor formulas identify its sections
with the tensor of the two section modules; the inverse sends s tensor t to the two
pulled-back sections tensored together. These formulas commute with restrictions.
(3) Flatness of the schemes and invertibility make sections on all these opens and on
the entire schemes torsion-free (lem-sc-flat-invertible-sections-torsion-free).
Over a DVR they are flat (lem-trf-valuation-torsionfree-flat, Tag 0539).
(4) Tensor the first sheaf equalizer by sections on an affine open of the second
scheme. Flat-tensor exactness and finite-product compatibility identify its kernel
with the sections on the product with that open. (5) Tensor the second sheaf equalizer
by the first global section module and apply (4). Its kernel gives the asserted
isomorphism with exactly the pure-tensor formula. (8) An empty scheme has zero
sections and empty product; the formula is the unique isomorphism between zero modules.
No positive-cohomology vanishing or section base-change is used. -/
theorem dvr_external_invertible_global_sections
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (X Y : Over (Spec R)) [CompactSpace X.left] [CompactSpace Y.left]
    [IsSeparated X.hom] [IsSeparated Y.hom] [Flat X.hom] [Flat Y.hom]
    (F : X.left.Modules) (G : Y.left.Modules) [F.IsInvertible] [G.IsInvertible] :
    ∃ K : (sections R X F ⊗[R] sections R Y G) ≃ₗ[R]
      sections R (X ⊗ Y) (coefficients F G),
      ∀ (s : sections R X F) (t : sections R Y G), K (s ⊗ₜ[R] t) = pure F G s t := by
  sorry

/-- Naturality for arbitrary pullbacks and sheaf isomorphisms, including scheme isomorphisms.
Source: Stacks 0BED, functoriality; 0097 and 01CD, normalized comparisons.
(blueprint: lem-sfb-dvr-external-invertible-global-sections)

Proof: step (6) pulls back p_X^*s tensor p_Y^*t along the product of the two maps.
The two projection squares and normalized composition comparisons identify its factors
with the successive pullbacks of s and t. The tensor comparison identifies their tensor
with the pullback of the tensor section. Apply the two sheaf isomorphisms and their
linearity. Thus the square commutes on each pure tensor, hence everywhere by the
universal property of the module tensor product. The same pure-tensor construction
supplies the canonical linear map for the pulled-back sheaves, even when the new
schemes do not satisfy the isomorphism hypotheses. Identity maps and identity sheaf
isomorphisms give the respective individual naturality assertions. -/
theorem dvr_external_sections_naturality
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (X Y : Over (Spec R)) [CompactSpace X.left] [CompactSpace Y.left]
    [IsSeparated X.hom] [IsSeparated Y.hom] [Flat X.hom] [Flat Y.hom]
    (F : X.left.Modules) (G : Y.left.Modules) [F.IsInvertible] [G.IsInvertible]
    (K : (sections R X F ⊗[R] sections R Y G) →ₗ[R]
      sections R (X ⊗ Y) (coefficients F G))
    (hK : ∀ (s : sections R X F) (t : sections R Y G), K (s ⊗ₜ[R] t) = pure F G s t)
    (X' Y' : Over (Spec R)) (a : X' ⟶ X) (b : Y' ⟶ Y)
    (F' : X'.left.Modules) (G' : Y'.left.Modules)
    (eF : (Scheme.Modules.tensorPullback a.left).obj F ≅ F')
    (eG : (Scheme.Modules.tensorPullback b.left).obj G ≅ G') :
    ∃ K' : (sections R X' F' ⊗[R] sections R Y' G') →ₗ[R]
      sections R (X' ⊗ Y') (coefficients F' G'),
      (∀ (s : sections R X' F') (t : sections R Y' G'),
        K' (s ⊗ₜ[R] t) = pure F' G' s t) ∧
      ∀ (s : sections R X F) (t : sections R Y G),
        K' (eF.hom.app ⊤ (pullSection a.left F s) ⊗ₜ[R]
          eG.hom.app ⊤ (pullSection b.left G t)) =
        (((Scheme.Modules.tensorPullback (fst X' Y').left).map eF.hom ⊗ₘ
            (Scheme.Modules.tensorPullback (snd X' Y').left).map eG.hom)).app ⊤
          ((pullCoefficients a b F G).hom.app ⊤
            (pullSection (a ⊗ₘ b).left (coefficients F G) (K (s ⊗ₜ[R] t)))) := by
  sorry

/-- Equivariance for induced rational coactions; the double sum is the diagonal coaction.
Source: Stacks 0BED, 03LF, 01I8, 01I9 and 01U5, the node's pure-tensor argument.
(blueprint: lem-sfb-dvr-external-invertible-global-sections)

Proof: step (7) puts C = R[H]. Flatness of H makes C flat over R. Restriction of
product sections to the finite affine rectangle cover is injective. Tensoring with C
preserves this injection, and the affine section formula identifies its coordinates
with restriction after base change to H. Hence the comparison from Q tensor C to
sections on H times the product is injective; no base-change isomorphism is assumed.
For finite presentations of the two coactions, the induced-coaction equations say
that their sums, with antipode coefficients S(ci), S(dj), give precisely the descended
action pullbacks. The external descent is their tensor after pullback to the same H
variable, with normalized composition and tensor comparisons
(lem-weil-pbc-invertible-pullback-tensor). Its coefficients multiply, and
S(ci)S(dj) = S(ci dj) because C is commutative, giving the displayed double sum.
Both sides have the same image under
the injective comparison, hence are equal. Tensor generators give the entire coaction
square. Step (8) also covers empty schemes and zero section modules. -/
theorem dvr_external_sections_coaction
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (H X Y : Over (Spec R)) [GrpObj H] [IsAffine H.left] [Flat H.hom]
    [ModObj H X] [ModObj H Y]
    [CompactSpace X.left] [CompactSpace Y.left]
    [IsSeparated X.hom] [IsSeparated Y.hom] [Flat X.hom] [Flat Y.hom]
    (DX : EquivariantCoherent.ActionGroupoidModel H X)
    (DY : EquivariantCoherent.ActionGroupoidModel H Y)
    (M : Scheme.GroupoidModule (EquivariantCoherent.source H X)
      (EquivariantCoherent.target H X) (EquivariantCoherent.identityArrow H X)
      (EquivariantCoherent.inverseArrow H X) DX.comp DX.laws)
    (N : Scheme.GroupoidModule (EquivariantCoherent.source H Y)
      (EquivariantCoherent.target H Y) (EquivariantCoherent.identityArrow H Y)
      (EquivariantCoherent.inverseArrow H Y) DY.comp DY.laws)
    [M.moduleObj.IsInvertible] [N.moduleObj.IsInvertible]
    (K : (sections R X M.moduleObj ⊗[R] sections R Y N.moduleObj) →ₗ[R]
      sections R (X ⊗ Y) (coefficients M.moduleObj N.moduleObj))
    (hK : ∀ (s : sections R X M.moduleObj) (t : sections R Y N.moduleObj),
      K (s ⊗ₜ[R] t) = pure M.moduleObj N.moduleObj s t)
    (ρM : sections R X M.moduleObj →ₗ[R] sections R X M.moduleObj ⊗[R] Γ(H.left, ⊤))
    (ρN : sections R Y N.moduleObj →ₗ[R] sections R Y N.moduleObj ⊗[R] Γ(H.left, ⊤))
    (ρQ : sections R (X ⊗ Y) (coefficients M.moduleObj N.moduleObj) →ₗ[R]
      sections R (X ⊗ Y) (coefficients M.moduleObj N.moduleObj) ⊗[R] Γ(H.left, ⊤))
    (hM : IsInduced H X M.moduleObj (ModObj.smul (M := H) (X := X)).left (descent M) ρM)
    (hN : IsInduced H Y N.moduleObj (ModObj.smul (M := H) (X := Y)).left (descent N) ρN)
    (hQ : IsInduced H (X ⊗ Y) (coefficients M.moduleObj N.moduleObj)
      (diagonalAction H X Y).left
      (externalDescent M.moduleObj N.moduleObj (descent M) (descent N)) ρQ)
    (s : sections R X M.moduleObj) (t : sections R Y N.moduleObj)
    (n m : ℕ) (si : Fin n → sections R X M.moduleObj)
    (tj : Fin m → sections R Y N.moduleObj) (ci : Fin n → Γ(H.left, ⊤))
    (dj : Fin m → Γ(H.left, ⊤))
    (hs : ρM s = ∑ i, si i ⊗ₜ[R] ci i) (ht : ρN t = ∑ j, tj j ⊗ₜ[R] dj j) :
    ρQ (K (s ⊗ₜ[R] t)) = ∑ i, ∑ j, K (si i ⊗ₜ[R] tj j) ⊗ₜ[R] (ci i * dj j) := by
  sorry

end AlgebraicGeometry.RelativeExternalSections
