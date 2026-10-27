/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import Sheaf.AlgebraicGeometry.FieldProductSquarePower

/-! # A square power for a pointed smooth family with geometrically integral generic fibre

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 5.9,
final assertion, case (1), and Lemma 5.7, printed pages 14--15, March 31, 2026 version.
(blueprint: lem-sfb-pointed-generic-integral-action-square-power)

Products in `Over S` are the chosen scheme fibre products. For a test object `B`,
`fst Y B` and `snd Y B` are the projections of `Y ×_S B`. The morphism
`(snd Y B ≫ g) • fst Y B` sends `(y,b)` to `g(b)y`; pulling back along this
map gives `τ_g^* M_B` by canonical pullback composition. Thus no choice of a
translation or of a comparison isomorphism enters the assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- A positive tensor power of any invertible module satisfies the square identity
for every test scheme and pair of group-valued points. The section is an ordinary
section, without an equivariance condition. Only the generic fibre of `Y` is
assumed geometrically integral. The normality hypothesis is on every local ring.
The base is Noetherian because it is affine and locally Noetherian; integrality
includes nonemptiness. `S.fromSpecStalk (genericPoint S)` is `Spec k(S) → S`.

Source: Guo, Proposition 5.9, final assertion, case (1), and Lemma 5.7, printed
pages 14--15; Stacks Project, Tags 0BCM and 0BD7.
(blueprint: lem-sfb-pointed-generic-integral-action-square-power)

Proof:
1. Smoothness and finite type, together with separatedness, give finite presentation
   (lem-pc-smooth-flat, def-weil-finite-type-morphism, def-weil-closed-immersion,
   def-sbc-locally-finite-presentation). Apply the smooth section-component lemma
   lem-sbc-smooth-section-component-geometrically-irreducible to the identity of H.
   Connectedness fills each fibre; sbc-lem-smooth-geometrically-reduced makes these
   nonempty fibres geometrically integral. No such assertion is needed for Y.
2. Put C = Y × H × H, P = Y × Y × H × H and Z = P × H, all over S.
   Smooth base change and composition (lem-pc-proper-base-change,
   lem-trf-smooth-composition) give smooth products. Normal ascent
   (lem-sfb-smooth-normal-ascent) and pqf-lem-locnoeth-lft give normal locally
   Noetherian products. The generic fibres are geometrically integral by
   lem-sc-geometrically-irreducible-product and geometric reducedness. Use
   lem-weil-pbc-separated-base-change and lem-weil-pbc-qcqs-morphism-permanence
   for the required finite presentation after base change.
3. P is integral by the affine localization argument of Stacks 0BCM: for an affine
   ring D over a domain R in S, flatness gives an injection D → D ⊗_R Frac(R)
   (lem-weil-pbc-flat-morphism-affine-criterion,
   lem-trf-flat-module-torsionfree-domain). The latter ring is a domain because
   it is the ring of a nonempty open in P's integral generic fibre
   (lem-weil-pbc-fibre-product-affine-spectra). Every nonempty open meets that
   fibre, so P is irreducible as well as reduced. The sections (e,e,1,1) give
   surjectivity over S, so the generic point of P lies over the generic point of S.
4. Let b(y,u,v) = uv⁻¹y and A = b^*L. On Z put
   E(F) = F(y₀,u₀,v) ⊗ F(y₁,u₁,v) ⊗ F(y₀,u₁,v)ᵛ ⊗ F(y₁,u₀,v)ᵛ.
   Apply lem-sfb-field-product-square-power in the order Yη,Hη,Hη to Aη.
   It gives one r ≥ 1 and a line Qη on Pη with E(A.tensorPow r)η ≅ πη^*Qη.
   Set M = L.tensorPow r and F = b^*M. Pullback, tensor powers and duals agree
   on local rank-one frames (def-sc-invertible-module, def-pc-module-pullback).
5. For π : Z → P, the fibres are extensions of H's geometrically integral fibres.
   Restrict the preceding isomorphism to the generic point of P. The line Qη
   becomes a one-dimensional vector space and hence trivial there. Apply
   lem-sfb-normal-noetherian-generic-line-pullback to obtain E(F) ≅ π^*Q
   with Q invertible on P. Only H's integral special fibres are used here.
6. Comparing this isomorphism at v₀ and v₁ cancels Q and gives a trivial cube
   difference on Y² × H⁴. Reorder the eight tensor factors, without reordering
   group factors. For T = H⁴ put
   D(y) = F(y,u₀,v₀) ⊗ F(y,u₁,v₁) ⊗ F(y,u₀,v₁)ᵛ ⊗ F(y,u₁,v₀)ᵛ.
   The trivial cube difference is D(y₀) ⊗ D(y₁)ᵛ. Tensor and dual identities
   hold on local frames (def-pur-sheaf-tensor-product).
7. Pull back along (y,t) ↦ (y,e(s),t). For K = e_T^*D this gives
   D ⊗ q^*Kᵛ ≅ O and therefore D ≅ q^*K. No fixed-point condition on e is used.
8. For arbitrary B,g,h specialize T by (g,1,h⁻¹,1). The four action maps become
   gh,1,g,h by the group and action identities, in that order. Put N = t^*K
   and cancel the two inverse line factors. The resulting isomorphism is exactly
   the displayed square identity. Since it is a pullback of a global isomorphism,
   the r fixed in step 4 works also for nonreduced and non-Noetherian test schemes.
-/
theorem exists_pointedGenericIntegralAction_square_tensorPower
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S] [IsIntegral S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] [GeometricallyConnected H.hom]
    (Y : Over S) [Smooth Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsIntegral Y.left]
    (e : S ⟶ Y.left) (he : e ≫ Y.hom = 𝟙 S) [ModObj H Y]
    (hη : GeometricallyIntegral
      (pullback.snd Y.hom (S.fromSpecStalk (genericPoint S))))
    (L : Y.left.Modules) [L.IsInvertible] :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((tensorPullback (((snd Y B ≫ (g * h)) • fst Y B).left)).obj
              (L.tensorPow r) ⊗
            (tensorPullback (fst Y B).left).obj (L.tensorPow r)) ≅
           (((tensorPullback (((snd Y B ≫ g) • fst Y B).left)).obj
               (L.tensorPow r) ⊗
             (tensorPullback (((snd Y B ≫ h) • fst Y B).left)).obj
               (L.tensorPow r)) ⊗
            (tensorPullback (snd Y B).left).obj N)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
