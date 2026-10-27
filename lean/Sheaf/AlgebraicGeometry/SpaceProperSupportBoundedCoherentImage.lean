/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing

/-! # Bounded coherent direct images with proper cohomology supports

Source: Stacks Project, spaces-perfect.tex, Tag 08GK, lemma-direct-image-coherent
(blueprint: lem-sfb-space-proper-support-bounded-coherent-image).

Cohomology is transported through the canonical small-model module equivalence.
Coherence means quasi-coherence and finite generation on every affine etale chart;
local Noetherianity of the source follows from local finite type over the target.
Proper support is expressed by the reduced closed subspace with exactly that point image.
The direct image is the existing unbounded K-injective derived direct image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type map to a Noetherian algebraic space sends bounded coherent
complexes with degreewise proper support to bounded coherent complexes.
Source: Stacks Project, spaces-perfect.tex, Tag 08GK, lemma-direct-image-coherent
(blueprint: lem-sfb-space-proper-support-bounded-coherent-image).

Proof:
1. Choose a finite cohomological interval [a,b], with a <= b also for the zero object.
Use def-sbc-standard-tstructure-derived-category to choose a representative zero below a.
By lem-pur-ringed-site-grothendieck-abelian the module categories are Grothendieck abelian.
The canonical direct image is additive and left exact by its limit description and
adjunction in def-trf-space-etale-module-functors. Apply thm-sp-truncation-e2 to obtain
E_2^{p,q} = R^p f_* H^q(E) converging to H^{p+q}(Rf_*E), with p >= 0, stabilization,
and finite exhaustive separated abutment filtrations.
2. On compatible scheme charts, pqf-lem-locnoeth-lft makes X locally Noetherian.
For each q in [a,b], the coherent module M = H^q(E) is quasi-coherent and finite type.
By lem-sfb-space-module-proper-carrier-support its annihilator defines a closed subspace.
For a finite module N, N localized at a prime is zero exactly when one element outside
that prime kills all finitely many generators. Hence V(Ann N) is its Zariski support.
By lem-sfb-space-etale-chart-support this equals the inverse image of moduleSupport M.
The charts cover X, so the annihilator subspace has precisely that support.
By lem-sfb-space-proper-support-closed-operations its map to Y is proper. The carrier
criterion lem-sfb-space-module-proper-carrier-support supplies j:W -> X with g = f j
proper and a finite type quasi-coherent G on W satisfying j_*G isomorphic to M.
3. Again pqf-lem-locnoeth-lft makes W locally Noetherian. On a Noetherian affine chart,
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
lem-sfb-scheme-etale-module-exact-finiteness-comparison identify G with an etale
extension of a finite type Zariski module. By
lem-weil-pbc-quasi-coherent-finite-type-affine its global sections N are finite;
lem-weil-pbc-affine-tilde-gamma-adjunction and lem-weil-pbc-tilde-pullback-base-change
identify its sections on Spec B with B tensor N. Thus G is coherent. The closed
immersion j is affine on scheme tests by
lem-weil-pbc-closed-immersion-integral-separated-uc. Apply
lem-sfb-space-affine-module-higher-image-vanishing: R^r j_*G = 0 for r > 0.
4. The spectral sequence lem-sfb-ringed-topos-relative-leray for j, f and G has only
row zero, giving R^p f_*M isomorphic to R^p g_*G. These are coherent by
lem-sfb-space-proper-coherent-higher-images. Proper g is quasi-compact and
quasi-separated, its closed diagonal being affine by
lem-weil-pbc-closed-immersion-integral-separated-uc. Since Y is quasi-compact,
lem-sfb-space-derived-pushforward-upper-bound applied to G[0] gives N_q >= 1 with
R^p g_*G = 0 for p >= N_q. This bound is used only on the proper carrier map g.
5. All E_2 terms are coherent. Apply
lem-sfb-space-coherent-kernel-cokernel-extension to the kernels, images and quotients
of the differentials to make every finite page coherent. Stabilization from
thm-sp-truncation-e2 identifies the infinity terms with finite-page terms. The finite
abutment filtration and closure under extensions give coherence of every H^n(Rf_*E).
6. Take the maximum N of the finitely many N_q. The E_2 page vanishes outside
p >= 0, a <= q <= b, p < N. For n < a or n >= b+N every term with p+q=n is zero,
and remains zero on later pages. The finite exhaustive separated abutment filtration
then has zero graded pieces, so its abutment vanishes. This proves boundedness.
For E = 0 use empty proper carriers and N_q = 1; the same argument applies.
-/
theorem derivedDirectImage_bounded_coherent_of_proper_support
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y) (hf : MapIsLocally (@LocallyOfFiniteType) f)
    (hYln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (hYqc : CompactSpace (Point Y.obj.obj))
    (hYqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y.obj.obj)
      (b : yoneda.obj V ⟶ Y.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (E : X.DerivedModules)
    (hcoh : ∀ i : ℤ,
      (X.smallModuleEquivalence.inverse.obj
        ((DerivedCategory.homologyFunctor X.SmallModules i).obj E)).IsQuasicoherent ∧
      ∀ T : X.EtaleSite, IsAffine (X.etaleForget.obj T) →
        Module.Finite Γ(X.etaleForget.obj T, ⊤)
          Γ((X.schemeRestriction T).obj (X.smallModuleEquivalence.inverse.obj
            ((DerivedCategory.homologyFunctor X.SmallModules i).obj E)), ⊤))
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj E))
    (hsupport : ∀ i : ℤ, ∃ (Z : AlgebraicSpace S) (j : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) j.hom.hom ∧
      IsReduced Z ∧
      pointImage j.hom.hom = moduleSupport (X.smallModuleEquivalence.inverse.obj
        ((DerivedCategory.homologyFunctor X.SmallModules i).obj E)) ∧
      MapIsProper (j ≫ f)) :
    (∀ i : ℤ,
      (Y.smallModuleEquivalence.inverse.obj
        ((DerivedCategory.homologyFunctor Y.SmallModules i).obj
          ((derivedDirectImage f).obj E))).IsQuasicoherent ∧
      ∀ T : Y.EtaleSite, IsAffine (Y.etaleForget.obj T) →
        Module.Finite Γ(Y.etaleForget.obj T, ⊤)
          Γ((Y.schemeRestriction T).obj (Y.smallModuleEquivalence.inverse.obj
            ((DerivedCategory.homologyFunctor Y.SmallModules i).obj
              ((derivedDirectImage f).obj E))), ⊤)) ∧
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj
        ((derivedDirectImage f).obj E))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
