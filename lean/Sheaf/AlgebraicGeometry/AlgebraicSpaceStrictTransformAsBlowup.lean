/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import Mathlib.RingTheory.Smooth.Flat

/-! # The strict transform of an algebraic space is its intrinsic blowup

Source: Stacks Project, Divisors on Spaces, Tags 0862, 0863 and 0864(1);
Tags 085R and 085Z; Morphisms of Spaces, Tags 03KL, 03KQ and 03XG
(blueprint: lem-sfb-space-strict-transform-as-blowup).

Blowups use the existing etale-chart presentations. The strict transform is specified
by the kernel of its structure map, on every affine etale chart of the fibre product.
For a finite-type ideal, annihilation locally by powers of its generators is equivalent
on an affine to annihilation by one power of the ideal. On exceptional-equation charts
this is precisely the quotient by exceptional power torsion in Tag 0862.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The blowup in the image ideal is canonically the strict transform, with both
projections, its closed inclusion, the off-centre restriction and the stated permanence
properties. The kernel formula specifies the strict transform as a closed subspace,
including its scheme structure, rather than only its point set. The off-centre clause
is tested on every open immersion on which the extended centre ideal is the unit ideal;
these are exactly the open subspaces of the complement of the centre.
Source: Stacks Project, Divisors on Spaces, Tags 0862, 0863, 0864(1), 085R and 085Z;
Morphisms of Spaces, Tags 03KL, 03KQ and 03XG
(blueprint: lem-sfb-space-strict-transform-as-blowup).

Proof:
1. Form the image J of g^* K to O_Y. It is quasi-coherent by
   lem-sfb-space-module-pullback-quasicoherent and lem-sfb-space-qcoh-kernels-colimits;
   pulled-back local generators show finite type. Form B = Bl_J Y. By
   lem-sfb-space-blowup-chart-properties the ideals K O_D and J O_B are Cartier.
2. Form P = Y times_T D.space by lem-trf-space-fibre-products-etale-covers.
   On charts with exceptional equation a the torsion ideal is Gamma_a(R).
   lem-trf-supported-kernel-flat-pullback gives quasi-coherence and flat compatibility;
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence transports to etale modules.
   Etale chart changes are flat by lem-weil-pbc-etale-algebra-flat. Unit multiples of a
   give the same ideal. Glue by lem-sfb-space-qcoh-cartesian-chart-family and cut out W
   using lem-sfb-space-ideal-closed-subspace-correspondence. On any affine chart,
   support in V(K) is equivalent to annihilation by a power of the finite-type ideal:
   finitely many generators give one common exponent after increasing their exponents.
3. Multiplication by a on R/Gamma_a(R) is injective: ar killed by a^n implies r killed
   by a^(n+1). Thus K O_W = J O_W is Cartier, including when a is a zero-divisor on R.
4. lem-sfb-space-blowup-universal-property gives v:B to D.space and B to P. Torsion
   sections die on B since the exceptional equation there is a non-zero-divisor.
   The ideal/closed-subspace correspondence factors this map through W. The same
   blowup universal property gives W to B over Y.
5. Uniqueness in the two blowup universal properties makes the two composites
   identities: first compare over Y, then over T and both projections of P; finally
   cancel the monic closed inclusion. This gives the unique projection-preserving
   isomorphism e. Its composite with the closed inclusion of W is a closed immersion.
6. On every open where K is unit, lem-sfb-space-blowup-chart-properties identifies D
   with that open. Its equation a is a unit, so the torsion ideal is zero. The two
   cartesian squares in the conclusion identify the strict-transform projection with
   g on this open, compatibly also with the projection to Y.
7. If T is qcqs, D to T is proper, hence quasi-compact and separated. Apply
   lem-sfb-space-quasicompact-fppf-local, lem-sfb-space-quasiseparated-test-calculus
   and lem-sfb-space-qcqs-source-products to obtain the displayed atlas and absolute
   quasi-separatedness of D.space.
8. If g is separated and finite type, base change preserves both properties by
   lem-sfb-space-separated-fp-composition and lem-sfb-stack-finite-type-calculus.
   The closed inclusion of W is proper by lem-sfb-space-closed-subspace-proper.
   Composition uses lem-sfb-space-finite-type-composition and the separated calculus.
   Finally lem-sfb-space-quasiseparated-test-calculus gives the quasi-compact diagonal.
   Empty spaces, K=0 and K=O are included in all these constructions. -/
theorem strictTransform_as_blowup
    {S : Scheme.{u}} {T Y : AlgebraicSpace S}
    (K : QuasiCoherentIdeal T) (hK : (K.val : T.Modules).IsFiniteType)
    (g : Y ⟶ T) (D : BlowupPresentation K) :
    ∃ J : QuasiCoherentIdeal Y,
      (∃ q : (moduleTensorPullback g).obj (K.val : T.Modules) ⟶ (J.val : Y.Modules),
        Epi q ∧ q ≫ J.val.arrow = idealTensorMap g K) ∧
      ∃ (B : BlowupPresentation J) (P : AlgebraicSpace S)
        (qY : P ⟶ Y) (qD : P ⟶ D.space) (W : ClosedSubspace P)
        (v : B.space ⟶ D.space),
        IsPullback qY qD g D.projection ∧
        v ≫ D.projection = B.projection ≫ g ∧
        (∀ (V : P.EtaleSite), IsAffine (P.etaleForget.obj V) →
          ∀ s : P.structureSheaf.obj.obj (op V),
            (moduleStructureMap W.val.arrow).val.app (op V) s = 0 ↔
              ∃ n : ℕ, ∀ a : P.structureSheaf.obj.obj (op V),
                a ∈ idealSectionImage (idealTensorMap (qY ≫ g) K) V ^ n → a * s = 0) ∧
        (∃! e : B.space ≅ (W.val : AlgebraicSpace S),
          e.hom ≫ W.val.arrow ≫ qY = B.projection ∧
          e.hom ≫ W.val.arrow ≫ qD = v ∧
          IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
            (e.hom ≫ W.val.arrow).hom.hom) ∧
        (∀ (U : AlgebraicSpace S) (j : U ⟶ T),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom →
          Epi (idealTensorMap j K) →
          ∃ (l : U ⟶ D.space), IsPullback l (𝟙 U) D.projection j ∧
            ∃ (Q : AlgebraicSpace S) (a : Q ⟶ Y) (b : Q ⟶ U)
              (w : Q ⟶ (W.val : AlgebraicSpace S)),
              IsPullback a b g j ∧
              IsPullback w b (W.val.arrow ≫ qD) l ∧
              w ≫ W.val.arrow ≫ qY = a) ∧
        (((∃ (V : Over S) (a : yoneda.obj V ⟶ T.obj.obj),
            CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a) ∧
            IsAbsolutelyQuasiSeparated T) →
          (∃ (V : Over S) (a : yoneda.obj V ⟶ D.space.obj.obj),
            CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a) ∧
            IsAbsolutelyQuasiSeparated D.space) ∧
        (MapIsSeparated g → MapIsFiniteType g →
          MapIsSeparated (W.val.arrow ≫ qD) ∧ MapIsFiniteType (W.val.arrow ≫ qD) ∧
          MapIsQuasiCompact (pullback.diagonal (W.val.arrow ≫ qD).hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
