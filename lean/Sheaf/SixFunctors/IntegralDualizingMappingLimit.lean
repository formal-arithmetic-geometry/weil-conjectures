/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal
import Sheaf.SixFunctors.IntegralDualizingMappingLimitHom

/-! # Mapping complexes into the prescribed dualizing tower limit

Source: current blueprint prop-coef-integral-dualizing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The mapping-complex and degree-zero adjunction for a prescribed normalized
finite-dualizing tower limit. It constructs no tower or integral dualizing object.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph,
the displayed chain of finite mapping-complex inverse limits and its counits
(blueprint: lem-coef-integral-dualizing-mapping-limit).

Proof: for a bounded constructible K, integral residue Tor invariance gives a common
finite Tor interval on its reductions. Integral compact-support reduction then
identifies every finite compact-support value with the reduction of its integral
value C; coefficient-point sections preserve these reductions. Scalar extension
and restriction adjunction identify the finite mapping complexes. Finite exceptional
adjunction gives their duality isomorphisms, and the counit compatibility under
quotient reduction makes them coherent. Use one K-injective tower resolution of
T to form the left mapping tower. Ringed internal Hom preserves derived products
by tensor-Hom adjunction, is exact, and commutes with shifts; derived sections
preserve the resulting Roos triangles. Thus mapping into the prescribed Roos limit
is the derived limit of this same mapping tower, naturally in K. The fixed trace
rectification, tower evaluation pairing, compact-support coaugmentation, and natural
currying identify it with the coefficient Hom tower RHom_R(C,A_n). The complete DVR
is the inverse limit of its quotients, whose surjective transition maps give no
higher derived limit: solve x_n-q(x_(n+1))=b_n recursively to see surjectivity of 1-s.
Consequently the last Hom tower has limit RHom_R(C,R). Compose these natural
isomorphisms. For degree zero apply rhom_global_sectionsOfUniverses to source and
point and use the coefficient-point equivalence, which takes the point unit to R.
The resulting equivalence is Hom_X(K,M) = Hom_s(Ra_!K,R_s). Only the given
presentation and e are used; no choice of arbitrary existence data defines M. -/
theorem integralDualizing_mapping_limit
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    Nonempty (integralDualizingGlobalHom l E X M.obj ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        coefficientDerivedDual (integralDualizingCoefficients l E)) ∧
    ∀ K : sfIntegralConstructibleCategory l E X,
      Nonempty ((K.obj ⟶ M.obj) ≃
        ((integralDualizingLimit l E (Spec (.of D.k))).obj
          ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
            (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
              (SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  refine ⟨integralDualizing_mapping_limit_global D l hl E X T e he M hM, ?_⟩
  exact integralDualizing_mapping_limit_hom D l hl E X T e he M hM

end WeilConjectures
