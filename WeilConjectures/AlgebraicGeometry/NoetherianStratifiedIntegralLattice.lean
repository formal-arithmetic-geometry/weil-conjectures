/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpectralEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.SpectralFiniteEtaleTraceLattice
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Stratified integral lattices over a Noetherian scheme

Source: latest blueprint, six-functors basics, `sk-lem-stratified-lattice`, statement
and proof, with the trace construction in `det-lem-stratified-lattice-trace`.
(blueprint: lem-fd-stratified-integral-lattice).

The coefficients are continuous-map condensed rings pulled back from the point.
The rationalization map is the adjoint of the actual integral lattice inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational coefficient module on a Noetherian scheme admits lisse integral
lattices on a finite partition by locally closed subschemes. Ranks may vary or vanish,
and empty strata are permitted. The field has its spectral norm topology and its
valuation ring has the subspace topology.

Source: latest blueprint, `sk-lem-stratified-lattice`, statement and proof, and
`det-lem-stratified-lattice-trace`, trace construction.
(blueprint: lem-fd-stratified-integral-lattice).

Proof.
1. A finite cover by Noetherian affine opens makes the underlying space Noetherian:
   intersect a descending closed chain with each affine and take the maximum of its
   finitely many stabilization indices (lem-sc-affine-noetherian-underlying-space).
   Local Noetherianity also implies quasi-separatedness
   (lem-weil-pbc-locally-noetherian-quasi-separated).
2. Apply lem-sfb-spectral-etale-local-lattice to obtain a qcqs surjective etale
   cover carrying a lisse integral module whose rationalization is the pulled module.
3. Apply lem-weil-pbc-etale-stratified-finite (Stacks 03S0) to this cover. Its finite
   etale restrictions remain surjective by lem-weil-pbc-surjective-base-change.
4. Restrict the integral and rational modules to each pullback square. They remain
   lisse by lem-weil-pbc-continuous-locally-free-pullback. Use
   lem-sfb-pullback-extend-scalars-comparison, def-sfb-module-upper-star-comp and
   sk-def-sfb-coefficient-morphisms to identify the rationalization with the pullback
   of the restricted rational module, for the actual pulled coefficient inclusion.
5. Apply lem-sfb-spectral-finite-etale-trace-lattice on each stratum. Its trace image
   is lisse integral, embeds monically in the restricted rational module, and its
   inclusion has invertible scalar-extension adjoint. On a split cover it is the sum
   of finitely many sheet lattices; no division by the degree occurs.
6. Identify this monic module with its embedded submodule. By the adjunction of
   sk-def-sfb-change-of-scalars the adjoint is precisely b tensor m mapped to b i(m).
   The finite partition and these lattices give the result. The empty partition handles
   the empty scheme, and rank zero and retained empty strata allow the zero module. -/
theorem exists_noetherian_stratified_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (Profinite.continuousMapRingSheafOfUniverse.{u, u}
          (Padic.coefficientExtensionIntegers l E))) :=
      Sheaf.isCommMonObj_sheafCompose_obj _
        (Profinite.continuousMapRingSheafOfUniverse.{u, u}
          (Padic.coefficientExtensionIntegers l E))
        (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers l E)) ↦
          mul_comm a b)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Z),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj E) L →
      ∃ S : Z.FiniteLocallyClosedStratification, ∀ a : Fin S.n,
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          (condensedRingObj
            (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))
            (S.domain a)),
          IsLisseCoefficientModule
            (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)) M ∧
          ∃ ι : M ⟶ (Mod.comap ((upperStarFromPoint (S.domain a)).map
              ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
                (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
                  (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)))).obj
              ((upperStar (Profinite.continuousCoefficientRingObj E) (S.immersion a)).obj L),
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
              ((upperStarFromPoint (S.domain a)).map
                ((sheafCompose (coherentTopology Profinite.{u})
                  (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
                  (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
                    (Padic.coefficientExtensionIntegers l E).subtype
                    continuous_subtype_val)))).homEquiv M
                ((upperStar (Profinite.continuousCoefficientRingObj E)
                  (S.immersion a)).obj L)).symm ι) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
