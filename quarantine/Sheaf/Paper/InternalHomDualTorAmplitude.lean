/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q109 and NB
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison

/-!
# Finite Tor amplitude of locally constant perfect duals

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md,
  paragraph 2 final sentence and paragraph 3 parenthetical
  (blueprint: lem-sfb-internal-hom-dual-tor-amplitude).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The termwise scalar extension of a coefficient complex to a pro-etale chart.
The zero-morphism preservation witness is explicit so this construction does not depend on a
file-local instance. Source: def-weil-pbc-strict-perfect-coefficient-package
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
noncomputable def scalarExtensionComplex
    {Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})}
    {U : Scheme.{u}}
    (G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U))
    (hG : G.PreservesZeroMorphisms)
    (F : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ) :
    CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U)) ℤ :=
  by
    letI : G.PreservesZeroMorphisms := hG
    exact (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- A finite projective module object is a retract of a finite free module object.
The maps between finite free condensed modules are matrices over `R = Λ(*)`. Thus a
retract is scalar extension of the corresponding finite projective R-module; maps between
retracts are likewise R-linear matrices. This identifies complexes of these retracts with
the termwise scalar models of the statement, including their differentials.
Source: def-pc-perfect-ring-complex and def-weil-pbc-strict-perfect-coefficient-package;
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
def FiniteProjectiveCondensedModule
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) : Prop :=
  ∃ n : ℕ, ∃ i : M ⟶ Mod.finiteFree Λ.X n,
    ∃ p : Mod.finiteFree Λ.X n ⟶ M, i ≫ p = 𝟙 M

/-- The relative derived internal Hom dual `RHom_B(P,B)` used in the statement.
Source: sk-def-sfb-derived-tensor-hom (blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
noncomputable def relativeInternalHomDual
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (S : Scheme.{u})
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S))) : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S)) :=
  ((CondensedRing.derivedHom Λ.X S).obj (Opposite.op P)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X S)))

/-- The dual of a pro-etale locally constant perfect complex has finite Tor amplitude.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md, paragraphs 2--3
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude).

Proof plan, following all seven steps of the DAG node:
1. Use lem-sfb-module-object-ringed-site-derived-comparison to identify module objects with
   modules on the ringed site, preserving tensor, internal Hom and slice restriction.
2. For the empty scheme take `[0,0]`. Otherwise quasi-compactness and the fpqc covering
   condition give a nonempty finite covering refinement. Take the minimum lower bound and
   maximum upper bound of its bounded coefficient models.
3. Pull back their degreewise finite-projective splittings. Each term is a retract of a
   finite free coefficient module, so tensor and internal Hom out of it are exact
   (lem-sc-finite-free-internal-hom-exact).
4. Use lem-weil-pbc-ringed-internal-hom-exact-restriction and
   lem-pc-bounded-exact-term-hom-quasi-iso to compute the restricted dual by the signed
   Hom complex into B[0]. Its n-th term is Hom(E^(-n),B), with differential
   phi mapped to (-1)^(n+1) phi composed with d_E^(-n-1), and interval `[-b_j,-a_j]`.
5. Dualizing the splittings shows the dual terms are finite-free retracts and flat.
   Apply lem-sp-ringed-site-tor-flat-model to both bounded flat models.
6. Exact slice restriction commutes with cohomology and derived tensor, by
   lem-pur-site-restriction-module-adjunction-exact and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Test the local bounds on N restricted
   to each chart, and enlarge to the common intervals `[a,b]` and `[-b,-a]`.
7. Apply lem-sfb-sheaf-cover-local-isomorphism to each cohomology sheaf mapped to zero.
   Transport the resulting global vanishings back to module objects. The bounds were
   chosen before N, so they give finite Tor amplitude as in sk-def-sfb-constructible.

The hypothesis `_hΛ` is the recorded six-case admissible coefficient predicate, including
all continuous functions into the algebraic closure with its specified topology. -/
theorem internalHom_dual_tor_amplitude
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S)))
    (hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ i : 𝒰.I₀,
        ∃ F : CochainComplex
          (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ,
          (∃ c d : ℤ, ∀ n : ℤ, n < c ∨ d < n → IsZero (F.X n)) ∧
          (∀ n : ℤ, FiniteProjectiveCondensedModule Λ (F.X n)) ∧
          ∃ hG : ((upperStarFromPoint (𝒰.X i)).mapMod Λ.X).PreservesZeroMorphisms,
          Nonempty
            (((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory).obj P ≅
              DerivedCategory.Q.obj
                (scalarExtensionComplex (Λ := Λ) (U := 𝒰.X i)
                  ((upperStarFromPoint (𝒰.X i)).mapMod Λ.X) hG F))) :
    ∃ a b : ℤ, a ≤ b ∧
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj Λ.X S),
        ∀ q : ℤ, q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((CondensedRing.derivedTensor Λ.X S).obj P).obj
              ((DerivedCategory.singleFunctor _ 0).obj N)))) ∧
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj Λ.X S),
        ∀ q : ℤ, q < -b ∨ -a < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((CondensedRing.derivedTensor Λ.X S).obj
              (relativeInternalHomDual Λ S P)).obj
              ((DerivedCategory.singleFunctor _ 0).obj N)))) ∧
      (IsEmpty S → a = 0 ∧ b = 0) := by
  sorry

end AlgebraicGeometry.ProEtale
