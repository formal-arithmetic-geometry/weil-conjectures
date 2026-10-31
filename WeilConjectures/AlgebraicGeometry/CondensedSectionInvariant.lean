/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedVaryingDualizingInverse
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # The section invariant with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-geometry/
def-pur-section-invariant.md, definition and invertibility assertion
(blueprint: def-pur-section-invariant).

The object is the actual total derived module pullback of the native exceptional image
of the coefficient unit. The dualizing-inverse theorem supplies only the proof arguments
needed to type that exceptional functor and the finite-Tor membership of the literal unit.
Neither a tensor inverse nor an orientation is chosen in the definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
      (Padic.coefficientExtensionRing ell E n))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
  (B V : Over (Spec (.of D.k)))
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
  [LocallyOfFiniteType g.left] [QuasiCompact g.left]

/-- The section invariant is `Ls^* Rg^! Λ_B` in the ordinary condensed module category.
The four coefficient presentations use precisely the fixed quotient at positive level,
its valuation ring, its finite extension field, and the finite-subextension-valued closure.
The witnesses extracted from `condensed_varying_dualizing_inverse` are proofs and a Dctf
representative whose underlying object is equal to the coefficient unit. That equality
transports membership to the literal unit before applying `ctfExceptionalInverseImage`.
Thus no unspecified object or arbitrary exceptional functor is selected.

Source: latest blueprint sec-smooth-purity/sk-lem-geometry/def-pur-section-invariant.md,
displayed definition (blueprint: def-pur-section-invariant). -/
def condensedSectionInvariant (s : B ⟶ V) [IsClosedImmersion s.left]
    (_hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) :=
  let H := condensed_varying_dualizing_inverse D ell hell E n hn Λ hcoeff B V g
  let hp := H.choose
  let hd := H.choose_spec.choose
  let hcd := H.choose_spec.choose_spec.choose
  let ha := H.choose_spec.choose_spec.choose_spec.choose
  let U := H.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let hU := H.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  let unit : ConstantModelConstructibleFiniteTor Λ B.left := ⟨𝟙_ _, hU ▸ U.property⟩
  (moduleObjectDerivedPullback Λ s.left).obj
    ((@ctfExceptionalInverseImage Λ _ _ ell _ D.k _ hp hd hcd
      V B _ _ _ _ _ _ g ha).obj unit).obj

/-- The section invariant belongs to Dctf and has a two-sided tensor inverse there.
The tensor is the relative K-flat derived tensor over the pulled-back coefficient ring.
The isomorphisms are asserted as properties, so no orientation or Tate identification is
part of the invariant.

Source: latest blueprint sec-smooth-purity/sk-lem-geometry/def-pur-section-invariant.md,
final invertibility assertion (blueprint: def-pur-section-invariant).

Proof plan, following the four DAG steps:
1. Use the purity datum and pulled-back coefficient rings. The smooth native dualizing
object and its two-sided Dctf inverse are supplied by
lem-pur-condensed-varying-dualizing-inverse, with no pure-dimension assumption.
2. Pull back both objects along the closed section. It is separated of finite type by
lem-weil-pbc-closed-immersion-proper. At finite coefficients, use
lem-sf-module-object-ordinary-coefficient-equivalence and
lem-pe-finite-coefficient-model-comparison to identify the discrete internal modules,
their relative tensors and constructibility with the ordinary constant-coefficient model.
The section actions identify the inverse-image functors and hence their derived functors.
The tensor tests of def-weil-finite-tor-amplitude and
det-def-sfb-constructible-tor-amplitude agree, so lem-sf-pullback-tor-amplitude applies.
3. For each nonfinite coefficient, det-prop-sfb-module-pullback-exact-main identifies
cohomology of pullback with pullback of cohomology. Pull back a finite stratification and
its pro-etale covers. The finite constant matrices of
det-def-sfb-constructible-local-model and their cokernels pull back unchanged. The bounds
remain finite, and lem-integral-ctf-equals-bc on the qcqs base gives Dctf membership.
4. Let mu be the tensor comparison and u the unit comparison of
lem-sfb-derived-pullback-strong-monoidal. The first evaluation is the composite
C tensor Q --mu inverse--> Ls^*(omega tensor P) --Ls^*e--> Ls^*Lambda_V --u--> Lambda_B.
Use the reversed tensor and the second evaluation e' for the other isomorphism.
Both factors have Dctf membership by steps 2--3, giving the asserted Picard object. -/
theorem condensedSectionInvariant_invertible (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (constantModelBoundedConstructible Λ B.left ⊓ DerivedCategory.finiteTorAmplitude _)
      (condensedSectionInvariant D ell hell E n hn Λ hcoeff B V g s hs) ∧
    ∃ Q : ConstantModelConstructibleFiniteTor Λ B.left,
      Nonempty (((derivedTensor Λ B.left).obj
        (condensedSectionInvariant D ell hell E n hn Λ hcoeff B V g s hs)).obj Q.obj ≅
          𝟙_ _) ∧
      Nonempty (((derivedTensor Λ B.left).obj Q.obj).obj
        (condensedSectionInvariant D ell hell E n hn Λ hcoeff B V g s hs) ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
