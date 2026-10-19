/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.RingedModuleSkyscraper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization
import Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Sheaf.RingTheory.RegularLocalDimOneIffNormal
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import Sheaf.TraceFormula.CurveNormalizationCompletion
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.RingTheory.SimpleFiltration

/-!
# The normalization quotient of a reduced algebraic curve

Source: Stacks Project, Varieties, Tag 0C1R, parts (1)--(4), (7), (9)
(blueprint: lem-trf-normalization-singular-skyscraper).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The actual ring stalk of the direct image of the normalization's structure sheaf.
Source: Stacks Project, Varieties, Tag 0C1R(3)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
abbrev normalizationPushforwardStalk (X : Scheme.{u}) (x : X) : Type u :=
  ((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
    X.reducedNormalization.presheaf).stalk x

/-- The scalar action on the normalization stalk comes from the structure-sheaf map.
Source: Stacks Project, Varieties, Tag 0C1R(3)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
noncomputable instance normalizationPushforwardStalkAlgebra (X : Scheme.{u}) (x : X) :
    Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat x).map X.fromReducedNormalization.c).hom.toAlgebra

/-- The quotient C_x/A_x is the module quotient by the image of the structural inclusion.
Source: Stacks Project, Varieties, Tag 0C1R(4)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
abbrev normalizationQuotientStalk (X : Scheme.{u}) (x : X) : Type u :=
  normalizationPushforwardStalk X x ⧸
    (Algebra.linearMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x)).range

/-- The maximal-ideal completion of the local ring A_x.
Source: Stacks Project, Varieties, Tag 0C1R(7)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
abbrev normalizationBaseCompletion (X : Scheme.{u}) (x : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The ideal m_x C_x defining the completion of the normalization stalk.
Source: Stacks Project, Varieties, Tag 0C1R(7)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
abbrev normalizationCompletionIdeal (X : Scheme.{u}) (x : X) :
    Ideal (normalizationPushforwardStalk X x) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
    (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X x))

/-- The completion of C_x with respect to m_x C_x, namely lim C_x/m_x^n C_x.
Source: Stacks Project, Varieties, Tag 0C1R(7)
(blueprint: lem-trf-normalization-singular-skyscraper). -/
abbrev normalizationStalkCompletion (X : Scheme.{u}) (x : X) : Type u :=
  AdicCompletion (normalizationCompletionIdeal X x) (normalizationPushforwardStalk X x)

/-- The normalization quotient is the finite sum of its nonzero finite-length singular
stalk quotients, and these quotients are unchanged by completion. The completion map `i`
is specified at every quotient level; `e` identifies its target with the integral closure
of the completed base, and `eM` is induced by completing representatives in C_x.

Source: Stacks Project, Varieties, Tag 0C1R, parts (1)--(4), (7), (9)
(blueprint: lem-trf-normalization-singular-skyscraper).

Proof:
1. The empty scheme gives the empty singular set and zero quotient. Otherwise finite type
   over the Noetherian field makes X Noetherian. Reduced algebraic normalization gives
   a finite surjective normalization, isomorphic over the dense open normal locus N.
2. On an affine Spec R, normalization has ring the product of the integral closures of
   R/p in their fraction fields for minimal primes p. The reduced Noetherian total-fraction
   decomposition identifies this product with the integral closure of R in Q(R).
3. Localize this description at x. Affine pushforward stalk localization and commutation of
   integral closure with localization identify the actual C_x with the integral closure of
   A_x in Q(A_x). It is finite over A_x and the structural map is injective.
4. The affine injections give a monomorphism of structure sheaves. The structure sheaf,
   its finite pushforward, and its cokernel Q are coherent on the locally Noetherian scheme.
   Exactness of stalks identifies Q_x with C_x/A_x.
5. A reduced Noetherian ring is normal iff integrally closed in its total fractions; a local
   normal ring is a domain. Thus Supp Q is the complement of N. It is closed and misses all
   generic points. Pure dimension one and Noetherianity make it a finite set of closed points.
6. Closed points have dimension-one local rings and structural residue field k. The regular
   local/separable-residue smoothness criterion and regular/normal equivalence in dimension
   one identify this support with the nonsmooth locus. Over the perfect field k the normal
   open N is regular and hence smooth, also accounting for nonclosed points.
7. Each nonzero finite Q_x is supported only at the maximal ideal: all other primes of A_x
   are minimal and the corresponding generic stalks vanish. The finite-module point-support
   criterion gives finite length, and the simple-filtration lemma supplies the stated chain.
8. The stalk-skyscraper adjunction gives Q to each skyscraper of Q_x by taking germs. Assemble
   these maps using the finite sum/product identification. At each singular point the stalk
   map is the identity, and elsewhere both stalks vanish, so the stalkwise criterion gives
   the claimed isomorphism with exactly the germ scalar action.
9. The local ring A_x is reduced, one-dimensional and essentially finite type over k. The
   curve-normalization/completion lemma and finite-module completion/tensor comparison
   identify the completion of C_x with the integral closure of the completion of A_x.
   On pure tensors the map is a tensor c sent to a times the completed image of c, so it
   respects multiplication and the structural map. At every finite quotient this is the
   map induced by A_x to C_x, giving the displayed normalization of i.
10. A simple module over a local ring is killed by its maximal ideal. A filtration of length
    r therefore gives m_x^r M_x = 0. The completion system of M_x is constant from r onward,
    so its canonical completion map is an A_x-linear isomorphism.
11. Exactness of completion on finite modules applied to 0 to A_x to C_x to M_x to 0 gives
    0 to Ahat_x to Chat_x to Mhat_x to 0. The quotient isomorphism composed with completion
    of representatives agrees with the isomorphism of step 10. Hence that natural map is
    the asserted eM, with the displayed formula on every representative c.

Proof dependencies by step:
1. lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-reduced-algebraic-normalization-field-
   change, lem-sc-noetherian-finite-irreducible-components
2. lem-weil-pbc-reduced-algebraic-normalization-field-change, def-weil-pbc-reduced-normalization,
   def-sc-normalization, lem-weil-pbc-relative-normalization, lem-weil-pbc-reduced-noetherian-
   total-ring-fractions, lem-weil-pbc-finite-algebra-is-integral
3. lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian, lem-sc-
   affine-pushforward-stalk-localization, lem-weil-pbc-integral-closure-commutes-localization,
   lem-weil-pbc-reduced-noetherian-total-ring-fractions
4. pqf-lem-coherent-ft-locnoeth, lem-weil-pbc-finite-pushforward-coherent, lem-weil-pbc-coherent-
   modules-kernel-cokernel-sum, lem-weil-pbc-module-stalk-exact
5. lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions, lem-weil-pbc-noetherian-
   finitely-many-minimal-primes, lem-weil-pbc-reduced-noetherian-total-ring-fractions, lem-sc-
   noetherian-closed-subset-finite-components
6. lem-weil-pbc-closed-point-residue-field-base, lem-weil-pbc-regular-local-separable-residue-
   smooth, lem-weil-pbc-regular-local-dim-one-iff-normal, lem-trf-regular-perfect-field-smooth
7. lem-weil-pbc-spec-tilde-stalk-localization, lem-sc-generic-stalk-finite-length, lem-weil-pbc-
   finite-length-module-simple-filtration
8. lem-weil-pbc-module-skyscraper-stalk-adjunction, lem-weil-pbc-module-iso-on-stalks
9. lem-trf-curve-normalization-completion, lem-weil-pbc-completion-finite-module-tensor
10. Elementary finite-length argument.
11. lem-weil-pbc-completion-exact-finite-modules
-/
theorem normalization_singular_skyscraper
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (hpure : ∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = 1)
    (S : Set X) (hS : S = {x : X | x ∉ (X ↘ Spec (.of k)).smoothLocus}) :
    S.Finite ∧
    (∀ x : S, IsClosed ({x.val} : Set X) ∧
      ∃ e : X.residueField x.val ≅ CommRingCat.of k,
        Spec.map e.inv = X.fromSpecResidueField x.val ≫ (X ↘ Spec (.of k))) ∧
    IsFinite X.fromReducedNormalization ∧
    RingedSpace.IsCoherent X.toRingedSpace (Modules.unit X) ∧
    RingedSpace.IsCoherent X.toRingedSpace
      ((Modules.pushforward X.fromReducedNormalization).obj
        (Modules.unit X.reducedNormalization)) ∧
    (∃ (Q : X.Modules)
      (q : (Modules.pushforward X.fromReducedNormalization).obj
        (Modules.unit X.reducedNormalization) ⟶ Q)
      (hq : SheafOfModules.unitToPushforwardObjUnit
        X.fromReducedNormalization.toRingCatSheafHom ≫ q = 0),
      (ShortComplex.mk (SheafOfModules.unitToPushforwardObjUnit
        X.fromReducedNormalization.toRingCatSheafHom) q hq).ShortExact ∧
      RingedSpace.IsCoherent X.toRingedSpace Q ∧
      Nonempty (Q ≅ ∐ (fun x : S ↦
        SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x.val
          (ModuleCat.of (X.presheaf.stalk x.val) (normalizationQuotientStalk X x.val))))) ∧
    (∀ x : S,
      Nonempty (normalizationPushforwardStalk X x.val ≃ₐ[X.presheaf.stalk x.val]
        integralClosure (X.presheaf.stalk x.val) (FractionRing (X.presheaf.stalk x.val))) ∧
      Nontrivial (normalizationQuotientStalk X x.val) ∧
      (∃ (r : ℕ) (F : Fin (r + 1) →
          Submodule (X.presheaf.stalk x.val) (normalizationQuotientStalk X x.val)),
        F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧
        (∀ j : Fin r, F j.castSucc < F j.succ) ∧
        (∀ j : Fin r, IsSimpleModule (X.presheaf.stalk x.val)
          (F j.succ ⧸ Submodule.comap (F j.succ).subtype (F j.castSucc)))) ∧
      ∃ i : normalizationBaseCompletion X x.val →ₐ[X.presheaf.stalk x.val]
          normalizationStalkCompletion X x.val,
        (∀ (n : ℕ) (a : normalizationBaseCompletion X x.val) (b : X.presheaf.stalk x.val),
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x.val)) n a =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (X.presheaf.stalk x.val)) ^ n) b →
          AdicCompletion.evalₐ (normalizationCompletionIdeal X x.val) n (i a) =
            Ideal.Quotient.mk ((normalizationCompletionIdeal X x.val) ^ n)
              (algebraMap (X.presheaf.stalk x.val) (normalizationPushforwardStalk X x.val) b)) ∧
        Function.Injective i ∧
        ∃ e : normalizationStalkCompletion X x.val ≃+*
            integralClosure (normalizationBaseCompletion X x.val)
              (FractionRing (normalizationBaseCompletion X x.val)),
          (∀ a : normalizationBaseCompletion X x.val,
            e (i a) = algebraMap (normalizationBaseCompletion X x.val)
              (integralClosure (normalizationBaseCompletion X x.val)
                (FractionRing (normalizationBaseCompletion X x.val))) a) ∧
          ∃ eM : normalizationQuotientStalk X x.val ≃ₗ[X.presheaf.stalk x.val]
              (normalizationStalkCompletion X x.val ⧸ i.toLinearMap.range),
            ∀ c : normalizationPushforwardStalk X x.val,
              eM (Submodule.Quotient.mk c) = Submodule.Quotient.mk
                (AdicCompletion.of (normalizationCompletionIdeal X x.val)
                  (normalizationPushforwardStalk X x.val) c)) := by
  sorry

end AlgebraicGeometry.Scheme
