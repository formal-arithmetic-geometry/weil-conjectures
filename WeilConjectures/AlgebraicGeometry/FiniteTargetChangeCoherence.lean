/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.NormalizedOriginScalarComparisons
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BasicOperationsCoefficientReduction

/-! # Coefficient change with a compatible finite-Tor target family

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-finite-verdier.proof.md, the resulting map, evaluation and quotient cocycle
(blueprint: lem-coef-finite-target-change-coherence).

The auxiliary records spell out the same equations in either of the two published
site presentations. Index n denotes exponent n + 1; a family indexed by Fin N has
exactly the levels 1 through N. Every comparison is the specified evaluation transpose
followed by the given target isomorphism. Targets need not be dualizing objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section Equations

variable {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
  {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
  {F : ∀ {i j : ℕ}, j ≤ i → C i ⥤ C j}

/-- A finite family of the targets in the node, with the canonical scalar unit and
reassociation written explicitly. P is the recorded finite-Tor constructibility predicate.
Source: cor-coef-finite-verdier.proof.md, compatible target identifications
(blueprint: lem-coef-finite-target-change-coherence). -/
structure FiniteTargetChangeFamily
    (α : ∀ {i j r : ℕ} (h : j ≤ i) (k : r ≤ j), F h ⋙ F k ≅ F (k.trans h))
    (ε : ∀ i : ℕ, F (le_refl i) ≅ 𝟭 (C i))
    (P : ∀ i : ℕ, ObjectProperty (C i)) (N : ℕ) where
  obj : ∀ i : Fin N, C i.val
  constructible : ∀ i : Fin N, P i.val (obj i)
  transition : ∀ (i j : Fin N) (h : j.val ≤ i.val), (F h).obj (obj i) ≅ obj j
  unit : ∀ i : Fin N, (transition i i (le_refl i.val)).hom = (ε i.val).hom.app (obj i)
  cocycle : ∀ (i j r : Fin N) (h : j.val ≤ i.val) (k : r.val ≤ j.val),
    (α h k).hom.app (obj i) ≫ (transition i r (k.trans h)).hom =
      (F k).map (transition i j h).hom ≫ (transition j r k).hom

/-- The target-changed arrow h is literally H(1,u) after the evaluation-defined v.
Source: cor-coef-finite-verdier.proof.md, 'The resulting map is d'
(blueprint: lem-coef-finite-target-change-coherence). -/
def finiteTargetChangeArrow
    (S : FiniteHomQuotientClosedData C H F)
    {α : ∀ {i j r : ℕ} (h : j ≤ i) (k : r ≤ j), F h ⋙ F k ≅ F (k.trans h)}
    {ε : ∀ i : ℕ, F (le_refl i) ≅ 𝟭 (C i)}
    {P : ∀ i : ℕ, ObjectProperty (C i)} {N : ℕ}
    (Ω : FiniteTargetChangeFamily α ε P N) (i j : Fin N) (h : j.val ≤ i.val)
    (K : C i.val) :
    (F h).obj ((H i.val).obj (op K, Ω.obj i)) ⟶
      (H j.val).obj (op ((F h).obj K), Ω.obj j) :=
  S.comparison h K (Ω.obj i) ≫
    (H j.val).map (Prod.mkHom (𝟙 (op ((F h).obj K))) (Ω.transition i j h).hom)

/-- The isomorphism, source naturality, evaluation, quotient cocycle, unit and target
naturality clauses for the explicitly defined arrow. The inverse associator in the
contravariant input is written on the two-step side of the cocycle.
Source: cor-coef-finite-verdier.proof.md, evaluation and quotient cocycle
(blueprint: lem-coef-finite-target-change-coherence). -/
structure FiniteTargetChangeLaws
    (S : FiniteHomQuotientClosedData C H F)
    (α : ∀ {i j r : ℕ} (h : j ≤ i) (k : r ≤ j), F h ⋙ F k ≅ F (k.trans h))
    (ε : ∀ i : ℕ, F (le_refl i) ≅ 𝟭 (C i))
    (P : ∀ i : ℕ, ObjectProperty (C i)) (N : ℕ) : Prop where
  isIso : ∀ (Ω : FiniteTargetChangeFamily α ε P N)
    (i j : Fin N) (h : j.val ≤ i.val) (K : C i.val), P i.val K →
      IsIso (finiteTargetChangeArrow S Ω i j h K)
  naturality : ∀ (Ω : FiniteTargetChangeFamily α ε P N)
    (i j : Fin N) (h : j.val ≤ i.val) (K L : C i.val), P i.val K → P i.val L →
    ∀ f : K ⟶ L,
      (F h).map ((H i.val).map (Prod.mkHom f.op (𝟙 (Ω.obj i)))) ≫
          finiteTargetChangeArrow S Ω i j h K =
        finiteTargetChangeArrow S Ω i j h L ≫
          (H j.val).map (Prod.mkHom ((F h).map f).op (𝟙 (Ω.obj j)))
  evaluation : ∀ (Ω : FiniteTargetChangeFamily α ε P N)
    (i j : Fin N) (h : j.val ≤ i.val) (K : C i.val), P i.val K →
      (S.closed j.val).tensor.map
          (Prod.mkHom (finiteTargetChangeArrow S Ω i j h K) (𝟙 ((F h).obj K))) ≫
          (S.closed j.val).evaluation ((F h).obj K) (Ω.obj j) =
        (S.tensor h).inv.app ((H i.val).obj (op K, Ω.obj i), K) ≫
          (F h).map ((S.closed i.val).evaluation K (Ω.obj i)) ≫
          (Ω.transition i j h).hom
  cocycle : ∀ (Ω : FiniteTargetChangeFamily α ε P N)
    (i j r : Fin N) (h : j.val ≤ i.val) (k : r.val ≤ j.val)
    (K : C i.val), P i.val K →
      (α h k).hom.app ((H i.val).obj (op K, Ω.obj i)) ≫
          finiteTargetChangeArrow S Ω i r (k.trans h) K =
        (F k).map (finiteTargetChangeArrow S Ω i j h K) ≫
          finiteTargetChangeArrow S Ω j r k ((F h).obj K) ≫
          (H r.val).map (Prod.mkHom ((α h k).inv.app K).op (𝟙 (Ω.obj r)))
  unit : ∀ (Ω : FiniteTargetChangeFamily α ε P N) (i : Fin N)
    (K : C i.val), P i.val K →
      finiteTargetChangeArrow S Ω i i (le_refl i.val) K ≫
          (H i.val).map (Prod.mkHom ((ε i.val).inv.app K).op (𝟙 (Ω.obj i))) =
        (ε i.val).hom.app ((H i.val).obj (op K, Ω.obj i))
  target_naturality : ∀ (Ω Ω' : FiniteTargetChangeFamily α ε P N)
    (t : ∀ i : Fin N, Ω.obj i ⟶ Ω'.obj i),
    (∀ (i j : Fin N) (h : j.val ≤ i.val),
      (Ω.transition i j h).hom ≫ t j =
        (F h).map (t i) ≫ (Ω'.transition i j h).hom) →
    ∀ (i j : Fin N) (h : j.val ≤ i.val) (K : C i.val), P i.val K →
      finiteTargetChangeArrow S Ω i j h K ≫
          (H j.val).map (Prod.mkHom (𝟙 (op ((F h).obj K))) (t j)) =
        (F h).map ((H i.val).map (Prod.mkHom (𝟙 (op K)) (t i))) ≫
          finiteTargetChangeArrow S Ω' i j h K

end Equations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The scalar identity unit on the etale site, the mate of identity restriction.
The equality supplied to the published unit is the quotient-factor identity lifted to
ULift, so no choice of a self-equivalence occurs.
Source: cor-coef-finite-verdier.proof.md, canonical scalar units
(blueprint: lem-coef-finite-target-change-coherence). -/
def finiteTargetEtaleUnit (n : ℕ) :
    finiteHomEtaleReduction l E X (le_refl n) ≅ 𝟭 (finiteHomEtale l E X n) :=
  ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
    (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
      (S := Padic.coefficientExtensionIdeal l E (n + 1))))

/-- The intrinsic scalar identity unit, the mate of the published normalized restriction unit.
Source: cor-coef-finite-verdier.proof.md, canonical scalar units
(blueprint: lem-coef-finite-target-change-coherence). -/
def finiteTargetIntrinsicUnit (n : ℕ) :
    coefficientFiniteQuotientDerived l E X (le_refl n) ≅
      𝟭 (normalizedDVRDerived l E X n) :=
  Adjunction.leftAdjointIdIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (le_refl n)) (normalizedDVRResUnit l E X n)

/-- The already normalized pro-etale closed and scalar-tensor data as a shared diagram.
Source: cor-coef-finite-verdier.proof.md, the comparison from thm-coef-finite-hom
(blueprint: lem-coef-finite-target-change-coherence). -/
def finiteTargetIntrinsicData : FiniteHomQuotientClosedData
    (normalizedDVRDerived l E X) (coefficientFiniteInternalHom l E X)
    (coefficientFiniteQuotientDerived l E X) where
  closed := finiteIntrinsicClosed l E X
  tensor := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor

/-- Evaluation and coherence after changing an arbitrary compatible finite-Tor target family.
Source: cor-coef-finite-verdier.proof.md, 'The resulting map is d', evaluation compatibility,
and 'The cocycle is their quotient cocycle'
(blueprint: lem-coef-finite-target-change-coherence).

Proof:
1. Scalar extension preserves the finite-Tor constructible domain, by
lem-coef-finite-hom-domain-calculus on the etale site and lem-coef-closed-scalar-domains
on the pro-etale site. Apply thm-coef-finite-hom to (K, Omega_i).
2. Postcomposition H(1,u) is invertible with inverse H(1,u inverse). Compose with the
invertible canonical comparison v. Bifunctoriality and naturality of v give the
contravariant naturality square for any morphism K to L in the finite-Tor domain.
3. Naturality of the tensor-Hom counit in its target moves u outside evaluation.
The evaluation identity for v then identifies the result with scalar-extended evaluation
followed by u, with precisely the specified inverse tensor comparison.
4. For i >= j >= r, naturality of v in the target moves scalar extension of H(1,u_ij)
past v_jr. Functoriality combines the two target maps. The quotient cocycle for v and
the assumed cocycle for u identify this composite with h_ir. The scalar associators
act on Hom and on K, in inverse directions for the contravariant input.
5. At i = j, uniqueness of the transpose of evaluation gives the identity comparison
under the canonical scalar unit, and the assumed unit for u gives the displayed unit.
For a compatible target-family morphism t, move H(1,t) across v by covariant naturality
and use t_j after u_ij = u'_ij after scalar extension of t_i. No t_i need be invertible.
These arguments apply to both sites and require no geometric dualizing property. -/
theorem finiteTargetChange_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (N : ℕ) (_hN : 1 ≤ N) :
    FiniteTargetChangeLaws (finiteHomEtaleData l E X) (finiteHomEtaleAssoc l E X)
      (finiteTargetEtaleUnit l E X)
      (fun n ↦ finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) N ∧
    FiniteTargetChangeLaws (finiteTargetIntrinsicData l E X) (finiteHomIntrinsicAssoc l E X)
      (finiteTargetIntrinsicUnit l E X)
      (fun n ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X) N := by
  sorry

end WeilConjectures
