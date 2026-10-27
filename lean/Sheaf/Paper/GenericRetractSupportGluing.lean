/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.Paper.NormalizedInternalSupportScalars
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.NoetherianComplementaryStratifications
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible
import Sheaf.Paper.ScalarModelImmersionExtension
import Sheaf.TraceFormula.ReducedSchemeImage
public import Mathlib.Order.CompletePartialOrder

/-! # Gluing a generic retract across a smaller closed support

Source: Stacks Project, proetale.tex, Tag 09AH, lemma-ses-associated-to-open;
agent derived support consequence, original tame-pair generator steps 8--9
(blueprint: lem-sfb-generic-retract-support-gluing).

The assertion uses the existing internal-module categories, constant scalar models and
canonical exact support extension through the scheme-theoretic image. Its local names
only abbreviate terms in this one assertion; no functor or coefficient ring is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open SupportedCommonField

/-- The clauses of the generic-retract support-gluing assertion, with the actual
internal-module functors. `F` is the closure of the boundary image, `w` its complementary
open, `e` the normalized exact extension, `o` its generic term, and `c` its error term.
The Noetherian structures are derived from finite type over the field, not assumed.
All local abbreviations here have explicit construction data.

Source: Stacks Project, proetale.tex, Tag 09AH, lemma-ses-associated-to-open;
agent derived support consequence, original tame-pair generator steps 8--9
(blueprint: lem-sfb-generic-retract-support-gluing). -/
def GenericRetractSupportGluingAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
    (U S : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (a : S ⟶ U) [IsImmersion a.left] {S₀ B : Scheme.{u}}
    (v : S₀ ⟶ S.left) [IsOpenImmersion v]
    (z : B ⟶ S.left) [IsClosedImmersion z] : Prop :=
  letI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  letI : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  letI : IsNoetherian U.left := ⟨⟩
  letI : IsLocallyNoetherian S.left := LocallyOfFiniteType.isLocallyNoetherian S.hom
  letI : CompactSpace S.left := QuasiCompact.compactSpace_of_compactSpace S.hom
  letI : IsNoetherian S.left := ⟨⟩
  letI : NoetherianSpace S₀ := v.isEmbedding.isInducing.noetherianSpace
  let F : Set U.left := closure (Set.range (z ≫ a.left))
  let w : U.left.Opens := ⟨Fᶜ, isClosed_closure.isOpen_compl⟩
  let e := support Λ a.left
  let e₀ := support Λ (v ≫ a.left)
  let r := pull Λ v
  let o := fun K : D Λ S.left ↦ e₀.obj (r.obj K)
  let c := fun K : D Λ S.left ↦ e.obj ((closed Λ z).obj ((pull Λ z).obj K))
  F ⊂ closure (Set.range a.left) ∧
    ∀ (M N : D Λ S.left), constantModelBoundedConstructible Λ S.left M →
      constantModelBoundedConstructible Λ S.left N →
      ∀ (ι : r.obj M ⟶ r.obj N) (ρ : r.obj N ⟶ r.obj M), ι ≫ ρ = 𝟙 (r.obj M) →
        (∀ K : D Λ S.left, K = M ∨ K = N →
          (∃ (f : o K ⟶ e.obj K) (g : e.obj K ⟶ c K)
            (h : c K ⟶ (o K)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (D Λ U.left)) ∧
          constantModelBoundedConstructible Λ U.left (c K) ∧
          IsZero ((pull Λ w.ι).obj (c K))) ∧
        e₀.map ι ≫ e₀.map ρ = 𝟙 (o M) ∧
        (∀ P : ObjectProperty (D Λ U.left), P.IsTriangulated →
          P.IsClosedUnderIsomorphisms → P.IsStableUnderRetracts → P (e.obj N) →
          (∀ K : D Λ U.left, constantModelBoundedConstructible Λ U.left K →
            IsZero ((pull Λ w.ι).obj K) → P K) →
          P (o N) ∧ P (o M) ∧ P (e.obj M)) ∧
        (Set.range v = Set.univ → IsZero (c M) ∧ IsZero (c N))

/-- A retract on a nonempty dense open glues, using two localization triangles,
modulo bounded constructible objects supported on a strictly smaller closed subset.
No extension of the generic projector is an input.

Source: Stacks Project, proetale.tex, Tag 09AH, lemma-ses-associated-to-open;
agent derived support consequence, original tame-pair generator steps 8--9
(blueprint: lem-sfb-generic-retract-support-gluing).

Proof plan, following the six steps of the DAG node:
1. Finite type over the field makes the schemes Noetherian. Use
   lem-sfb-noetherian-complementary-stratifications for qcqs and quasi-compact open
   immersions. The locally closed image S is open in its closure Z, so the nonempty
   open S₀ is open in Z. Its closed complement contains the boundary closure F,
   proving F is a proper closed subset of Z.
2. sk-prop-sfb-cartesian-coefficients identifies inverse-image coefficients with A_E.
   lem-weil-pbc-proetale-ringed-open-closed gives the open/closed localization SES;
   lem-sfb-internal-module-operations-transport carries it, its exact functors and
   adjunction maps to the actual internal-module categories.
3. For K=M,N, lem-weil-pbc-complex-ses-triangle gives the localization triangle.
   Apply the exact a_! termwise, using lem-sfb-locally-closed-extension-coherence
   and lem-weil-pbc-exact-functor-derived-factorization. The normalized composition
   comparison identifies its first term with (av)_! v^*K.
4. lem-sfb-pullback-constant-model-constructible and
   lem-sfb-scalar-model-immersion-extension preserve the finite constant models under
   z^*, z_* and the two factors of a_!. Exactness identifies their cohomology with
   the image of H^q(K), hence keeps the bounded cohomological interval.
5. Since B is reduced, lem-trf-reduced-scheme-image identifies the image of az with
   the reduced closed scheme on F. Coherence factors the error term through its
   closed direct image. Open/closed localization makes its restriction to U minus F
   zero. This is scheme-theoretic factorization, not just containment of point sets.
6. Functoriality preserves the displayed retract. Rotate the N triangle backwards:
   its generic term is a shifted cone of a_!N to its error term, hence belongs to P.
   Retract closure gives the M generic term; the M triangle then gives a_!M.
   If S₀=S, B is empty; the empty covering makes its module category zero, so both
   error terms vanish. Only the given generic maps and the two triangles are used.
-/
theorem genericRetractSupportGluing
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    {k : Type u} [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (U S : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (a : S ⟶ U) [IsImmersion a.left] [IsIntegral S.left]
    {S₀ B : Scheme.{u}} (v : S₀ ⟶ S.left) [IsOpenImmersion v] [Nonempty S₀]
    (_hv : DenseRange v) (z : B ⟶ S.left) [IsClosedImmersion z] [IsReduced B]
    (_hz : Set.range z = (Set.range v)ᶜ) :
    GenericRetractSupportGluingAssertions (normContinuousRing E).X U S a v z := by
  sorry

end AlgebraicGeometry.ProEtale
