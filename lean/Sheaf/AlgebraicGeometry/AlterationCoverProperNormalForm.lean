/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataRing
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.IntegralEtaleChartFlatification
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.FieldTheory.SylowSimultaneousFieldSections

/-!
# Proper normal form for alteration covers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Theorem 3.2.1,
printed pp. 29--30, with the finite affine-open refinement from Corollary 2.2.4,
printed p. 27 (blueprint: lem-per-alteration-cover-proper-normal-form).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- A finite alteration cover is dominated by a proper prime-to-ell integral cover followed
by a finite completely decomposed separated étale family. The object `base` in `hcover`
is the identity of `alt/X`, specified by its underlying object of `Over X`. The degree
is computed using the stalk map at the generic point of `Y`; the displayed generic-point
identity identifies its source with the function field of `X`. No integrality of `V i`
is imposed.

Source: ILO Exposé II, Theorem 3.2.1, pp. 29--30, and Corollary 2.2.4, p. 27
(blueprint: lem-per-alteration-cover-proper-normal-form).

Proof:
1. Use `lem-per-alteration-finite-normal-generator-tree` and induct on the height of the
   finite refinement tree. A leaf uses the identity. Finite type constructions stay
   Noetherian and quasi-excellent by `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-per-quasi-excellent-finite-type-stability`. Steps 2--8 prove the interchange of
   completely decomposed étale charts followed by proper prime-to-ell integral covers.
2. Apply `lem-per-integral-etale-chart-flatification` simultaneously to those covers.
   Obtain a normal integral modification `Z₀ → Z` and integral finite locally free covers
   `Bᵢ → Eᵢ⁰`, of the original generic ranks, mapping to the proper covers. The modification
   is surjective since its closed image contains a dense open; its degree is one.
   Complete decomposition survives pullback by lifting the residue-field rational points.
3. The integral étale charts have finite separable generic fields `Kᵢ/K`, by
   `lem-weil-pbc-etale-fibre-discrete-separable-points`, étale openness
   (`lem-weil-pbc-flat-lfp-open`) and
   `lem-weil-pbc-etale-algebra-residue-field-separable`. The generic fields `Fᵢ` of `Bᵢ`
   have the prescribed ranks: their generic coordinate rings are finite-dimensional
   domains, hence fields, using `lem-sc-integral-function-field-affine-fraction`.
   Invertibility of ell implies `char K ≠ ell`. Apply
   `lem-per-sylow-simultaneous-field-sections` to obtain a finite prime-to-ell `K'/K`
   and embeddings of `Fᵢ` into every field factor of `Kᵢ ⊗ K'`.
4. Normalize `Z₀` in `K'`, using `def-fin-normalization-extension`. This is finite:
   quasi-excellent rings are Nagata (`lem-exc-quasi-excellent-nagata`), hence their
   integral closures in finite extensions are finite by `def-weil-pbc-nagata-ring`
   and `def-weil-pbc-japanese-domain`. Normality and the function field identification
   follow from `lem-weil-pbc-integral-closure-finite-extension-normal` and
   `lem-weil-pbc-localization-normal-domain`.
5. The normalization `N → Z₀` is proper by `lem-weil-pbc-finite-proper` and surjective
   since its closed image contains the generic point. Compose with the modification,
   using `lem-weil-pbc-proper-fp-permanence`. Its degree remains `[K':K]`, and finite
   type gives Noetherianity and quasi-excellence by the stability lemmas of Step 1.
6. Pull the étale charts to `N`; étaleness and separated finite type persist by
   `lem-weil-pbc-etale-scheme-base-change` and `lem-pod-separated-finite-type-base-change`.
   Split into finitely many clopen normal integral components by
   `lem-fin-etale-normal-components`. Openness ensures every component meets the generic
   fibre; `lem-weil-pbc-etale-fibre-discrete-separable-points` identifies its field with
   one of the factors in Step 3, giving a generic section of the pulled-back finite cover.
7. That cover is finite by `def-pc-finite-locally-free` and
   `lem-trf-finite-radicial-basechange`. Take the reduced closure of the generic section
   (`lem-weil-pbc-reduced-induced-closed-subscheme`). It is finite and birational over
   the normal component by `lem-weil-pbc-closed-immersion-finite` and
   `lem-weil-pbc-finite-composition`, hence isomorphic by
   `lem-trf-finite-birational-normal-iso`. Its inverse extends the section.
8. The components form a finite completely decomposed family: rational points persist
   under pullback and lie on a component. Clopen inclusions preserve étaleness by
   `lem-weil-pbc-etale-composition-cancellation`; they are quasi-compact in Noetherian
   schemes, hence the family is separated finite type. Step 7 supplies all factorizations.
9. At a proper vertex, compose its cover with the inductively obtained proper cover,
   using `lem-weil-pbc-proper-fp-permanence`. Surjectivity composes and generic degrees
   multiply (multiply bases in the field tower), preserving coprimality with ell.
10. At an étale vertex apply the interchange to the inductively obtained proper covers.
    Pull back their subsequent étale families and compose, using the étale base-change
    and composition lemmas, `lem-pod-separated-finite-type-base-change`,
    `lem-weil-pbc-proper-fp-permanence` and `lem-sfb-finite-type-composition-base-change`.
    Residue-field isomorphisms compose, and the new family is finite.
11. Apply the induction at `X`, and compose the maps from the leaves to the original
    members `T b`. This gives the displayed factorizations and every asserted property. -/
theorem alteration_cover_proper_normal_form
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U.1))
    (ell : ℕ) [Fact ell.Prime]
    (hinv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    {B : Type w} [Finite B] (T : B → Alt X)
    (hcover : ∃ (base : Alt X) (_ : base.obj = Over.mk (𝟙 X))
      (q : ∀ b : B, T b ⟶ base), IsCoveringFamily ell T q) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (f : Y ⟶ X)
      (n : ℕ) (V : Fin n → Scheme.{u}) (v : ∀ i, V i ⟶ Y)
      (b : Fin n → B) (a : ∀ i, V i ⟶ (T (b i)).obj.left),
      IsNoetherian Y ∧ IsProper f ∧ Surjective f ∧
      f (genericPoint Y) = genericPoint X ∧
      (f.stalkMap (genericPoint Y)).hom.Finite ∧
      Nat.Coprime
        (@Module.finrank (X.presheaf.stalk (f (genericPoint Y))) Y.functionField _ _
          (@Algebra.toModule _ _ _ _ (f.stalkMap (genericPoint Y)).hom.toAlgebra)) ell ∧
      (LocallyOfFiniteType f ∧ QuasiCompact f) ∧
      (∀ i, IsSeparated (v i) ∧ Etale (v i) ∧
        LocallyOfFiniteType (v i) ∧ QuasiCompact (v i)) ∧
      (∀ y : Y, ∃ (i : Fin n) (z : V i),
        v i z = y ∧ IsIso ((v i).residueFieldMap z)) ∧
      (∀ i, a i ≫ (T (b i)).obj.hom = v i ≫ f) ∧
      (∀ i, LocallyOfFiniteType (v i ≫ f) ∧ QuasiCompact (v i ≫ f)) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
