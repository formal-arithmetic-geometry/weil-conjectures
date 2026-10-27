/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Limits

import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.NodalClosedPointsReduced
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Preparation for adjunction on a nodal curve

Source: Stacks Project, curves.tex, Tags 0C4E and 0E37; algebra.tex, Tags 00SC and
061L; duality.tex, Tag 0B6V (blueprint: lem-trf-nodal-adjunction-preparation).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite-type pure one-dimensional curve over an algebraically closed field, whose
nonsmooth points are closed ordinary double points, has the stated finiteness,
reducedness, regular presentations and canonical adjunction line. No separatedness or
properness assumption is imposed. The scalar equation on the completed-ring equivalence
says exactly that it is an equivalence of k-algebras for the structure map p.

Source: Stacks Project, curves.tex, Tags 0C4E and 0E37; algebra.tex, Tags 00SC and
061L; duality.tex, Tag 0B6V (blueprint: lem-trf-nodal-adjunction-preparation).

Proof plan, in the order of the eight DAG steps:
1. Finite type over the Noetherian field gives a quasi-compact locally Noetherian
   scheme (lem-weil-pbc-finite-type-over-noetherian). Flatness follows from
   lem-pc-flat-field; pqf-lem-lft-fp-locnoeth gives local finite presentation.
   Local Noetherianity gives quasi-separatedness, and morphism permanence gives
   quasi-separatedness of p (lem-weil-pbc-locally-noetherian-quasi-separated and
   lem-weil-pbc-qcqs-morphism-permanence).
2. Use k as its algebraic closure in lem-trf-nodal-curve-lci-criterion: the affine
   lci cover exists and the Fitting singular subscheme is unramified over k.
   Lem-trf-nodal-points-reduced-algebraically-closed gives reducedness.
3. Lem-trf-field-curve-fitting-smooth-preparation identifies the support with the
   nonsmooth locus. Lem-trf-unramified-field-fibre-decomposition decomposes it into
   spectra of finite separable extensions, all equal to k. Its closed support is
   quasi-compact, so the disjoint singleton cover has a finite subcover.
4. A nonsmooth generic point would be closed. Its irreducible component would be a
   singleton of dimension zero, contradicting pure dimension one.
5. Lem-trf-relative-dimension-base-change applied to the sole fibre C gives pure
   dimension one for each nonempty geometric fibre, without identifying its space
   with that of C.
6. Lem-trf-lci-pointwise-criterion supplies a global complete intersection near x.
   Lem-trf-locally-algebraic-dimension-components gives local dimension one;
   lem-weil-pbc-global-complete-intersection-equidimensional identifies it with n-c,
   so c=n-1.
7. Lem-weil-pbc-global-complete-intersection-local-regular-sequence gives regularity
   at the ambient prime. Noetherianity of the polynomial ring follows from
   lem-weil-pbc-finite-type-algebra-noetherian. Spread the equations by
   lem-exc-regular-sequence-principal-neighbourhood, and use
   lem-weil-pbc-principal-localization-open-immersion to obtain an affine open
   source closed in an open of affine n-space with c=n-1 regular equations.
8. Apply lem-trf-flat-lci-canonical-adjunction with d=1. Its normalized system
   gives the invertible line and canonical comparison on the smooth locus. The
   first exterior power is canonically the differential module: on every open,
   send the wedge of the one-entry tuple a to a(0), and sheafify. This converts
   the normalized exterior-power comparison to the displayed identification. -/
theorem nodal_adjunction_preparation
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (p : C ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, x ∉ p.smoothLocus →
      IsClosed ({x} : Set C) ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
        ∀ a : k, e (algebraMap (C.presheaf.stalk x) _
          (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ ⊤ le_top ≫
            C.presheaf.germ ⊤ x trivial).hom a)) = algebraMap k _ a) :
    IsNoetherian C ∧ IsReduced C ∧ Flat p ∧
    LocallyOfFinitePresentation p ∧ QuasiSeparated p ∧
    HasPureFlatLCIGeometricFibres p 1 ∧
    (∀ x : C, ∃ U : C.affineOpens, x ∈ U.1 ∧
      ∃ ft : @Algebra.FiniteType k Γ(C, U.1) _ _
          ((p.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra,
        @Algebra.IsLocalCompleteIntersection k Γ(C, U.1) _ _
          ((p.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra ft ∧
          Nonempty (FlatLCIPresentation p 1 U.1)) ∧
    (∃ (I : Type u) (_ : Finite I)
      (e : (∐ fun _ : I ↦ Spec (.of k)) ≅ (Scheme.firstFittingIdealSheaf p).subscheme),
      ∀ i : I, Sigma.ι (fun _ : I ↦ Spec (.of k)) i ≫ e.hom ≫
        Scheme.firstFittingSingularSubscheme p ≫ p = 𝟙 _) ∧
    Set.range (Scheme.firstFittingSingularSubscheme p) = (p.smoothLocus : Set C)ᶜ ∧
    (∀ (Z : Set C), Z ∈ irreducibleComponents C →
      ∀ ξ : C, IsGenericPoint ξ Z → ξ ∈ p.smoothLocus) ∧
    (∃ F : FlatLCIAdjunctionSystem p 1, F.IsNormalized ∧
      ∃ e : (Scheme.Modules.tensorPullback p.smoothLocus.ι).obj
          (F.line (FlatLCIBaseChange.identity p)) ≅
          (p.smoothLocus.ι ≫ p).relativeDifferentials,
        ∃ w : Scheme.Modules.exteriorSheaf
            (p.smoothLocus.ι ≫ p).relativeDifferentials 1 ≅
            (p.smoothLocus.ι ≫ p).relativeDifferentials,
          (∀ (V : p.smoothLocus.toScheme.Opens)
            (a : Fin 1 → Γ((p.smoothLocus.ι ≫ p).relativeDifferentials, V)),
            w.hom.app V (Scheme.Modules.exteriorSheafSection
              (p.smoothLocus.ι ≫ p).relativeDifferentials 1 V a) = a 0) ∧
          F.IsSmoothComparison (FlatLCIBaseChange.identity p) p.smoothLocus (e ≪≫ w.symm)) := by
  sorry

end AlgebraicGeometry
