/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch
public import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.DirectSum.Module

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.StacksNodalClosedSubcurve
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # The base ideal and boundary colength of a nodal linear series

Source: Franciosi--Tenni, On Clifford's theorem for singular curves,
Proposition 2.17(ii) and Theorem 3.9 proof, printed pp. 233 and 247;
Stacks Project, curves.tex, Tag 0E38, and varieties.tex, Tag 0AYT
(blueprint: lem-sfb-nodal-linear-series-base-colength).

Sections are written as morphisms from the structure module. The base ideal is
characterized on affine opens by the evaluation span; it is not chosen from an
uncharacterized existence assertion. Section equalities are ranges of the canonical
inclusions. The auxiliary definitions only name the component unions, boundary sets,
and coordinate vector spaces occurring in this statement.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The component-generic value of a global section, as its germ.
Source: Franciosi--Tenni, Proposition 2.17(ii), p. 233
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
noncomputable def nodalSeriesGenericValue {X : Scheme.{u}} (L : X.Modules)
    (s : Scheme.Modules.unit X ⟶ L) (C : irreducibleComponents X) :
    L.presheaf.stalk (genericPoints.ofComponent C).1 :=
  L.presheaf.germ ⊤ (genericPoints.ofComponent C).1 trivial
    (s.app ⊤ (1 : Γ(X, ⊤)))

/-- The reduced closed union of a collection of irreducible components, via its ideal.
Closure makes the construction meaningful before finiteness of the components is used.
Source: Stacks Project, curves.tex, Tag 0E38
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
noncomputable def nodalSeriesUnionIdeal {X : Scheme.{u}}
    (S : Set (irreducibleComponents X)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure {x : X | ∃ C ∈ S, x ∈ C.1}, isClosed_closure⟩

/-- Nodes crossing two different blocks, described by their incident components.
Source: Franciosi--Tenni, Theorem 3.9 proof, p. 247; Stacks Project, Tag 0E38
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
def nodalSeriesBoundary {X : Scheme.{u}} (P : Setoid (irreducibleComponents X)) : Set X :=
  {x | ∃ C D : irreducibleComponents X,
    ¬ P.r C D ∧ x ∈ C.1 ∧ x ∈ D.1}

/-- The boundary of one block, including its precise underlying set.
Source: Stacks Project, curves.tex, Tag 0E38
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
def nodalSeriesBlockBoundary {X : Scheme.{u}}
    (P : Setoid (irreducibleComponents X)) (a : Quotient P) : Set X :=
  {x | ∃ C D : irreducibleComponents X,
    Quotient.mk P C = a ∧ Quotient.mk P D ≠ a ∧ x ∈ C.1 ∧ x ∈ D.1}

/-- The reduced ideal of the nodes crossing the partition.
Source: Franciosi--Tenni, Theorem 3.9 proof, p. 247
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
noncomputable def nodalSeriesBoundaryIdeal {X : Scheme.{u}}
    (P : Setoid (irreducibleComponents X)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure (nodalSeriesBoundary P), isClosed_closure⟩

/-- The coordinate space of a closed subscheme with its specified k-scalar action.
Source: Stacks Project, varieties.tex, Tag 0AYT
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
noncomputable def nodalSeriesCoordinateSpace (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (I.subschemeι ≫ X ↘ Spec (.of k)).appTop).hom).obj
        (ModuleCat.of Γ(I.subscheme, ⊤) Γ(I.subscheme, ⊤))

/-- The k-length used for the finite base and boundary schemes.
Source: Stacks Project, varieties.tex, Tag 0AYT
(blueprint: lem-sfb-nodal-linear-series-base-colength). -/
noncomputable def nodalSeriesLength (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData) : ℕ :=
  Module.finrank k (nodalSeriesCoordinateSpace k I)

/-- Base-ideal coherence, finite colength, partition boundaries, and adjoining the base
scheme to a Cartier cluster without changing its complete canonical series.

Source: Franciosi--Tenni, Proposition 2.17(ii) and Theorem 3.9 proof, pp. 233 and 247;
Stacks Project, curves.tex, Tag 0E38, modules.tex, Tag 01BY, and varieties.tex,
Tags 06LH, 08AA and 0AYT (blueprint: lem-sfb-nodal-linear-series-base-colength).

Proof:
1. Projectivity gives properness (lem-kun-projective-implies-proper). The proper-field
   preparation (lem-trf-proper-field-invertible-coherent) gives Noetherianity and coherence.
   On a trivializing affine open write a basis of V as f_i e and take the ideal (f_i).
   Changing the generator multiplies all f_i by a unit, so these ideals glue. The finite
   sum, cokernel and kernel coherence theorem
   (lem-weil-pbc-coherent-modules-kernel-cokernel-sum) makes the evaluation image coherent;
   tensoring by the inverse line gives coherence of B and its quotient.
2. The generically nonzero section generates at each component generic point, since a
   reduced generic local ring is a field. Thus V(B) misses those points. Apply
   lem-pc-nowhere-dense-dim-zero and lem-pc-zero-dimensional-closed-subscheme-finite.
   The empty base scheme is allowed.
3. The reduced complementary component union is the scheme-theoretic closure of the
   complement: its affine ideal is the intersection of the complementary minimal primes.
   Apply lem-trf-stacks-nodal-closed-subcurve (Tag 0E38). Each block intersection is a
   finite disjoint union of reduced points at exactly its boundary nodes. Algebraic
   closedness makes their residue fields k, so its length is the number of these points.
4. A block-supported section restricts to zero on the reduced complementary union,
   because its coefficients vanish in all the component fraction fields. Thus each
   summand vanishes at every node crossing the partition. The evaluation generators
   belong to those maximal ideals, giving B ≤ I_E. The exact quotient sequence and
   lem-pc-euler-additive, lem-pc-chi-zero-dim-support give b ≥ #E. Coherence of these
   quotients also uses pqf-lem-coherent-ft-locnoeth and the coherence theorem in step 1.
5. If V is complete, each global section factors through the evaluation image via
   s tensor 1. The canonical inclusion is injective and surjective on global sections.
6. Locally I_T=(t), with t a nonzerodivisor, so multiplication identifies I_T tensor B
   with I_T B. The product is coherent and its zero scheme is supported on T union Z,
   hence zero-dimensional and finite by lem-pc-zero-dimensional-closed-subscheme-finite.
   It is contained in I_T, so its subscheme contains T. The exact sequence with terms
   I_T/I_T B, O/I_T B and O/I_T, and the identification of the first with
   I_T tensor (O/B), give length(Tbar)=length(T)+b by lem-pc-chi-zero-dim-support and
   lem-pc-euler-additive. The product inclusions into omega agree with multiplication,
   and step 5 gives equality of the canonical section subspaces. No Cartier condition
   on Tbar is asserted.
-/
theorem exists_nodal_linear_series_base_colength
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) →
      x ∉ (X ↘ Spec (.of k)).smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
        ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)
          (X.presheaf.germ ⊤ x trivial (Scheme.globalSectionsRingHom k a))) =
            Ideal.Quotient.mk _ (MvPowerSeries.C a))
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k (Scheme.Modules.unit X ⟶ L)) [FiniteDimensional k V]
    (hgeneric : ∃ s ∈ V, ∀ C : irreducibleComponents X, nodalSeriesGenericValue L s C ≠ 0) :
    ∃ B : X.IdealSheafData,
      (∀ U : X.affineOpens,
        B.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) =
          Submodule.span Γ(X, U.1) {t | ∃ s ∈ V, s.app U.1 (1 : Γ(X, U.1)) = t}) ∧
      RingedSpace.IsCoherent X.toRingedSpace B.toModules ∧
      topologicalKrullDim B.subscheme ≤ 0 ∧
      FiniteDimensional k (nodalSeriesCoordinateSpace k B) ∧
      (∀ (P : Setoid (irreducibleComponents X))
        (W : Quotient P → Submodule k V),
        (∀ (a : Quotient P) (s : V), s ∈ W a ↔
          ∀ C : irreducibleComponents X, Quotient.mk P C ≠ a →
            nodalSeriesGenericValue L s.1 C = 0) →
        iSupIndep W → (⨆ a, W a) = ⊤ →
        (nodalSeriesBoundary P).Finite ∧
        ((nodalSeriesBoundaryIdeal P).support : Set X) = nodalSeriesBoundary P ∧
        (∀ x ∈ nodalSeriesBoundary P, IsClosed ({x} : Set X) ∧
          x ∉ (X ↘ Spec (.of k)).smoothLocus) ∧
        IsReduced (nodalSeriesBoundaryIdeal P).subscheme ∧
        FiniteDimensional k (nodalSeriesCoordinateSpace k (nodalSeriesBoundaryIdeal P)) ∧
        B ≤ nodalSeriesBoundaryIdeal P ∧
        (nodalSeriesBoundary P).ncard ≤ nodalSeriesLength k B ∧
        (∀ a : Quotient P,
          ∃ (A C : X.IdealSheafData),
            A = nodalSeriesUnionIdeal {D | Quotient.mk P D = a} ∧
            C = nodalSeriesUnionIdeal {D | Quotient.mk P D ≠ a} ∧
            ((A + C).support : Set X) = nodalSeriesBlockBoundary P a ∧
            (nodalSeriesBlockBoundary P a).Finite ∧
            nodalSeriesLength k (A + C) = (nodalSeriesBlockBoundary P a).ncard ∧
            ∃ (n : ℕ) (e : (∐ fun _ : Fin n ↦ Spec (.of k)) ≅
              pullback A.subschemeι C.subschemeι),
              n = (nodalSeriesBlockBoundary P a).ncard ∧
              ∀ i : Fin n, Sigma.ι (fun _ : Fin n ↦ Spec (.of k)) i ≫ e.hom ≫
                pullback.fst A.subschemeι C.subschemeι ≫ A.subschemeι ≫
                  X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))) ∧
      (V = ⊤ →
        Function.Bijective
          ((L ◁ B.toModulesι ≫ (ρ_ L).hom).app ⊤) ∧
        ∀ (D : ReducedCurveDualizingPair k X) (T : X.IdealSheafData),
          T.IsInvertible → topologicalKrullDim T.subscheme ≤ 0 →
          Nonempty (L ≅ T.toModules ⊗ D.omega) →
          RingedSpace.IsCoherent X.toRingedSpace (T * B).toModules ∧
          topologicalKrullDim (T * B).subscheme ≤ 0 ∧
          FiniteDimensional k (nodalSeriesCoordinateSpace k (T * B)) ∧
          T * B ≤ T ∧
          nodalSeriesLength k (T * B) = nodalSeriesLength k T + nodalSeriesLength k B ∧
          Set.range (((T * B).toModulesι ▷ D.omega ≫ (λ_ D.omega).hom).app ⊤) =
            Set.range ((T.toModulesι ▷ D.omega ≫ (λ_ D.omega).hom).app ⊤)) := by
  sorry

end AlgebraicGeometry
