/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.RingTheory.BoundedPseudoCoherentResidueModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Recognizing shifted line modules from geometric derived fibres

Source: Stacks Project, More on Algebra, Tags 0BYP and 0BCC; Derived Categories,
Tag 08J5 (blueprint: lem-sfb-pseudocoherent-point-fibre-line).

The equivalent small affine ringed model represents the existing small etale module topos.
At an algebraically closed field its structure module represents the field itself.
Canonicity is expressed by invertibility of both legs of the truncation roof, with the
projection uniquely prescribed by the cycles-to-cohomology quotient in degree `-m`.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w wPoint

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally bounded-below pseudo-coherent complex with every geometric derived fibre
isomorphic to the field in degree `-m` is its line cohomology module shifted by `m`.
The last clause fixes the canonical comparison: for every representative, the inclusion
of its upper truncation and the uniquely specified projection to its single cohomology
complex become invertible. Their quotient is the canonical comparison, transported
through the representative isomorphism and the standard single-complex identifications.
Source: Stacks Project, More on Algebra, Tags 0BYP and 0BCC; Derived Categories, Tag 08J5
(blueprint: lem-sfb-pseudocoherent-point-fibre-line).

Proof:
1. On sufficiently small affine etale charts take bounded-above finite-free models
   (def-pc-ring-pseudo-coherent-complex). Termwise affine association and exact etale
   association compute the restriction (lem-pc-affine-qcoh-derived-equivalence,
   lem-sfb-scheme-etale-module-exact-finiteness-comparison). K-flat restriction and
   bounded-above flat K-flatness identify the geometric derived fibre with tensoring
   this model with the geometric field (lem-sfb-ringed-site-restriction-kflat,
   lem-pc-bounded-above-flat-kflat-site,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
2. Exact extension from the residue field to its algebraic closure commutes with
   cohomology (lem-weil-pbc-exact-functor-complex-cohomology). A basis extends to a
   basis, so the residue cohomology ranks are zero except for rank one in degree -m.
3. Apply lem-sfb-bounded-pseudocoherent-residue-model with a=-m. The chart's lower
   bound and these residue ranks give, near each prime, the one-term model R_f[m].
4. Realize those models on the etale site. Localization is computed by termwise
   tensor (lem-pc-module-bounded-flat-kflat). Exact restriction commutes with
   cohomology (lem-weil-pbc-site-restriction-exact and
   lem-weil-pbc-exact-functor-complex-cohomology). Thus cohomology vanishes away from
   -m and the cohomology in degree -m is locally the structure module. The resulting
   covers cover X; separatedness of sheaves makes the vanishing global.
5. The two canonical truncation arrows of lem-weil-pbc-truncation-triangle induce
   isomorphisms on all cohomology, hence are invertible by
   lem-weil-pbc-unbounded-derived-iso-cohomology. The projection is uniquely specified
   by its degree -m component. Its composite with the inverse inclusion gives the
   canonical isomorphism, independently of local trivializations. -/
theorem pseudoCoherent_pointFibre_line
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    [∀ (Ω : Type u) [Field Ω] (b : Spec (.of Ω) ⟶ S),
      HasDerivedCategory.{wPoint} (schemeSpace (Over.mk b)).SmallModules]
    (E : X.DerivedModules) (m : ℤ) (hpc : X.IsPseudoCoherent E)
    (hbelow : ∀ V : X.SmallEtaleModel,
      ∃ R : Sieve V, R ∈ X.smallEtaleModelTopology V ∧
        ∀ (U : X.SmallEtaleModel) (f : U ⟶ V), R f →
          ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero
            ((SheafOfModules.overFunctor X.smallStructureRings U).obj
              ((DerivedCategory.homologyFunctor X.SmallModules n).obj E)))
    (hfibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S) (x : schemeSpace (Over.mk b) ⟶ X),
      Nonempty ((derivedTensorPullback x).obj E ≅
        (schemeSpace (Over.mk b)).derivedStructure⟦m⟧)) :
    X.IsLineModule (X.smallModuleEquivalence.inverse.obj
      ((DerivedCategory.homologyFunctor X.SmallModules (-m)).obj E)) ∧
    Nonempty (E ≅ ((DerivedCategory.singleFunctor X.SmallModules 0).obj
      ((DerivedCategory.homologyFunctor X.SmallModules (-m)).obj E))⟦m⟧) ∧
    ∀ P : CochainComplex X.SmallModules ℤ, Nonempty (DerivedCategory.Q.obj P ≅ E) →
      IsIso (DerivedCategory.Q.map (P.ιTruncLE (-m))) ∧
      ∃! j : P.truncLE (-m) ⟶
          (CochainComplex.singleFunctor X.SmallModules (-m)).obj (P.homology (-m)),
        j.f (-m) ≫
            (HomologicalComplex.singleObjXSelf (.up ℤ) (-m) (P.homology (-m))).hom =
          (P.truncLEXIsoCycles (-m)).hom ≫ P.homologyπ (-m) ∧
        IsIso (DerivedCategory.Q.map j) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
