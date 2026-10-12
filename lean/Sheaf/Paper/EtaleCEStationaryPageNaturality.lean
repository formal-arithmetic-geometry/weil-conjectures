/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.EtaleCETotalSections
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.CategoryTheory.DegreewiseFilteredStableQuotient
import Sheaf.CategoryTheory.BoundedBelowSecondFiltration

/-! # Naturality of stationary CE page quotients

Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Identifications with the actual cycle/boundary cokernels, without making any choice.
Source: Stacks Project, Tag 012K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
abbrev EtaleCEQuotientRealization {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :=
  ∀ (q p r : ℤ) (hr : 1 ≤ r),
    ((D.sequence.page r hr).X (q, p)) ≅
      filteredComplexPageObject D.sectionsTotal D.L r (q, p)

/-- A page map is induced by the sections-total map on graded cycle representatives.
This is an equation of maps from arbitrary test objects, rather than an existence
assertion about a spectral-sequence map. Source: Stacks Project, Tags 012K and 015K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
def EtaleCEPageMapOnRepresentatives {X Y : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    {L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (e : EtaleCEQuotientRealization D) (e' : EtaleCEQuotientRealization D')
    (b : D.sectionsTotal ⟶ D'.sectionsTotal) (N : D.sequence ⟶ D'.sequence) : Prop :=
  ∀ (A : AddCommGrpCat.{uNatural + 1}) (q p r : ℤ) (hr : 1 ≤ r)
    (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (z : A ⟶ (D.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1}))
    (z' : A ⟶ (D'.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1})),
    x ≫ (D.L.step q).arrow.f (q + p) ≫ b.f (q + p) =
      y ≫ (D'.L.step q).arrow.f (q + p) →
    z ≫ (D.L.complexCycles q (q + p) r).arrow =
      x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z' ≫ (D'.L.complexCycles q (q + p) r).arrow =
      y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z ≫ filteredComplexPageπ D.sectionsTotal D.L r (q, p) ≫
        (e q p r hr).inv ≫ (N.hom r hr).f (q, p) =
      z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L r (q, p) ≫ (e' q p r hr).inv

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent simultaneous page and presentation families.
/-- Choose the stationary comparisons naturally for all sections-total filtered maps.
No augmentation, pullback, ordinary first-page identification or CE lift is asserted.
Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality).

Proof. If b bounds the complex degree of D.I below, its extended flipped total has
zero summands in negative resolution degree and in complex degrees below b.
The filtration formula therefore makes D.L top at b and bottom at n+1 in degree n.
For fixed q,n choose R at least 1 so that q+R is past the upper tail in degree n+1,
and q-R+1 is below the lower tail in degree n-1. These inequalities persist for
larger r. The definitions of cycles and boundaries then reduce to actual cycles
in the q-th step and boundaries of the total intersected with that step, projected
onto its graded complex. The abelian subquotient theorem identifies their cokernel
canonically with the q-th graded piece of the homology-image filtration.
Transport this comparison by D.c n, using D.H_formula to identify the transported
steps with D.H n. Compose with e to define eInf; its bound uses only D,q,n.
For a filtered chain map, homology of each step maps its image into the target
image. Transport these restricted image maps by the two c-isomorphisms to obtain
t and its inclusion equation. These restrictions commute with successive step
inclusions by cancellation of the target step's monomorphism. The representative
hypothesis states exactly the naturality of the source page cokernel map. Apply
it to actual cycles in each filtration step; the canonical representative-to-image
quotient projections are epimorphic. Cancellation proves the displayed square
with cokernel.map. Changing its commutativity proof changes no map by proof
irrelevance. Zero totals and empty diagonals obey the same universal properties. -/
theorem exists_etaleCE_stationary_page_comparisons
    (D : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleTermwiseHypercohomology X K)
    (e : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleCEQuotientRealization (D X K)) :
    ∃ (R : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      ∀ {X Y : Scheme.{uNatural}}
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (b : (D X K).sectionsTotal ⟶ (D Y L).sectionsTotal)
        (N : (D X K).sequence ⟶ (D Y L).sequence),
        (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
            ((D Y L).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
          s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) →
        EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L) b N →
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  b n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            (N.hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q) := by sorry

end AlgebraicGeometry.Etale
