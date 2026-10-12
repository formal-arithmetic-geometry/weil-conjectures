/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import Sheaf.CategoryTheory.CartanEilenbergFunctorial
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexZBDescription
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.FilteredComplexSpectralSequence
import Sheaf.CategoryTheory.HypercohomologyFirstPage

/-! # Coherent filtered Cartan--Eilenberg total maps

Source: Stacks Project, derived.tex, Tags 015J and 015K.
(blueprint: lem-weil-pbc-ce-total-filtered-maps).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the simultaneous presentation, total-map and stabilization witnesses.
/-- Choose the filtered CE spectral sequences and their maps on CE totals. The abutment
here uses the CE total source, rather than any supplied lift between the chosen resolutions.
Source: Stacks Project, derived.tex, Tag 015J (lemma-two-ss-complex-functor) and
Tag 015K (remark-functorial-ss).
(blueprint: lem-weil-pbc-ce-total-filtered-maps).

Proof: Shift each bounded-below complex to start in degree zero, choose its CE resolution
by exists_cartanEilenberg_resolution, and shift back. Construct the second filtration
of the extended, flipped CE total. Its steps are the entire object below a fixed lower
complex-degree bound b and are zero in cochain degree i above filtration index i.
To use the uniformly finite filtered-complex construction, crop the filtration above
an integer c: retain its steps through c and replace all later steps by zero. This is
a finite filtration of the whole complex. For a fixed total degree n choose c > n+1;
the cropped and original filtrations then agree in degrees n-1,n,n+1 for every index.
The canonical cycle and boundary formulas therefore agree in bidegrees (q,n-q) on
every page. Increasing c gives identity filtered maps between cropped filtrations;
the representative comparisons identify these maps with identities on the unchanged
cycle/boundary quotients. Thus the page objects and homology structure maps glue.
For a page differential use a common c for its source and target total degrees.
For a filtered map use common lower and upper crop bounds in source and target;
canonical representative naturality then glues its page maps as well. This constructs
the canonical spectral sequence for the degreewise finite filtration, without claiming
that the original filtration is uniformly finite. Use the signed row identifications
and the natural
Ext/global-sections comparison to obtain the presentations D. For each (f,v), apply
cartanEilenberg_lift to exact inverse image and the augmented CE resolutions. Totalize
this bicomplex map, and compose with the target presentation's comparison to its chosen
K-injective resolution to obtain g. The augmentation square is the stated homotopy.
Apply the global-sections unit to g to obtain s. Additivity commutes with the finite
diagonal sums: cartanEilenberg_mapped_total_iso supplies e. Its summand formula and the
presentation's w_formula later identify w with e.hom followed by Γ(comparison).
The total map preserves the complex-degree filtration, hence induces M. On each row
resolve the inverse-image row into the target injective row; naturality of the fixed
constant-integer/global-sections comparison computes H(v) after cohomologyMap. The sign
correction is the same in source and target, giving the first-page equation.
Restrict the total map to the images of cohomology of filtration steps and transport
along c_X and the target resolution isomorphism. This gives t and ht. Choose for each
presentation and bidegree a bound beyond the finite filtration tails in degrees n-1,
n and n+1. Cycles and boundaries are then stationary; their canonical quotient-to-image
comparisons give eInf. These representative comparisons commute with the filtered
map, so the map on stationary pages is the induced map on the two successive image
quotients, namely cokernel.map. Its compatibility proof is immaterial by proof
irrelevance. The bound depends only on a presentation and a bidegree, not on (f,v).
Zero complexes, empty schemes and empty diagonal sums are included in these constructions.
No choice of an arbitrary resolution lift is used in this statement. -/
theorem exists_etaleHypercohomology_ce_total_maps :
    ∃ (D : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (R : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        let A := (((CartanEilenbergPresentation.mappedFunctor
          (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
            (D X K).I).flip).total (ComplexShape.up ℤ)
        let B := (((CartanEilenbergPresentation.mappedFunctor
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
            (D X K).I).flip).total (ComplexShape.up ℤ)
        ∃ (g : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A ⟶ (D Y L).ρ.complex)
          (s : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A ⟶
            ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D Y L).ρ.complex)
          (e : B ≅ ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj A),
          Nonempty (Homotopy
            (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (D X K).aug ≫ g) (v ≫ (D Y L).ρ.map)) ∧
          (∀ i : ℤ, s.f i =
            globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X i) ≫
              (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (g.f i)) ∧
          (∀ (m : ℕ) (k n : ℤ) (h : (m : ℤ) + k = n),
            (((CartanEilenbergPresentation.mappedFunctor
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
                (D X K).I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h ≫ e.hom.f n =
              (HomologicalComplex.extendXIso
                (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X k))
                ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
                ((HomologicalComplex.extendXIso
                  (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
                    |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X k))
                  ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    (D X K).I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h)) ∧
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
            (((D X K).c n).inv ≫
              HomologicalComplex.homologyMap (e.hom ≫ s) n ≫
              (@resolutionEtaleCohomologyIso.{uNatural} Y L.obj (D Y L).ρ.complex
                (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) := by
  sorry

end AlgebraicGeometry.Etale
