/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.CategoryTheory.BoundedFilteredComplexPageCore
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Algebra.Homology.DerivedCanonicalFiltration
import Sheaf.Algebra.Homology.FilteredPageLocalization
import Sheaf.Algebra.Homology.FilteredTensorGradedComparison
import Sheaf.Algebra.Homology.FilteredTensorLocalization
import Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement

/-!
# The functorial bounded derived-tensor Tor spectral sequence

Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H7Y
(blueprint: lem-kun-bounded-tensor-tor-spectral-sequence).

The tensor is the upstream K-flat derived monoidal tensor of modules, whose fixed-second-
factor functor is the ordinary derived tensor of Tag 06Y6. Coproducts of modules are direct
sums. The stationary value is expressed by coherent identifications with every sufficiently
late page; this avoids choosing a single page simultaneously for all objects and morphisms.
The filtration has arbitrary integer endpoints, and the tensor need not have bounded
cohomology. No global dimension or finite generation hypothesis occurs.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace DerivedCategory

variable (R : Type u) [CommRing R]

/-- Tor in an integer homological degree, extended by zero in negative degrees.
Source: Stacks Project, Tag 0H7Z, with Tor as in Tags 00LY/00LZ
(blueprint: lem-kun-bounded-tensor-tor-spectral-sequence). -/
noncomputable def kunnethIntegerTor (k : ℤ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  if k < 0 then
    (Functor.const (ModuleCat.{u} R)).obj
      ((Functor.const (ModuleCat.{u} R)).obj (0 : ModuleCat.{u} R))
  else Tor' (ModuleCat.{u} R) k.toNat

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The displayed second-page direct sum of Tor of cohomology.
Source: Stacks Project, Tag 0H7Z
(blueprint: lem-kun-bounded-tensor-tor-spectral-sequence). -/
noncomputable def kunnethTorPage (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) :
    ModuleCat.{u} R :=
  ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
    ((kunnethIntegerTor R (-p)).obj
      ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
        ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)

/-- The direct sum of the Tor maps induced by two derived morphisms.
Source: Stacks Project, Tags 0H7Z and 00LZ
(blueprint: lem-kun-bounded-tensor-tor-spectral-sequence). -/
noncomputable def kunnethTorPageMap (p q : ℤ)
    {C C' D D' : Bounded (ModuleCat.{u} R)} (f : C ⟶ C') (g : D ⟶ D') :
    kunnethTorPage R p q C D ⟶ kunnethTorPage R p q C' D' :=
  Limits.Sigma.map fun ij ↦
    ((kunnethIntegerTor R (-p)).map
      ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
        ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
    ((kunnethIntegerTor R (-p)).obj
      ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
        ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)

/-- Bounded derived objects admit the Tor spectral sequence with finite abutment
filtrations, coherent stationary-page identifications, and naturality in both arguments.
Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H7Y; Homology, Tags 012K and 012W
(blueprint: lem-kun-bounded-tensor-tor-spectral-sequence).

Proof (the seven DAG steps):
1. Choose bounded cochain representatives using the standard t-structure truncations
   (`def-sbc-standard-tstructure-derived-category`). Filter by F^i K = tau_{<=-i} K.
   The graded quotient maps naturally and quasi-isomorphically to H^{-i}(K)[i].
2. Apply `lem-kun-finite-filtered-kflat-replacement` to these finite filtrations.
   The filtered K-flat replacements and their steps and graded pieces have flat terms;
   their localization equivalence also handles morphisms and equality of morphisms.
3. Form the convolution-filtered total tensor. By
   `lem-kun-filtered-tensor-graded-comparison` its graded pieces are the finite sums of
   the tensors of graded pieces. Apply `lem-sp-bounded-filtered-page-core`: the
   quotient-to-quotient comparison sends a representative to the same representative.
   This gives a page-one spectral sequence and its finite image filtration on homology.
4. A nonpositive free resolution computes the tensor with a degree-zero module by
   `lem-pc-module-bounded-flat-kflat` and `lem-pc-derived-tensor-second-factor-functor`.
   Its homology is Tor; maps agree with `lem-weil-pbc-tor-map-via-resolution-lift`.
   The signed shift/tensor comparison gives old E_1^{a,b} equal to the sum of
   Tor_{-2a-b}(H^{-i}(C),H^{-j}(D)) for i+j=a, with negative Tor zero.
5. Reindex by E_s^{p,q} = old E_{s-1}^{-q,p+2q}. The inverse indices are
   (p,q)=(b+2a,-a), preserving total degree and giving differential (s,1-s).
   This produces precisely the displayed page two and its Tor-map naturality.
6. Reindex the old cohomology filtration by F^p H^n = G^{p-n} H^n.
   Its graded pieces identify with E_infinity^{p,n-p}. Finite old filtration bounds
   make incoming and outgoing differentials zero on all sufficiently late pages.
   Successor-page homology supplies the coherent stationary identifications below.
7. Canonical truncations preserve chain maps and quasi-isomorphisms on graded pieces.
   Filtered K-flat replacement, convolution tensor, and the page-core construction
   descend through filtered quasi-isomorphisms and filtered homotopies. Represent
   derived maps by roofs (`lem-pc-right-fraction-representation`) and equal roofs by
   common refinements (`lem-pc-right-fraction-common-refinement`); truncate each finite
   diagram to common term bounds. The resulting construction respects composition.
   Its page-two maps are the direct sums of Tor maps, and its underlying total map is
   f tensor-derived g. The image filtration and quotient identifications are natural.
   The quotient-map equation below specifies the induced map on each graded piece;
   the last equation makes the graded stationary identifications natural. -/
theorem bounded_tensor_tor_spectral_sequence :
    ∃ (S : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
        E₂CohomologicalSpectralSequence (ModuleCat.{u} R))
      (F : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        DecreasingFiltration
          ((homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj)))
      (N : Bounded (ModuleCat.{u} R) → Bounded (ModuleCat.{u} R) → ℤ → ℤ → ℤ)
      (hN : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p : ℤ), 2 ≤ N C D n p)
      (e₂ : ∀ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ),
        (((S.obj C).obj D).page 2).X (p, q) ≅ kunnethTorPage R p q C D)
      (eInf : ∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (F C D n).gr p ≅ (((S.obj C).obj D).page r hr).X (p, n - p)),
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        ∃ a b : ℤ, (F C D n).F a = ⊤ ∧ (F C D n).F b = ⊥) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D')
          (p q : ℤ),
        (((S.map f).app D ≫ (S.obj C').map g).hom 2).f (p, q) ≫
            (e₂ C' D' p q).hom =
          (e₂ C D p q).hom ≫ kunnethTorPageMap R p q f g) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ) (hr : 2 ≤ r),
        N C D n p ≤ r →
          (((S.obj C).obj D).page r hr).dFrom (p, n - p) = 0 ∧
          (((S.obj C).obj D).page r hr).dTo (p, n - p) = 0) ∧
      (∀ (C D : Bounded (ModuleCat.{u} R)) (n p r : ℤ)
          (hr : 2 ≤ r) (hs : N C D n p ≤ r),
        (((S.obj C).obj D).page r hr).iCycles (p, n - p) ≫
            (eInf C D n p r hr hs).inv =
          (((S.obj C).obj D).page r hr).homologyπ (p, n - p) ≫
            (((S.obj C).obj D).iso r (r + 1) (p, n - p) rfl hr).hom ≫
              (eInf C D n p (r + 1) (by omega) (by omega)).inv) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D'),
        ∃ (a : ∀ (n p : ℤ), ((F C D n).F p : ModuleCat.{u} R) ⟶
              ((F C' D' n).F p : ModuleCat.{u} R))
          (b : ∀ n p : ℤ, (F C D n).gr p ⟶ (F C' D' n).gr p),
          (∀ n p : ℤ,
            a n p ≫ ((F C' D' n).F p).arrow =
              ((F C D n).F p).arrow ≫
                (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom)) ∧
          (∀ n p : ℤ,
            cokernel.π (Subobject.ofLE _ _ ((F C D n).F_succ_le p)) ≫ b n p =
              a n p ≫ cokernel.π (Subobject.ofLE _ _ ((F C' D' n).F_succ_le p))) ∧
          (∀ (n p r : ℤ) (hr : 2 ≤ r)
              (hs : N C D n p ≤ r) (ht : N C' D' n p ≤ r),
            b n p ≫ (eInf C' D' n p r hr ht).hom =
              (eInf C D n p r hr hs).hom ≫
                (((S.map f).app D ≫ (S.obj C').map g).hom r hr).f (p, n - p))) := by
  sorry

end DerivedCategory
