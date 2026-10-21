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
import Sheaf.Algebra.Homology.KunnethSpectralSequenceReindex
import Sheaf.Algebra.Homology.LocalizedFilteredConvergence
import Sheaf.Algebra.Homology.KunnethFilteredFirstPage
import Sheaf.Algebra.Homology.FilteredPageLocalization

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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

private def shiftFiltration {A : ModuleCat.{u} R} (F : DecreasingFiltration A) (n : ℤ) :
    DecreasingFiltration A where
  F p := F.F (p - n)
  F_succ_le p := by
    simpa only [show p + 1 - n = (p - n) + 1 by omega] using F.F_succ_le (p - n)

private noncomputable def shiftGrIso {A : ModuleCat.{u} R}
    (F : DecreasingFiltration A) (n p : ℤ) :
    (shiftFiltration R F n).gr p ≅ F.gr (p - n) := by
  let h : F.F (p + 1 - n) = F.F ((p - n) + 1) := by congr 1; omega
  exact cokernel.mapIso _ _ (Subobject.isoOfEq _ _ h)
    (Iso.refl _) (by
      apply (cancel_mono (F.F (p - n)).arrow).1
      simp only [shiftFiltration, Iso.refl_hom, Subobject.isoOfEq_hom,
        Category.assoc, Category.comp_id, Subobject.ofLE_arrow])

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
@[reassoc]
private theorem shiftGrIso_projection {A : ModuleCat.{u} R}
    (F : DecreasingFiltration A) (n p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ ((shiftFiltration R F n).F_succ_le p)) ≫
        (shiftGrIso R F n p).hom =
      cokernel.π (Subobject.ofLE _ _ (F.F_succ_le (p - n))) := by
  simp only [shiftGrIso, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc, Iso.refl_hom,
    Category.id_comp]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem stationary_transport
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 1)
    (i j : ℤ × ℤ) (hij : i = j) {A B : ModuleCat.{u} R} (u : A ≅ B)
    (t t' : ℤ) (htt : t + 1 = t') (ht : 1 ≤ t)
    (e : B ≅ (E.page t ht).X i) (e' : B ≅ (E.page t' (by omega)).X i)
    (h : (E.page t ht).iCycles i ≫ e.inv =
      (E.page t ht).homologyπ i ≫ (E.iso t t' i htt ht).hom ≫ e'.inv) :
    (E.page t ht).iCycles j ≫ (u ≪≫ e ≪≫ (E.page t ht).XIsoOfEq hij).inv =
      (E.page t ht).homologyπ j ≫ (E.iso t t' j htt ht).hom ≫
        (u ≪≫ e' ≪≫ (E.page t' (by omega)).XIsoOfEq hij).inv := by
  subst j
  simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.trans_inv, Iso.refl_inv,
    Category.id_comp, Category.assoc] using congrArg (fun z ↦ z ≫ u.inv) h

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem stationary_at (d : FilteredPageLocalizationData R)
    (c : LocalizedFilteredConvergenceData R d)
    (X : finiteFilteredModuleDerivedCategory R) (n a t t' : ℤ)
    (h : t + 1 = t') (ht : 1 ≤ t) (ht' : 1 ≤ t')
    (hs : c.bound X n a ≤ t) (hs' : c.bound X n a ≤ t') :
    ((d.Sbar.obj X).page t ht).iCycles (a, n - a) ≫
        (c.comparison X n a t ht hs).inv =
      ((d.Sbar.obj X).page t ht).homologyπ (a, n - a) ≫
        ((d.Sbar.obj X).iso t t' (a, n - a) h ht).hom ≫
          (c.comparison X n a t' ht' hs').inv := by
  subst t'
  exact c.successor X n a t ht hs

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem graded_inverse_naturality
    {K L A B : FilteredObject (ModuleCat.{u} R)} (e : K ≅ A) (e' : L ≅ B)
    (f : K ⟶ L) (g : A ⟶ B) (h : f ≫ e'.hom = e.hom ≫ g) (a : ℤ) :
    FilteredObject.gradedMapSteps g a ≫
        ((kunnethGradedFunctor (ModuleCat R) a).mapIso e'.symm).hom =
      ((kunnethGradedFunctor (ModuleCat R) a).mapIso e.symm).hom ≫
        FilteredObject.gradedMapSteps f a := by
  have hi : g ≫ e'.inv = e.inv ≫ f := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (kunnethGradedFunctor (ModuleCat R) a).map g ≫
      (kunnethGradedFunctor (ModuleCat R) a).map e'.inv =
    (kunnethGradedFunctor (ModuleCat R) a).map e.inv ≫
      (kunnethGradedFunctor (ModuleCat R) a).map f
  rw [← Functor.map_comp, ← Functor.map_comp, hi]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem page_index_naturality {r : ℤ}
    {E E' : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up' (r, 1 - r))}
    (f : E ⟶ E') (i j : ℤ × ℤ) (h : i = j) :
    f.f i ≫ (E'.XIsoOfEq h).hom = (E.XIsoOfEq h).hom ≫ f.f j := by
  subst j
  simp

set_option linter.unusedVariables false in
-- Preserve the original names of existential binders used only implicitly.
set_option maxHeartbeats 1000000 in
-- Associativity and naturality involve dependent page and filtered-graded indices.
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
  classical
  obtain ⟨d⟩ := filteredPageLocalization R
  obtain ⟨c⟩ := localizedFilteredConvergence R d
  obtain ⟨U, F₀, eH, e₁, h₁, hH⟩ := exists_kunnethFilteredFirstPage R d
  let S := U ⋙ (Functor.whiskeringRight _ _ _).obj
    (d.Sbar ⋙ kunnethReindexFunctor (C := ModuleCat.{u} R))
  let F := fun C D n ↦ shiftFiltration R (F₀ C D n) n
  let N := fun C D n p ↦ c.bound ((U.obj C).obj D) n (p - n) + 1
  have hN (C D : Bounded (ModuleCat.{u} R)) (n p : ℤ) : 2 ≤ N C D n p := by
    have := c.bound_ge ((U.obj C).obj D) n (p - n)
    dsimp [N]
    omega
  have hind (n p : ℤ) : (p - n, n - (p - n)) = kunnethIndex (p, n - p) := by
    ext <;> dsimp [kunnethIndex] <;> omega
  let eInf := fun C D n p r (hr : 2 ≤ r) (hs : N C D n p ≤ r) ↦
    shiftGrIso R (F₀ C D n) n p ≪≫
      (kunnethGradedFunctor (ModuleCat R) (p - n)).mapIso (eH C D n).symm ≪≫
      c.comparison ((U.obj C).obj D) n (p - n) (r - 1) (by omega) (by
        dsimp [N] at hs; omega) ≪≫
      ((d.Sbar.obj ((U.obj C).obj D)).page (r - 1) (by omega)).XIsoOfEq (hind n p)
  refine ⟨S, F, N, hN, e₁, eInf, ?_, ?_, ?_, ?_, ?_⟩
  · intro C D n
    obtain ⟨a, b, ha, hb⟩ := kunneth_filtered_finite_iso (eH C D n)
      (c.finite ((U.obj C).obj D) n)
    refine ⟨a + n, b + n, ?_, ?_⟩
    · simpa [F, shiftFiltration] using ha
    · simpa [F, shiftFiltration] using hb
  · intro C C' D D' f g p q
    change ((((d.Sbar.map ((U.map f).app D)).hom 1).f (-q, p + 2 * q)) ≫
      (((d.Sbar.map ((U.obj C').map g)).hom 1).f (-q, p + 2 * q))) ≫
      (e₁ C' D' p q).hom = (e₁ C D p q).hom ≫ kunnethTorPageMap R p q f g
    simpa only [Functor.map_comp, SpectralSequence.comp_hom,
      HomologicalComplex.comp_f, kunnethTorPageMap, kunnethIntegerTor]
      using h₁ C C' D D' f g p q
  · intro C D n p r hr hs
    apply kunnethReindex_differentials
    have hd := c.differential ((U.obj C).obj D) n (p - n) (r - 1) (by omega)
      (by dsimp [N] at hs; omega)
    rw [hind n p] at hd
    exact hd
  · intro C D n p r hr hs
    apply kunnethReindex_successor
    apply stationary_transport R _ _ _ (hind n p)
      (shiftGrIso R (F₀ C D n) n p ≪≫
        (kunnethGradedFunctor (ModuleCat R) (p - n)).mapIso (eH C D n).symm)
      (r - 1) ((r + 1) - 1) (by omega) (by omega)
    exact stationary_at R d c ((U.obj C).obj D) n (p - n) (r - 1) ((r + 1) - 1)
      (by omega) (by omega) (by omega) (by dsimp [N] at hs; omega)
      (by dsimp [N] at hs; omega)
  · intro C C' D D' f g
    let α := (U.map f).app D ≫ (U.obj C').map g
    choose h hh hnat using fun n ↦ hH C C' D D' f g n
    let a := fun n p ↦ FilteredObject.restrictionSteps (h n) (p - n)
    let b := fun n p ↦ (shiftGrIso R (F₀ C D n) n p).hom ≫
      FilteredObject.gradedMapSteps (h n) (p - n) ≫
        (shiftGrIso R (F₀ C' D' n) n p).inv
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro n p
      simpa only [a, F, shiftFiltration, hh] using kunneth_step_arrow (h n) (p - n)
    · intro n p
      dsimp only [b]
      dsimp only [F, a]
      rw [← Category.assoc, shiftGrIso_projection]
      rw [reassoc_of% (kunneth_graded_projection (h n) (p - n))]
      have hp := shiftGrIso_projection R (F₀ C' D' n) n p
      have hp' := (Iso.comp_inv_eq (shiftGrIso R (F₀ C' D' n) n p)).2 hp.symm
      exact congrArg (FilteredObject.restrictionSteps (h n) (p - n) ≫ ·) hp'
    · intro n p r hr hs ht
      have hn := c.naturality α n (p - n) (r - 1) (by omega)
        (by dsimp [N] at hs; omega) (by dsimp [N] at ht; omega)
      have he := graded_inverse_naturality R (eH C D n) (eH C' D' n)
        ((d.Hbar n).map α) (h n) (hnat n) (p - n)
      have hi := page_index_naturality R ((d.Sbar.map α).hom (r - 1) (by omega))
        (p - n, n - (p - n)) (kunnethIndex (p, n - p)) (hind n p)
      dsimp only [b, eInf, Iso.trans_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% he, reassoc_of% hn, hi]
      simp only [α, Functor.map_comp, SpectralSequence.comp_hom,
        HomologicalComplex.comp_f]
      rfl

end DerivedCategory
