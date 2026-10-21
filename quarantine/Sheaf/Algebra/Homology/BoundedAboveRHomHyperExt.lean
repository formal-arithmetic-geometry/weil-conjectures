/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ExactCoupleMorphism
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCouple

/-! # Finite-diagonal internal hyper-Ext

Source: Stacks Project, derived.tex, Tag 015W (filtered-derived method),
sites-cohomology.tex, Tags 0A94 and 0A95, and homology.tex, Tags 011R, 011T and 012U.
This is the Postnikov/internal-Hom variant, rather than a left-exact functor on the heart.
It supplies the truncation passage in ILO XVII 10.1.1, proof p. 325.
(blueprint: lem-per-bounded-above-rhom-hyperext).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
    CommRingCat.{max uC vC u}
    RingCat.{max uC vC u})).obj R))]

/-- The functor T^n(M) = H^n RHom(K,M), with its actual derived morphism maps.
Source: Stacks Tags 0A94, 0A95; the internal-Hom version of Tag 015W.
(blueprint: lem-per-bounded-above-rhom-hyperext). -/
noncomputable abbrev ringedSiteRHomCohomology (K : DerivedCategory (ringedSiteModules.{max uC vC u}
  ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) (n : ℤ) :
    DerivedCategory (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC
      vC u}
      RingCat.{max uC vC u})).obj R)) ⥤ (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{uC, vC, u, w} J R)).obj (op K) ⋙
    DerivedCategory.homologyFunctor _ n

/-- Sheaf Ext^p(K,F) is H^p RHom(K,F[0]), for every integer p.
Source: the internal-Hom/Postnikov variant of Stacks Tag 015W, using Tags 0A94 and 0A95.
(blueprint: lem-per-bounded-above-rhom-hyperext). -/
noncomputable abbrev ringedSiteHyperExt (K : DerivedCategory (ringedSiteModules.{max uC vC u}
  ((sheafCompose J
  (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) (p : ℤ) :
    (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) ⥤
      (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
        RingCat.{max uC vC u})).obj R)) :=
  DerivedCategory.singleFunctor _ 0 ⋙ ringedSiteRHomCohomology.{uC, vC, u, w} J R K p

/-- A bounded-above source and a bounded-below target give the finite-diagonal
internal hyper-Ext spectral sequence, naturally and additively in the target.
Here E is a functor on the full subcategory D^{>=c}; e2 is the natural E2 identification;
a is the actual cohomology map as a filtered morphism. The isomorphisms conv identify
any sufficiently late page with the graded piece, and their squares identify its maps.

Source: Stacks Tag 015W (method), Tags 0A94, 0A95, 03EI, 08J5, 011R, 011T and 012U;
ILO XVII 10.1.1, proof p. 325 (the Ext-to-representable-sums passage).
(blueprint: lem-per-bounded-above-rhom-hyperext).

Proof:
1. Resolve the second argument by a K-injective complex. The local calculation
   lem-pur-rhom-into-kinjective-local, applied to the source shifted by -n, identifies
   T^n(M) with the sheafification of U |-> Hom(K|U,M|U[n]). The signed Hom-complex
   shift formula and exact module sheafification (Tag 03EI) give this identification
   naturally and additively in M and under restriction.
2. Exact restriction (lem-pur-site-restriction-module-adjunction-exact) preserves
   cohomology. Standard t-structure orthogonality gives T^n(M)=0 for n<b-r when
   M>=b. In particular Ext^p(K,F)=0 for p<-r and T^n(L)=0 for n<c-r.
3. Restrict a distinguished triangle to each localized site, apply the representable
   Hom exact sequence (lem-weil-pbc-hom-into-triangle-exact), and sheafify exactly.
   The boundary is postcomposition with the shifted third arrow; the last square of
   a triangle morphism proves its naturality. This makes the T^n a cohomological functor.
4. Apply T to the successive functorial Postnikov triangles
   tau<=q-1 L -> tau<=q L -> H^q(L)[-q] ->.
   By lem-weil-pbc-truncation-triangle their long exact sequences give the exact couple
   D^{p,q}=T^{p+q}(tau<=q L), E^{p,q}=T^{p+q}(H^q(L)[-q]), with alpha of degree
   (-1,1), f of degree (2,-1), and g of degree (0,0).
   Lem-sp-derived-couple-exact constructs its pages with d_s of degree (s,1-s).
5. Lem-pur-derived-internal-hom-shift-right identifies E2 with Ext^p(K,H^q L).
   Step 2 gives p>=-r and q>=c support, and D=0 for q<c. Subquotients preserve support.
6. Reindex by P=p+r. Thm-sp-half-plane-convergence applies with lower row c.
   The stable pages have s>max(q-c+1,p+r); total degree n has c<=q<=n+r.
   Its initial abutment is T^n(tau<=n+r L).
7. The tail tau>=n+r+1 L has T^{n-1}=T^n=0 by Step 2. The truncation triangle
   (lem-sf-derived-truncation-triangle) and Step 3 identify this initial abutment
   isomorphically with T^n(L), naturally in L, also when n+r<c.
8. Transport the image filtration to T^n(L). Its p-step is the image of
   T^n(tau<=n-p L) -> T^n(L). The tail argument gives F^{-r}=top, and q<c gives
   F^{n-c+1}=bottom. The half-plane theorem supplies the graded identifications.
   These finite bounds imply exhaustiveness, separatedness and completeness.
9. Functorial truncation triangles and the natural boundaries give couple morphisms.
   Lem-sp-couple-morphism gives compatible maps on pages, abutments and graded pieces.
   The abutment map is T^n(u) by Step 7. Truncation and local postcomposition are
   additive. Induction through kernels, images and quotients gives additivity on
   every page; uniqueness through the monic filtration inclusions gives additivity
   of step maps, and then of graded maps. The same uniqueness gives identities and
   composition. This proves all stated functorialities without dimension or Tor bounds. -/
theorem exists_boundedAbove_rhom_hyperExt
    (K : DerivedCategory (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max
      uC vC u}
      RingCat.{max uC vC u})).obj R))) (r c : ℤ) (_hK : K.IsLE r) :
    ∃ E : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c)) ⥤
      E₂CohomologicalSpectralSequence (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)),
    ∃ e2 : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max
      uC vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (p q :
      ℤ),
      ((E.obj L).page 2).X (p, q) ≅
        (ringedSiteHyperExt.{uC, vC, u, w} J R K p).obj ((DerivedCategory.homologyFunctor _ q).obj
          L.obj),
    ∃ F : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
      vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
      ℤ),
      DecreasingFiltration ((ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj),
    ∃ a : ∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
      (ringedSiteModules.{max uC vC u} ((sheafCompose J
      (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f : L ⟶ M),
      FilteredObject.Hom
        ⟨(ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj, F L n⟩
        ⟨(ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj M.obj, F M n⟩,
    ∃ conv : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max
      uC vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (s : ℤ)
      (hs : 2 ≤ s) (p q : ℤ),
      max (q - c + 1) (p + r) < s →
        (((E.obj L).page s hs).X (p, q) ≅ (F L (p + q)).gr p),
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE
          c))) (s : ℤ) (hs : 2 ≤ s)
          (hs' : 2 ≤ s + 1) (p q : ℤ)
          (hst : max (q - c + 1) (p + r) < s)
          (hst' : max (q - c + 1) (p + r) < s + 1),
        ((E.obj L).page s hs).iCycles (p, q) ≫ (conv L s hs p q hst).hom =
          ((E.obj L).page s hs).homologyπ (p, q) ≫
            ((E.obj L).iso s (s + 1) (p, q) rfl hs).hom ≫
              (conv L (s + 1) hs' p q hst').hom) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M) (p q : ℤ),
        ((E.map f).hom 2).f (p, q) ≫ (e2 M p q).hom =
          (e2 L p q).hom ≫ (ringedSiteHyperExt.{uC, vC, u, w} J R K p).map
            ((DerivedCategory.homologyFunctor _ q).map f.hom)) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ),
        ((E.map (f + g)).hom s hs).f (p, q) =
          ((E.map f).hom s hs).f (p, q) + ((E.map g).hom s hs).f (p, q)) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (s :
        ℤ) (hs : 2 ≤ s) (p q : ℤ),
        p < -r ∨ q < c → IsZero (((E.obj L).page s hs).X (p, q))) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
        ℤ),
        (F L n).IsFinite ∧ (F L n).IsExhaustive ∧ (F L n).IsSeparated ∧
          (F L n).F (-r) = ⊤ ∧ IsZero ((F L n).F (n - c + 1) : ringedSiteModules.{max uC vC u}
            ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M),
        (a n f).hom = (ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).map f.hom) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ) (hst : max (q - c + 1) (p + r) < s),
        ((E.map f).hom s hs).f (p, q) ≫ (conv M s hs p q hst).hom =
          (conv L s hs p q hst).hom ≫ FilteredObject.gradedMapSteps (a (p + q) f) p) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M) (p : ℤ),
        FilteredObject.restrictionSteps (a n (f + g)) p =
          FilteredObject.restrictionSteps (a n f) p +
            FilteredObject.restrictionSteps (a n g) p) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M) (p : ℤ),
        FilteredObject.gradedMapSteps (a n (f + g)) p =
          FilteredObject.gradedMapSteps (a n f) p +
            FilteredObject.gradedMapSteps (a n g) p) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n p
        q : ℤ),
        p + q = n → ¬ IsZero (((E.obj L).page 2).X (p, q)) → c ≤ q ∧ q ≤ n + r) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
        ℤ), n < c - r →
        IsZero ((ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj)) := by
  sorry

end CategoryTheory
