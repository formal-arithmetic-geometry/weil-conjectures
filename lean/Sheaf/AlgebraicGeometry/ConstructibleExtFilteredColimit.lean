/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Limits.HasLimits

import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleFreeSheafDerivedSections
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting

/-!
# Constructible sheaf Ext and filtered colimits

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Proposition 10.1.1,
first proof paragraph, printed p. 325
(blueprint: lem-per-constructible-ext-filtered-colimit).

The derived category is the ordinary category of etale module sheaves. No lower bound
or finite Tor amplitude is imposed on the source complex. Colimits are module-sheaf colimits.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The functor G ↦ H^n RHom(K,G[0]) with values in module sheaves, including its
canonical action on coefficient maps. The single functor places G in degree zero;
the recorded ordinary etale derived internal Hom and cohomology give sheaf Ext.
Source: ILO, Expose XVII, Proposition 10.1.1, first proof paragraph, p. 325
(blueprint: lem-per-constructible-ext-filtered-colimit). -/
noncomputable def sheafExtCoefficientFunctor (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (K : DerivedCategoryModule A X) (n : ℤ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  _root_.DerivedCategory.singleFunctor _ 0 ⋙
    (derivedHom (ModuleCat.{u + 1} A) X).obj (op K) ⋙
      _root_.DerivedCategory.homologyFunctor _ n

/-- Sheaf Ext from a bounded-above complex with constructible finite-type cohomology
commutes with every small filtered colimit of module sheaves, in every integer degree.
The map is `colimit.post`: its i-th leg is sheaf Ext applied to G_i → colim G.
Each cohomology sheaf may have its own finite locally closed stratification.

Source: ILO, Expose XVII, Proposition 10.1.1, first proof paragraph, p. 325
(blueprint: lem-per-constructible-ext-filtered-colimit).

Proof for stage 3, following the eight steps of the node:
1. Work first on affine Noetherian T. Finite A-modules are finitely presented
   (lem-sc-noetherian-finite-module-finite-presentation). The affine-local convention
   of lem-sfb-discrete-noetherian-constructible-serre agrees with finite stratifications:
   restrict a stratification to each affine open, and conversely take the open T itself.
   Apply lem-per-noetherian-constructible-flat-lifting to p=g=id_F. This gives a finite
   sum E of u_!A_U for affine etale U surjecting onto F. Its kernel is constructible by
   Serre closure. Repeat to obtain arbitrarily many constructible syzygies. Filtered
   colimits are exact by lem-weil-pbc-module-sheaves-grothendieck-abelian.
2. For each finite sum E, the etale sum-extension adjunction and injective preservation
   (lem-weil-pbc-etale-restriction-injectives), free-sheaf derived sections, and Ext via
   injective resolutions identify Ext^q(E,G) with the finite sum of H^q(U,G|_U).
   This identification respects differentials and coefficient maps. Restriction preserves
   colimits by prop-weil-pbc-inverse-image-modules-exact, and the module-coefficient clause
   of lem-weil-pbc-cohomology-filtered-colimit applies since U is affine, hence qcqs.
3. Present F by E_1 → E_0 → F → 0. Hom(F,G) is the kernel of Hom(E_0,G) → Hom(E_1,G),
   so degree-zero continuity follows from exact filtered colimits of groups. Induct on q
   simultaneously for all constructible F. For 0 → F' → E_0 → F → 0 use the natural
   five-term ladder Ext^(q-1)(E_0,-) → Ext^(q-1)(F',-) → Ext^q(F,-) → Ext^q(E_0,-)
   → Ext^q(F',-) from lem-coef-ext-contravariant-six-term.
4. First prove injectivity of c_F^q for every F. A class killed below lifts to the
   second term because c_E_0^q is invertible. Its lower image lifts from the first term;
   lift there using c_E_0^(q-1), subtract, and use injectivity of c_F'^(q-1).
   Now c_F'^q is injective too, and the five lemma gives invertibility of c_F^q.
   Negative Ext for degree-zero sheaves vanishes by a nonnegative injective resolution
   (lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-kinjective-hom-derived).
5. On an etale slice V, internal Hom restricts by
   lem-weil-pbc-ringed-internal-hom-exact-restriction. Its injective Hom-complex evaluated
   at V computes Ext on V: restriction preserves injectives. Exact module sheafification
   identifies sheaf Ext with the associated presheaf Ext. Use affine etale V as a basis;
   V is Noetherian since etale maps are locally finitely presented and finite-type
   algebras over Noetherian rings are Noetherian. Constructibility restricts, so steps
   1--4 apply. Restriction and sheafification preserve colimits; sheafify the objectwise
   comparisons. The cocycle formula identifies their legs with the coefficient maps.
6. If C is in D^{≤a} and N in D^{≥b}, choose a representative P vanishing above a and
   an injective representative I vanishing below b. In Hom(P,I)^t every factor
   Hom(P^j,I^{j+t}) is zero when t<b-a: either j>a or j+t<b. Consequently RHom(C,N)
   is in D^{≥b-a}. This uses no finite Tor amplitude.
7. For a bounded constructible B, use a finite Postnikov induction. Remove its highest
   cohomology sheaf with the truncation triangle. Step 5 handles all shifts of that
   sheaf. Internal Hom takes this triangle contravariantly to a triangle; its natural
   long exact cohomology sequence and exact filtered colimits give a comparison ladder.
   The outer four maps are invertible by induction, so the five lemma gives the middle
   map. The base is zero, including the single-degree and empty-interval cases.
8. Fix n and an upper bound r. Choose m<min(-n,r), and use the triangle
   C=τ_{≤m-1}K → K → B=τ_{≥m}K → C[1]. B has constructible cohomology in [m,r].
   Step 6 shows that H^t RHom(C,G) vanishes for t<1-m, hence at t=n-1,n, for each
   G_i and its colimit. The long exact sequence identifies sheaf Ext^n(B,-) with
   sheaf Ext^n(K,-). Naturality identifies the colimit comparison square. Step 7
   makes its top arrow invertible, so its bottom arrow is invertible too.
-/
theorem isIso_sheafExt_filteredColimit
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategoryModule A X)
    (_hbounded : ∃ r : ℤ, ∀ j : ℤ, r < j →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj K))
    (_hconstructible : ∀ j : ℤ, ∃ S : Scheme.FiniteLocallyClosedStratification X,
      ∀ i : Fin S.n, Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ j).obj K)))
    (n : ℤ) {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (colimit.post G (sheafExtCoefficientFunctor X A K n)) := by
  sorry

end AlgebraicGeometry.Etale
