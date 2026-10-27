/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTorDimensionOver
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-! # Perfect direct image with bounded coherent proper support

Source: Stacks Project, spaces-perfect.tex, Tag 08IS, lemma-perfect-direct-image;
Tag 0CZC, lemma-closed-proper-over-base
(blueprint: lem-sfb-space-bounded-coherent-finite-tor-image-perfect).

Noetherianity includes absolute quasi-separatedness. Supports are the closed
geometric-stalk supports with their reduced induced structures. The relative
Tor condition retains a single global interval on a possibly non-quasi-compact source.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A bounded coherent complex with proper cohomology supports and finite Tor dimension
relative to a Noetherian target has perfect direct image.
Source: Stacks Project, Tag 08IS; proper support is Tag 0CZC
(blueprint: lem-sfb-space-bounded-coherent-finite-tor-image-perfect).

Proof:
1. Put K = Rf_*H. By lem-sfb-space-proper-support-bounded-coherent-image, K has
   bounded coherent cohomology. Choose c with H^i(K)=0 for i>c. The Noetherian
   criterion lem-sfb-space-noetherian-pseudocoherent-criterion makes K pseudo-coherent.
2. For a quasi-coherent module F on Y, the canonical comparison of
   lem-sfb-space-proper-support-derived-projection-formula identifies K tensor^L F[0]
   with Rf_*(H tensor^L_{f^{-1}O_Y} (f^{-1}F)[0]). The relative Tor interval [a,b]
   bounds the latter tensor before direct image, uniformly in F.
3. The module categories are Grothendieck abelian by
   lem-pur-ringed-site-grothendieck-abelian. The canonical f_* is a right adjoint by
   def-trf-space-etale-module-functors, hence additive left exact. Apply
   thm-sp-truncation-e2 to a good lower truncation of the tensor complex. Its terms
   R^p f_* H^q have p>=0 and q>=a. The finite exhaustive separated abutment filtration
   gives H^n(Rf_*(...))=0 for n<a, with the same a for all F.
4. Set A=min(a,c). By lem-sfb-space-quasicoherent-tor-amplitude-test, the preceding
   lower bound for all quasi-coherent F, together with the upper bound c and
   quasi-separatedness of Y, gives Tor amplitude [A,c] against all module sheaves.
5. Apply lem-sfb-ringed-site-perfect-criterion: pseudo-coherence from step 1 and
   finite (hence locally finite) Tor dimension from step 4 give local bounded
   finite-free-retract models. These are exactly the asserted perfectness predicate.
Neither properness nor quasi-compactness of f was used. -/
theorem isPerfect_derivedDirectImage_of_bounded_coherent_finiteTor
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y)
    (_hYqc : CompactSpace (Point Y.obj.obj))
    (_hYqs : IsAbsolutelyQuasiSeparated Y)
    (_hYln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (_hft : MapIsLocally (@LocallyOfFiniteType) f)
    (_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (H : X.DerivedModules)
    (_hqc : X.derivedQCohProperty H)
    (_hcoherent : ∀ (n : ℤ) (T : X.EtaleSite), IsAffine (X.etaleForget.obj T) →
      Module.Finite (Γ(X.etaleForget.obj T, ⊤))
        (((X.schemeRestriction T).obj
          (X.smallModuleEquivalence.inverse.obj
            ((DerivedCategory.homologyFunctor X.SmallModules n).obj H))).val.obj (op ⊤)))
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules n).obj H))
    (_hsupport : ∀ n : ℤ, ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      (∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)) ∧
      Set.range (mapPoint i.hom.hom) =
        moduleSupport (X.smallModuleEquivalence.inverse.obj
          ((DerivedCategory.homologyFunctor X.SmallModules n).obj H)) ∧
      MapIsProper (i ≫ f))
    (_hTor : HasFiniteTorDimensionOver f H) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      Y.smallStructureSheaf ((derivedDirectImage f).obj H) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
