/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SpacePseudoCoherentPerfectApproximation
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Relative module Hom over a Noetherian algebraic-space base

Source: Stacks Project, quot.tex, Tag 08JY (lemma-noetherian-hom), in Situation 08JT;
spaces-perfect.tex, Tag 0CZI (lemma-module-support-proper-over-base)
(blueprint: lem-sfb-noetherian-module-hom).

The representing bijections include their tensor-pullback naturality on every scheme test.
The fibre products, projections, and tensor composition comparisons are the existing ones
used by the proper-support Quot presheaf; no finite-presentation hypothesis on f is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative Hom functor of finite type quasi-coherent modules, with relatively flat
and properly supported target, is affine and of finite presentation over a Noetherian base.
Source: Stacks Project, quot.tex, Tag 08JY, lemma-noetherian-hom, Situation 08JT;
spaces-perfect.tex, Tag 0CZI (blueprint: lem-sfb-noetherian-module-hom).

Proof:
1. Choose the proper closed carrier Z of G. It is quasi-compact over the quasi-compact
   base. By lem-a1-space-affine-etale-cover and lem-a1-space-etale-open-image, finitely
   many affine etale chart images cover it. Their union U is a quasi-compact open in X.
   By lem-sfb-space-finite-type-support-pullback, G_T vanishes off U_T for every test T.
   Restriction of Hom to U_T is bijective: glue a map there with zero off Supp(G_T).
   These inverse maps commute with tensor pullback, so replace X by U.
2. By pqf-lem-locnoeth-lft and lem-sfb-space-qcqs-source-products, this X is Noetherian
   and f is quasi-compact and quasi-separated. By lem-sfb-space-qcoh-affine-chart-calculus,
   F and G have finite modules on affine Noetherian charts. Kernels of finite free
   presentations are finite, so both modules are coherent and finitely presented.
3. By lem-sfb-space-noetherian-pseudocoherent-criterion, F[0] is pseudo-coherent. Apply
   lem-sfb-space-pseudocoherent-perfect-approximation in degree -1 to obtain perfect P
   and P → F[0], an isomorphism on H^0, with P having no positive cohomology.
4. Locally split off the exact positive tail of a bounded finite-projective model of P.
   Tensoring the resulting nonpositive model computes P_T. Right exactness of tensor
   gives H^0(P_T) = F_T for every T, even for nonflat base change. These canonical maps
   agree on overlaps, by def-weil-pbc-strict-perfect-coefficient-package and
   def-trf-space-etale-module-functors. No identification of Lh^*G with G_T is used.
5. By lem-sfb-ringed-site-nonpositive-derived-hom, precomposition gives natural
   Hom(F_T,G_T) ≃ Hom(P_T,G_T[0]), and RHom(P_T,G_T) has no negative cohomology.
6. Put K = Rf_*RHom(P,G). By lem-sfb-ringed-site-perfect-duality, P dual is perfect and
   RHom(P,G) is its derived tensor with G. By lem-sfb-space-module-proper-carrier-support,
   the carrier condition is proper scheme-theoretic support. Apply
   lem-sfb-space-noetherian-tensor-perfect to conclude that K is perfect.
7. Apply lem-sfb-space-flat-coefficient-rhom-base-change to obtain the canonical
   Lg^*K ≃ Rf_T,*RHom(P_T,G_T), with ordinary tensor pullback G_T on the right.
8. The module direct image is a right adjoint, hence left exact. By
   lem-weil-pbc-derived-functor-negative-vanishing and prop-pur-kinjective-resolutions-exist,
   its derived functor preserves the lower bound zero. Hence every Lg^*K has no negative
   cohomology. This is an application on D^+ inside the unbounded category.
9. By lem-pur-rhom-global-sections, lem-trf-space-enlarged-etale-ringed-site-model and
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition, the derived Hom set is
   naturally H^0(T,Lg^*K). The Hom formula, composition, and base-change comparisons
   identify tensor pullback of a module map with pullback of its global-section class.
10. Apply lem-sfb-space-connective-perfect-sections-affine to K. It represents these
    sections by an algebraic space affine and finitely presented over B. Compose its
    bijections with steps 1, 5 and 9. Naturality is precisely the displayed equation,
    with source and target normalized by properQuotSourceIso. -/
theorem exists_affine_finitePresentation_moduleHom_of_noetherian
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (hf : MapIsLocally (@LocallyOfFiniteType) f)
    (hfqs : MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom))
    (hBqc : ∃ (U : Over S) (a : yoneda.obj U ⟶ B.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hBqs : IsAbsolutelyQuasiSeparated B)
    (hBnoeth : ∀ V : B.EtaleSite, IsLocallyNoetherian (B.etaleForget.obj V))
    (F G : X.QCoh) (hF : F.obj.IsFiniteType) (hG : G.obj.IsFiniteType)
    (hGflat : ModuleIsFlatOver f G.obj)
    (hGsupport : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ N : Z.Modules,
        N.IsQuasicoherent ∧ N.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj N ≅ G.obj)) :
    ∃ (H : AlgebraicSpace S) (h : H ⟶ B),
      MapIsAffine h ∧ ProperQuotFinitePresentation h ∧
      ∃ e : ∀ T : ProperQuotTest B,
        {a : yoneda.obj T.left ⟶ H.obj.obj // a ≫ h.hom.hom = T.hom} ≃
          ((moduleTensorPullback (properQuotFst f T)).obj F.obj ⟶
            (moduleTensorPullback (properQuotFst f T)).obj G.obj),
        ∀ (T' T : ProperQuotTest B) (k : T' ⟶ T)
          (a : {a : yoneda.obj T.left ⟶ H.obj.obj // a ≫ h.hom.hom = T.hom})
          (a' : {a : yoneda.obj T'.left ⟶ H.obj.obj // a ≫ h.hom.hom = T'.hom}),
          a'.val = yoneda.map k.left ≫ a.val →
          e T' a' = (properQuotSourceIso f F.obj k).inv ≫
            (moduleTensorPullback (properQuotFibreMap f k)).map (e T a) ≫
              (properQuotSourceIso f G.obj k).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
