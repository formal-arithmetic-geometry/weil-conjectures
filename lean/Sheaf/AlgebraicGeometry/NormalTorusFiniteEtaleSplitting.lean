/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Sheaf.SecPurity.NormalLocallyConstantFiniteSection
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Finite etale splitting of tori over affine normal Noetherian schemes

Source: Cesnavicius, Problems about torsors over regular rings, Appendix A.1.2--A.1.8,
arXiv:2201.06424v4; Stacks, Tags 0357, 033M and 0BQL for the component refinements.
(blueprint: lem-sfb-normal-torus-finite-etale-splitting).

Group scheme isomorphisms are expressed as natural isomorphisms of their group-valued
functors of points. The recorded relativeSplitTorusFunctor is the functor of points of
G_m to the indicated finite power, including the trivial group in rank zero.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A relative torus over an affine normal Noetherian base is affine, smooth and finitely
presented, and splits after a finite etale surjection whose source is a finite disjoint
union of normal integral affine Noetherian schemes. The clopen opens U describe that
union; the natural isomorphisms are isomorphisms of group schemes by group-valued Yoneda.
Source: Cesnavicius, Problems about torsors over regular rings, Appendix A.1.2--A.1.8,
arXiv:2201.06424v4, and Stacks, Tags 0357, 033M and 0BQL.
(blueprint: lem-sfb-normal-torus-finite-etale-splitting).

Proof, following the accepted node:
1. By lem-weil-pbc-noetherian-finite-components and
lem-sfb-normal-locally-finite-components, decompose S into finitely many clopen normal
integral Noetherian components. Their affineness follows from being clopen in affine S.
For empty S use its identity cover and no components.
2. Fppf descent of maps (lem-pc-fppf-affine-refinement and
lem-weil-pbc-fpqc-representable-descent) first makes T commutative. Apply
lem-sfb-relative-torus-character-reconstruction to obtain its etale character lattice M,
its reconstruction, base-change compatibility and the three structure-map properties.
The rank is constant on each connected component of S.
3. The sheaf of bases of M is locally constant and locally nonempty, with fibre GL_r(Z).
The finite set of basis vectors and lem-weil-pbc-constant-sheaf-sections-locally-constant
identify bases with locally constant invertible matrices. Pull this sheaf to the
pro-etale site using def-weil-pbc-site-comparison-morphism and
lem-pur-etale-proetale-cover; inverse image preserves constants and local trivializations.
4. Apply lem-a1-normal-locally-constant-finite-section on each base component to obtain
a finite etale surjection and a section of this basis sheaf. By
det-pe-classical-sheaves-unit and restriction along the site comparison, that section
is an etale lattice basis. Character reconstruction identifies the pulled-back torus
with the split group of the same rank.
5. By lem-sfb-finite-etale-normal-generic-components the covers have finitely many clopen
normal integral components. They are Noetherian by lem-weil-pbc-finite-type-over-noetherian.
Take their disjoint union using lem-weil-pbc-scheme-coproduct-family. It is finite etale
and surjective over S, hence affine; its clopen components are affine by
lem-weil-pbc-spec-clopen-idempotent. Restrict the splitting to each component.
6. Etale means flat and locally finitely presented; together with finiteness this gives
def-pc-finite-locally-free. Rank zero uses the unique empty basis and the trivial group.
No nonempty-base or positive-rank assumption is needed. -/
theorem normal_torus_finite_etale_splitting
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (T : Over S) [GrpObj T] (hT : IsRelativeTorus T) :
    IsAffineHom T.hom ∧ Smooth T.hom ∧
      (LocallyOfFinitePresentation T.hom ∧ QuasiCompact T.hom ∧ QuasiSeparated T.hom) ∧
      ∃ (S' : Scheme.{u}) (f : S' ⟶ S),
        IsFinite f ∧ Etale f ∧ Surjective f ∧ f.IsFiniteLocallyFree ∧
        ∃ (n : ℕ) (U : Fin n → S'.Opens) (r : Fin n → ℕ),
          (∀ j, IsClosed (U j : Set S')) ∧
          (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ j, U j) = ⊤ ∧
          ∀ j, IsIntegral (U j).toScheme ∧ IsAffine (U j).toScheme ∧
            IsLocallyNoetherian (U j).toScheme ∧ CompactSpace (U j).toScheme ∧
            (∀ x : (U j).toScheme,
              IsDomain ((U j).toScheme.presheaf.stalk x) ∧
              IsIntegrallyClosed ((U j).toScheme.presheaf.stalk x)) ∧
            Nonempty ((Over.map ((U j).ι ≫ f)).op ⋙ yonedaGrpObj T ≅
              relativeSplitTorusFunctor (U j).toScheme (r j)) := by
  sorry

end AlgebraicGeometry
