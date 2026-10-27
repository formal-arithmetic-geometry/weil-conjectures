/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The affine-space cell in a general Borel quotient

Source: Milne, Algebraic Groups (2017), Lemma 18.21, printed p.392;
Proposition 13.52, printed p.275; proof of Theorem 17.65, printed p.374.
Quotient geometry: Theorem 7.18 and Remark 7.16(c), pp.142--143; Theorem 17.9, p.354.
(blueprint: lem-sfb-borel-quotient-affine-cell)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A general Borel quotient is regular, integral, Noetherian and absolutely separated,
and contains a dense open affine space over the given field. The presheaf coequalizer
is the right-coset presheaf: its maps identify `g` and `gb`. The represented presheaf
is an fppf sheaf by subcanonicity; `ηQ` has the sheafification universal property. This states
the result for every scheme representing that sheaf, independently of its presentation.
The last equation makes the displayed affine-space isomorphism an F-isomorphism.

Source: Milne, Lemma 18.21, p.392, Proposition 13.52, p.275, and the proof of
Theorem 17.65, p.374; Theorem 7.18 and Remark 7.16(c), pp.142--143;
Theorem 17.9, p.354. (blueprint: lem-sfb-borel-quotient-affine-cell)

Proof plan, following the four steps of the node:
1. Apply lem-sfb-homogeneous-orbit-quotient-geometry with H = B. Uniqueness of
   sheafification identifies its quotient with Q. It gives a separated finite-type
   quotient and a faithfully flat map q with kernel pair G × B via (g,b) ↦ (g,gb).
   By lem-weil-pbc-finite-type-over-noetherian Q is Noetherian; a field is Noetherian.
   Apply lem-sc-separated-over-affine-scheme-separated and
   lem-weil-pbc-qcqs-over-affine for absolute separation and quasi-separatedness.
2. Apply lemma-nagata-finite-type-to-separated-target and pqf-lem-lft-fp-locnoeth
   to q. Apply lem-weil-pbc-qcqs-morphism-permanence to obtain finite presentation.
   Its base changes are fppf covers by lem-trf-fppf-covering-base-change, hence
   fpqc covers by lem-trf-fppf-covering-is-fpqc. The second projection supplies local
   lifts, and the kernel pair gives the coset equality on every test scheme. These
   are the quotient hypotheses of lem-sfb-algebraic-group-homogeneous-quotient.
3. Apply lem-sfb-borel-quotient-proper-geometry to obtain regularity, Noetherianity,
   smoothness and geometric integrality. The identity field extension gives integrality.
4. Apply lem-sfb-general-flag-isolated-linear-action for an equivariant projective
   embedding and a cocharacter with finitely many reduced fixed points. Together
   with quasi-compactness, def-pc-projective-morphism gives projectivity. Smoothness
   and integrality give the hypotheses of lem-sfb-projective-attracting-cells. Its
   dense open stratum is affine n-space; def-sbc-affine-space identifies this with
   the polynomial spectrum over F. The zero-dimensional case gives n = 0. -/
theorem borel_quotient_affine_cell
    {F : Type u} [Field F] [IsAlgClosed F]
    (G B : Over (Spec (.of F))) [GrpObj G] [GrpObj B]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : B ⟶ G) (hB : IsBorelGroupScheme i)
    (Q : Over (Spec (.of F)))
    (ηQ : coequalizer (yoneda.map (fst G B))
      (yoneda.map (lift (fst G B) (snd G B ≫ i) ≫ μ[G])) ⟶ yoneda.obj Q)
    (hηQ : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηQ ≫ f)) :
    IsRegularScheme Q.left ∧ IsIntegral Q.left ∧ IsNoetherian Q.left ∧
      Q.left.IsSeparated ∧
      ∃ (n : ℕ) (U : Q.left.Opens), Dense (U : Set Q.left) ∧
        ∃ e : U.toScheme ≅ Spec (.of (MvPolynomial (Fin n) F)),
          e.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : F →+*
            MvPolynomial (Fin n) F)) = U.ι ≫ Q.hom := by
  sorry

end AlgebraicGeometry
