/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.RingTheory.ColimitCategoryFpAlgebras
import Mathlib.CategoryTheory.Presentable.Directed

/-! # The fibral criterion for multiplicative type

Source: Conrad, Reductive group schemes, Theorem B.4.1, printed pp.297--299
(blueprint: lem-sfb-multiplicative-type-fibral-criterion).

The conclusion uses affine members of an fppf covering, so that the recorded construction
`ringDiagonalizableGroup` applies directly. This expresses the same local splitting condition:
any fppf splitting family can be refined by affine open covers of its members. Conversely,
a family of affine splitting schemes is itself an fppf splitting family. Thus no construction
of the group-algebra spectrum over a nonaffine scheme is needed here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine flat finitely presented group scheme is of multiplicative type if its geometric
fibres are diagonalizable and the orders of all their torsion schemes are locally constant.
The algebraically closed extensions need not be algebraic. The torsion scheme is defined
without commutativity, using `torsionSubgroupScheme` as the identity fibre of the power map.

Source: Conrad, Reductive group schemes, Theorem B.4.1 and the opening of B.4, pp.297--299
(blueprint: lem-sfb-multiplicative-type-fibral-criterion).

Proof plan:
1. Around a point choose an affine open of S and its strict localization at the supplied
   geometric point (def-weil-pbc-strict-henselization-limit). Apply
   lem-sfb-strict-local-diagonalizable-clopen-lift to obtain a clopen group immersion
   D_C(M) → G_C which is an isomorphism on the closed fibre. The base is local by
   lem-weil-pbc-strict-henselization-local-structure; every open containing its closed
   point is the whole spectrum, as follows from the principal-open basis and the unit test.
2. Power maps and identity fibres commute with base change (def-pc-fibre-product).
   The affine tensor formula (lem-weil-pbc-fibre-product-affine-spectra) shows that orders
   are preserved by residue-field extension. Each locally constant torsion order is
   therefore constant on this local base. Do this separately for each n, without an
   infinite intersection of neighbourhoods.
3. The group-algebra Hopf formulas identify D_C(M)[n] with D_C(M/nM).
   The finitely generated abelian group theorem
   (lem-sbc-finitely-generated-abelian-group-structure) makes M/nM finite. The clopen
   immersion induces closed immersions on torsion fibres of equal finite order, hence
   isomorphisms: their coordinate maps are surjections of vector spaces of equal dimension.
4. Use lem-weil-common-extension-fields and def-weil-algebraic-closure to compare each
   residue field with its supplied splitting field in a common algebraically closed field.
   The image of the immersion is now a clopen subgroup of D_F(N) containing all n-torsion.
   This uses commutativity only in this split geometric fibre.
5. Decompose N by lem-sbc-finitely-generated-abelian-group-structure and use
   lem-sfb-diagonalizable-group-geometric-criteria to write D_F(N) as a torus times roots
   of unity. In positive characteristic separate the prime-to-characteristic parts.
   Every connected component contains a finite-order point, even with nonreduced torsion.
   A clopen subset meeting a connected component contains it. Thus the immersion is
   fibrewise surjective after field extension, hence surjective and an isomorphism
   (def-weil-open-immersion).
6. Descend this isomorphism to an affine pointed etale neighbourhood. Both coordinate
   algebras are finitely presented (lem-weil-pbc-lfp-affine-opens-finite-presentation
   and the finite abelian group presentation). Reindex strict henselization by
   lem-weil-pbc-cofiltered-limit-directed-reindex and apply parts (2),(3) of
   lem-weil-pbc-colimit-category-fp-algebras to descend the maps, inverse identities,
   and the finitely many group-law equations at one stage.
7. The pointed neighbourhoods cover S. Their composites with the affine-open inclusions
   are etale by lem-weil-pbc-etale-composition-cancellation, hence flat and locally of
   finite presentation (def-weil-etale-morphism). They give the required covering
   (def-pc-fppf-site), refined by affine opens if necessary. Over the empty base use
   the empty covering. -/
theorem multiplicativeType_fibral_criterion
    (S : Scheme.{u}) (G : Grp (Over S))
    [IsAffineHom G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (hgeom : ∀ s : S, ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (_ : Algebra (S.residueField s) Ω)
      (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫
          S.fromSpecResidueField s)).mapGrp.obj G) ≅ ringDiagonalizableGroup Ω M))
    (hfinite : ∀ (n : ℕ), 1 < n → ∀ s : S,
      IsFinite (torsionSubgroupScheme
        (((Over.pullback (S.fromSpecResidueField s)).mapGrp.obj G).X) n).hom)
    (horders : ∀ (n : ℕ), 1 < n → ∀ d : ℕ,
      IsOpen {s : S | (torsionSubgroupScheme
        (((Over.pullback (S.fromSpecResidueField s)).mapGrp.obj G).X) n).hom.finrankΓ = d}) :
    ∃ (I : Type u) (R : I → CommRingCat.{u}) (f : ∀ i : I, Spec (R i) ⟶ S),
      Presieve.ofArrows (fun i ↦ Spec (R i)) f ∈ Scheme.fppfPrecoverage S ∧
      ∀ i : I, ∃ (N : Type u) (_ : AddCommGroup N) (_ : AddGroup.FG N),
        Nonempty (((Over.pullback (f i)).mapGrp.obj G) ≅ ringDiagonalizableGroup (R i) N) := by
  sorry

end AlgebraicGeometry
