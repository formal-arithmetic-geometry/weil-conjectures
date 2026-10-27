/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.CategoryTheory.Yoneda

/-! # An fpqc schematic cover for a flat group algebraic space over a trait

Source: Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques
sur une base de dimension 1, Mémoires SMF 33 (1973), Proposition 3.4.1, printed p.52
(blueprint: lem-sfb-flat-group-space-fpqc-scheme-cover).

The group law is supplied by a group-valued presheaf with underlying presheaf `G`.
Restriction along `Over.map p` is the group sheaf `G ×_S T` on schemes over `T`.
The conclusion identifies this restriction with a group scheme's group-valued Yoneda
presheaf, so that the representation respects all the group operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated flat group algebraic space locally of finite type over a DVR becomes
schematic after an fpqc base change, retaining separatedness, flatness and local finite
presentation. Commutativity, smoothness and quasi-compactness of the group are not assumed.
Source: Anantharaman, Proposition 3.4.1, printed p.52
(blueprint: lem-sfb-flat-group-space-fpqc-scheme-cover).

Proof:
1. Choose an étale chart through the special-fibre identity. Its flat locally finite type
   structure over the Noetherian DVR makes it locally Noetherian
   (pqf-lem-locnoeth-lft). In an affine chart take a prime minimal over the uniformizer
   (lem-weil-pbc-minimal-prime-over-proper-ideal). Its local dimension is at most one by
   lem-sfb-krull-principal-ideal-height-bound. The lemma
   lem-sfb-space-schematic-near-height-one gives a scheme open meeting the special fibre.
2. Local finite type over the Noetherian ring implies local finite presentation by
   lem-weil-pbc-finite-type-noetherian-finite-presentation. The image of this flat scheme
   open is open by lem-weil-pbc-flat-lfp-open. Since it contains the closed point of the
   trait, it meets both fibres. Every original affine chart is also finitely presented.
3. Use lem-sfb-trait-absolute-normalization-local-sections to take the normalization in an
   algebraic closure of the fraction field as an fpqc cover. Pull back the space, charts,
   scheme open and group operations (lem-trf-space-fibre-products-etale-covers).
   Flatness and local finite presentation persist on the charts by
   lem-sfb-space-flat-proper-fp-locality; separatedness persists by
   lem-sfb-space-separated-fp-composition. All residue fields of the new base are
   algebraically closed and the scheme open meets every fibre.
4. Over each special-fibre point choose a rational point u of the scheme open, using
   lem-sc-lft-over-field-jacobson-space and lem-weil-pbc-closed-point-residue-field-base.
   For any rational group point x lift xu⁻¹ to a rational point of an étale chart.
   The normalization local-section lemma extends it to a section near the base point.
5. Left translation by this section carries the scheme open to a scheme open containing
   x. Its inverse is translation by the inverse section, so no commutativity is needed.
   Scheme tests verify openness and representability directly, without scheme descent.
6. The generic open of the normalization is the spectrum of the algebraic closure of the
   fraction field. The same rational-point and translation argument covers its rational
   group points, with no assertion that they extend over the new base.
7. The largest scheme open (lem-sfb-space-largest-schematic-open) contains all these
   translates. On each fibre, pull it back to an étale atlas. The Jacobson and residue-field
   lemmas show that its complement is empty. The point/open calculus
   lem-a1-space-point-open-calculus then shows that the largest scheme open is the whole
   space. Yoneda full faithfulness (lem-galois-yoneda-fully-faithful) transfers the group
   operations and identities to the representing scheme. The properties from step 3
   give the separated flat locally finitely presented structure morphism. -/
theorem exists_fpqc_groupScheme_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : AlgebraicSpace (Spec (CommRingCat.of R)))
    (F : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{u})
    (hF : Nonempty (F ⋙ forget GrpCat ≅ G.obj.obj))
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj)))
    (hflat : ∀ (U : Over (Spec (CommRingCat.of R)))
      (a : yoneda.obj U ⟶ G.obj.obj), IsEtale a → Flat U.hom)
    (hlft : ∀ (U : Over (Spec (CommRingCat.of R)))
      (a : yoneda.obj U ⟶ G.obj.obj), IsEtale a → LocallyOfFiniteType U.hom) :
    ∃ (T : Scheme.{u}) (p : T ⟶ Spec (CommRingCat.of R)),
      Presieve.singleton p ∈ Scheme.fpqcPrecoverage (Spec (CommRingCat.of R)) ∧
      QuasiCompact p ∧
      ∃ (H : Over T) (_ : GrpObj H),
        IsSeparated H.hom ∧ Flat H.hom ∧ LocallyOfFinitePresentation H.hom ∧
          Nonempty (yonedaGrpObj H ≅ (Over.map p).op ⋙ F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
