/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # A derived Chow neighbourhood for an algebraic space

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0CTR, lemma-derived-chow,
clauses (1)--(5); finite presentation over the open in Tag 0CTS
(blueprint: lem-sfb-space-derived-chow-neighbourhood).

Products are specified by their presheaf universal property on schemes over Spec A.
The two displayed pullback squares specify the entire product open and its closed
subscheme, respectively. No atlas or derived comparison is assumed as input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived Chow neighbourhood with a pseudo-coherent kernel supported on its closed graph.
Source: Stacks Project, Tag 0CTR, lemma-derived-chow, clauses (1)--(5), and Tag 0CTS
(blueprint: lem-sfb-space-derived-chow-neighbourhood).

Proof:
1. Write A as the filtered union of finitely generated integer subalgebras using
lemma-nagata-noetherian-inverse-system-affine. Descend X and its separatedness by
lem-sfb-fp-space-limit-category and lem-sfb-space-descend-separated. The descended base
is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
2. By lem-sfb-space-fp-qcqs-source and lem-sfb-qc-space-affine-etale-atlas, choose an
 affine etale chart through the image of x. Embed it in projective space by
lem-chow-affine-immersion and form its schematic closure Y using
lemma-nagata-scheme-image-ideal-qc. Projective properness and
lem-sfb-space-qcqs-permanence make the immersion quasi-compact. By
lemma-nagata-immersion-open-in-scheme-image it is an open of Y. Choose V in projective
space cutting out that open.
3. Apply lem-sfb-space-partial-section-schematic-image to its graph in X times Y.
This produces Z closed in X times projective space, whose inverse image W over V is
that chart. Thus W is etale over X, closed in V, and contains a point above x.
4. Standard projective charts (lem-weil-pbc-projective-space-standard-charts),
lem-weil-pbc-finite-type-over-noetherian and lem-sfb-space-qcqs-source-products show the
ambient spaces are Noetherian. Apply lem-sfb-space-closed-coherent-modules to Z.
5. The structure direct image is coherent, with support Z. On every Noetherian affine
etale chart, lem-sfb-affine-etale-derived-module-realization identifies it with the
associated module of a finite module. Resolve that module successively by finite free
modules. Exactness of the associated-module functor gives the local bounded-above
finite-free model required by def-sfb-space-pseudocoherent-complex. Set E to this
structure direct image in degree zero. By lem-sfb-space-closed-structure-finite-presentation,
the closed immersions of Z and Y are finitely presented; so is the restriction W into V.
6. Pull back the geometric data to A. Projective base change is
lemma-nagata-projective-space-base-change-pullback. Closed immersions and finite
presentation persist on scheme tests, and lem-weil-pbc-etale-scheme-base-change gives
etaleness. Use lem-a1-space-fibre-product-point to choose a point above x; uniqueness
is neither asserted nor used.
7. Set E to the derived pullback of the descended E. The local finite-free models are
K-flat by lem-pc-bounded-above-flat-kflat-site and remain such after pullback. They show
pseudo-coherence. Off the inverse-image closed subset the pullback is zero, so every
cohomology support lies in Z. Compose restrictions by def-sfb-space-derived-pullback.
8. On the entire product open, use lem-sfb-space-relative-flat-closed-kernel-base-change.
Its flatness hypotheses follow from etaleness of W over X and the polynomial projective
charts (lem-nagata-polynomial-projection-flat). It identifies the pulled-back kernel
with the closed structure direct image. Restriction of ordinary direct image commutes
with the target open, by the chart limits of def-trf-space-etale-module-functors.
This gives the required isomorphism on X times V, not just on W. -/
theorem exists_derivedChow_neighbourhood
    (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [∀ Y : AlgebraicSpace (Spec A), HasDerivedCategory.{w} Y.SmallModules]
    (hsep : IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : MapIsQuasiCompact (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hlfp : ∀ (U : Over (Spec A)) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFinitePresentation U.hom)
    (x : Point X.obj.obj) :
    ∃ (n : ℕ) (T Z Tᵥ : AlgebraicSpace (Spec A))
      (p : T ⟶ X) (q : T ⟶ schemeSpace (chowProjectiveSpace A n)) (h : Z ⟶ T)
      (V : (chowProjectiveSpace A n).left.Opens)
      (r : Tᵥ ⟶ T) (qᵥ : Tᵥ ⟶ schemeSpace (chowProjectiveOpen A n V))
      (W : Over (Spec A)) (k : schemeSpace W ⟶ Z) (j : W ⟶ chowProjectiveOpen A n V)
      (z : Point Z.obj.obj) (w₀ : W.left) (E : T.DerivedModules),
      Nonempty (IsLimit (BinaryFan.mk p.hom.hom q.hom.hom)) ∧
      IsRepresentableWith (fun _ _ a ↦
        IsClosedImmersion a.left ∧ LocallyOfFinitePresentation a.left) h.hom.hom ∧
      IsPullback r.hom.hom qᵥ.hom.hom q.hom.hom
        (chowProjectiveOpenInclusion A n V).hom.hom ∧
      IsPullback k.hom.hom (yoneda.map j) (h ≫ q).hom.hom
        (chowProjectiveOpenInclusion A n V).hom.hom ∧
      IsClosedImmersion j.left ∧ LocallyOfFinitePresentation j.left ∧
      IsEtale (k ≫ h ≫ p).hom.hom ∧
      schemePointMap k.hom.hom w₀ = z ∧ mapPoint (h ≫ p).hom.hom z = x ∧
      T.IsPseudoCoherent E ∧
      (∀ i : ℤ, moduleSupport ((T.smallModuleEquivalence.inverse).obj
        ((DerivedCategory.homologyFunctor T.SmallModules i).obj E)) ⊆ pointImage h.hom.hom) ∧
      Nonempty ((spaceDerivedPullback r).obj E ≅
        (spaceDerivedPullback r).obj ((DerivedCategory.singleFunctor T.SmallModules 0).obj
          ((smallModuleDirectImage h).obj (SheafOfModules.unit Z.smallStructureRings)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
