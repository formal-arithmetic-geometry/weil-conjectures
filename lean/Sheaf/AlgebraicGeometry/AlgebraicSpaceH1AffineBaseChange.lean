/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules

/-! # First-cohomology vanishing and affine base change for algebraic spaces

Source: Stacks Project, Spaces Cohomology, Situation 07UY and Lemma 07V0
(lemma-vanishing-base-change)
(blueprint: lem-sfb-space-h1-vanishing-affine-base-change).

The ring of global functions is specified by its limit cone of regular functions on
all small etale charts. Normalization by the given map to Spec A identifies that ring
with A, and the same normalization in the conclusion identifies the actual canonical
map from B with an isomorphism. No alternative isomorphism of abstract rings is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {X Y X' : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}

/-- Affine morphisms preserve qcqs spaces with vanishing H1 of every quasi-coherent module.
Source: Stacks Project, Spaces Cohomology, Tag 07V0(1), lemma-vanishing-base-change
(blueprint: lem-sfb-space-h1-vanishing-affine-base-change).

Proof:
1. The chart/point quasi-compactness comparison is lem-sfb-qc-space-affine-etale-atlas
   and lem-a1-space-finite-affine-subatlas. Affine locality
   (lem-sfb-space-affine-locality) gives qcqs of Y.
2. For quasi-coherent G, affine direct image is quasi-coherent by
   lem-sfb-space-affine-module-base-change. The affine Leray comparison
   lem-sfb-space-affine-cohomology identifies H1(Y,G) with H1(X,f_*G).
   The latter vanishes by the hypothesis on X. Cohomology is that of the underlying
   additive sheaf, as required by def-weil-pbc-sites-and-cohomology. -/
theorem affine_preserves_qcqs_h1_vanishing
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1))
    (f : Y ⟶ X) (hf : MapIsAffine f) :
    CompactSpace (Point Y.obj.obj) ∧ IsAbsolutelyQuasiSeparated Y ∧
      ∀ (G : Y.Modules) (_ : G.IsQuasicoherent),
        Subsingleton (Sheaf.H ((SheafOfModules.toSheaf Y.structureSheaf).obj G) 1) := by
  sorry

/-- Arbitrary affine scalar extension has its prescribed ring of global functions.
The limit-cone normalization means precisely A = Gamma(X,O_X) with p inducing the
identity, and the conclusion uses the canonical pullback along p', not an arbitrary
ring isomorphism. The cartesian square may be any representative of the fibre product.
Source: Stacks Project, Spaces Cohomology, Tag 07V0(2), lemma-vanishing-base-change
(blueprint: lem-sfb-space-h1-vanishing-affine-base-change).

Proof:
1. The affine-coordinate formula lem-weil-pbc-fibre-product-affine-spectra shows that
   Spec B -> Spec A is affine. Its base change f is affine; affine locality and the
   chart/point comparison give qcqs of X'. Since Spec B is quasi-separated,
   lem-sfb-space-qcqs-permanence makes the relative diagonal of p' quasi-compact.
2. On every affine etale test Spec C -> Spec A, the direct image of O_Spec B has
   sections B tensor_A C. The chart-limit sections comparison, tilde sections, and
   affine pullback sections identify it with the etale associated module of B:
   lem-trf-space-chart-limit-enlarged-sections, lem-weil-pbc-spec-module-tilde-sections,
   lem-weil-pbc-module-pullback-affine-sections and def-sc-etale-qcoherent-module.
3. Affine module base change (lem-sfb-space-affine-module-base-change) identifies
   f_*O_X' with B tensor_A O_X. Apply lem-sfb-space-acyclic-global-module-sections
   with M = B. The enlarged-site model identifies its global sections with those on X'.
4. The counit and tensor formulas of lem-trf-space-chart-adjunction-tensor-realization
   send b tensor 1 to p'^sharp(b). Thus the computed bijection is the canonical ring
   map. Its chart restrictions are exactly the displayed cone projections; being an
   isomorphism is exactly the limit universal property with vertex B.
   The zero ring, empty spaces, non-flat maps, and infinitely generated algebras occur
   without any change in these formulas. -/
theorem affine_baseChange_global_functions
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1))
    (A B : CommRingCat.{u}) (φ : A ⟶ B)
    (p : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A))))
    (πA : (Functor.const X.EtaleSiteᵒᵖ).obj A ⟶ X.etaleForget.op ⋙ Scheme.Γ)
    (hA : IsLimit (Cone.mk A πA))
    (hp : ∀ T : X.EtaleSite,
      πA.app (op T) = (Scheme.ΓSpecIso A).inv ≫
        (yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left.appTop)
    (f : X' ⟶ X)
    (p' : X' ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec B))))
    (hsq : IsPullback f.hom.hom p'.hom.hom p.hom.hom
      (yoneda.map (Over.homMk (Spec.map φ) (specULiftZIsTerminal.hom_ext _ _)))) :
    MapIsAffine f ∧ CompactSpace (Point X'.obj.obj) ∧ IsAbsolutelyQuasiSeparated X' ∧
      MapIsQuasiCompact (pullback.diagonal p'.hom.hom) ∧
      ∃ πB : (Functor.const X'.EtaleSiteᵒᵖ).obj B ⟶ X'.etaleForget.op ⋙ Scheme.Γ,
        Nonempty (IsLimit (Cone.mk B πB)) ∧
          ∀ T : X'.EtaleSite,
            πB.app (op T) = (Scheme.ΓSpecIso B).inv ≫
              (yoneda.preimage (T.obj.hom ≫ p'.hom.hom)).left.appTop := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
