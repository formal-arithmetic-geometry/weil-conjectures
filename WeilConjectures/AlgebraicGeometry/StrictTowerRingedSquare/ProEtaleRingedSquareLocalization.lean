/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization

/-! The canonical ringed inverse-image square is exact localization of its ordinary square.
Source: Stacks Project, Tag 0D6D.
(blueprint: lem-weil-pbc-ringed-square-localization) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingModuleAdjunction proEtaleRingCompositeCoefficients
  proEtaleCanonicalDerivedPullbackComparison

private theorem localization_transport
    {U V : Scheme.{t}} (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    {a b : Σ q : U ⟶ V,
      (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj R ≅ S} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg
        (fun z ↦ proEtaleRingModulePullback z.1 R S z.2) h)) =
      eqToIso (congrArg (fun z ↦ proEtaleRingDerivedPullback z.1 R S z.2) h) := by
  cases h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The published ambient pullback square is the exact descent of the ordinary square.
Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-ringed-square-localization).
Proof: the normalization theorem identifies each canonical derived compositor with
exact localization of the ordinary compositor. Its right-adjoint conjugate has the
same sectionwise fibre-product formula as exchangeModuleComposition, so uniqueness
identifies the ordinary isomorphisms. Exact localization preserves inverse,
composition and equality transport. Substitute these identities into the two
compositors defining the square. -/
theorem StrictTowerRingedSquare.ambientSquare_localization
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) :
    proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
        r.cf r.cg r.cg' r.cf' r.coherent =
      Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare := by
  unfold proEtaleAmbientRingedPullbackComparison
  dsimp only
  rw [composition_localization, composition_localization]
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, StrictTowerRingedSquare.exchangeModuleSquare,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  have ht := localization_transport r.RY r.RX' r.exchangeCoefficients_eq
  rw [ht]

end AlgebraicGeometry.Scheme
