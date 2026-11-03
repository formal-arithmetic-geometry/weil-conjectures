/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualityLocallyClosedComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedCounitComparison
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedRelativeHomIdentity
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion

/-!
# Locally closed exceptional comparison for geometric fields and finite rings

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-weil-finite-duality-site-comparison.proof.md, second paragraph, with the released
Wei Yang #1441 item 28 field correction and #1423 finite coefficient convention
(blueprint: lem-weil-finite-duality-locally-closed-comparison).

The existing `LocallyClosedExceptionalComparison` records the specified comparison maps,
not just their endpoints. Its `bounded`, `gamma`, `counit`, `transport`,
`unit_normalization`, and `relative_hom` fields express the six comparison clauses.
The existing `locallyClosed_comparison_factorization` applies to every finite ring and
supplies factorization independence, including the normalized gamma and transport squares.
This module adds the geometric existence statement using that same interface.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Locally closed exceptional inverse image commutes with the site comparison over a
finite or algebraically closed field of characteristic different from `l`, for every
finite commutative ring killed by a power of `l`.

`LocallyClosedExceptionalComparison` uses the pasted ordinary derived adjunctions.
Its `gamma` is fixed by the equation with the specified closed/open comparison `Delta`
and the pasted counits. The `transport` field identifies the pro-etale value with
`nu_S^* s^times Rnu_T,*`; `unit_normalization` fixes its composite with `gamma` to the
image of the comparison unit, after the counit-compatible etale adjoint identification.
The `relative_hom` equation identifies the adjunction maps for every bounded-below
etale-origin test object and every origin witness. The general theorem
`locallyClosed_comparison_factorization` identifies these data between factorizations.
No Noetherian or quasi-compact hypothesis is added: these witnesses are conclusions.

Source: latest blueprint, `lem-weil-finite-duality-site-comparison.proof.md`, second
paragraph; released field correction Wei Yang #1441 item 28 and finite ring convention
Wei Yang #1423 (blueprint: lem-weil-finite-duality-locally-closed-comparison).

Proof plan, following the node's four steps:
1. Apply `lem-sf-locally-closed-geometric-closure-bounds`. Finite type over a field gives
Noetherian S and T; an open of T is Noetherian, so V and the closed complements are
quasi-compact. The scheme-theoretic image supplies the closure compactification.
Exact open restriction and the right adjoint of exact closed direct image preserve a
lower bound. This constructs the ambient adjoints and the normalized comparison with
the ordinary etale closure right adjoint, and bounds J_et M for bounded constructible M.
2. Apply `lem-sf-locally-closed-counit-comparison`. On v_et^* M use the closed exceptional
comparison and its adjoint/presentation transport. Compose with the specified open
restriction comparison. The closed counit equation, naturality, and the normalized open
counit equation give epsilon_p F_p(gamma) Delta = C_T(epsilon_e). Transposition uniquely
identifies this composite with the canonical counit mate, hence proves naturality and
invertibility without invoking biduality.
3. Apply `lem-sf-locally-closed-origin-hom-chain`. Lift a morphism on etale-origin tests
through the fixed-module Hom bijection and transpose it on the etale side. The pasted
pro-etale transpose equals gamma followed by the comparison image of that transpose.
The normalized comparison-class transpose equals rho followed by the same image, where
rho = C_S(r followed by s^times(eta)). The site comparison unit eta is invertible on
bounded-below inputs. Therefore theta = gamma inverse followed by rho is invertible,
satisfies unit_normalization, and identifies the Hom bijections. Naturality in an
arbitrary origin witness proves relative_hom and independence of that witness; applying
these Hom bijections to identities identifies their units and counits.
4. Apply `lem-sf-locally-closed-right-comparison-coherence` to the normalized
factorization changes. It gives the gamma and transport squares, the identity and
cocycle laws, and agreement of the pasted units and counits. In the recorded interface
these squares and uniqueness are `locallyClosed_comparison_factorization`.
-/
theorem finiteDuality_locallyClosed_comparison_geometric
    (k : Type u) [Field k] (_hbase : Finite k ∨ IsAlgClosed k)
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)
    (A : Type (u + 1)) [CommRing A] [Finite A] (_hA : ∃ n : ℕ, (l : A) ^ n = 0)
    {S V T : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (_hs : (c ≫ v) ≫ aT = aS) :
    ∃ hT : IsNoetherian T, ∃ hqc : QuasiCompact (c ≫ v),
      Nonempty (@LocallyClosedExceptionalComparison A inferInstance inferInstance
        S V T c v inferInstance inferInstance hT hqc) := by
  have : IsNoetherian T := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aT
    __ := QuasiCompact.compactSpace_of_compactSpace aT }
  have : IsNoetherian S := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aS
    __ := QuasiCompact.compactSpace_of_compactSpace aS }
  have : QuasiCompact (c ≫ v) := inferInstance
  let W : V.Opens := ⟨(Set.range c)ᶜ,
    (IsClosedImmersion.isClosedEmbedding c).isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := v.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W := W.ι.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := inferInstance
  have hij : IsCompl (Set.range c) (Set.range W.ι) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  let a : LocallyClosedComparisonAdjoints A c := {
    etale := (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint
    proetale := (closedUpperShriek (ModuleCat.{u + 1} A) c W.ι).rightDerivedFunctor
    etaleAdjunction := Adjunction.ofIsLeftAdjoint _
    proetaleAdjunction := derivedLowerStarClosedUpperShriekAdjunction c W.ι hij }
  have bounded (M : Etale.BoundedConstructibleDerivedCategory A T) :
      _root_.DerivedCategory.TStructure.t.plus ((a.etaleRight v).obj M.obj) := by
    obtain ⟨k, b, hkb, hz⟩ := M.property.2
    have : M.obj.IsGE k :=
      (_root_.DerivedCategory.isGE_iff M.obj k).2 (fun i hi ↦ hz i (.inl hi))
    have : ((Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj M.obj).IsGE k :=
      Functor.isGE_mapDerivedCategory_obj _ M.obj k
    refine ⟨k, ?_⟩
    exact exactDerivedAdjunction_isGE (Etale.lowerStar (ModuleCat.{u + 1} A) c)
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory |>
        Functor.isoWhiskerLeft DerivedCategory.Q |>.trans
          (Etale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryFactors)
      a.etaleAdjunction _ k
  let g := locallyClosedCounitMate A c v a bounded
  have (M : Etale.BoundedConstructibleDerivedCategory A T) : IsIso (g.app M) :=
    locallyClosedCounitMate_isIso_finiteCoefficients k _hbase l (Ne.symm _hl)
      A _hA aS aT c v _hs a bounded M
  have : IsIso g := NatIso.isIso_of_isIso_app g
  let gamma := asIso g
  have hc (M : Etale.BoundedConstructibleDerivedCategory A T) :
      (locallyClosedExtensionComparison A c v).hom.app
          ⟨(a.etaleRight v).obj M.obj, bounded M⟩ ≫
        (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
          (a.proetalePasted v).counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((a.etalePasted v).counit.app M.obj) := by
    have h := ((a.proetalePasted v).homEquiv _ _).symm_apply_apply
      ((locallyClosedExtensionComparison A c v).inv.app
          ⟨(a.etaleRight v).obj M.obj, bounded M⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
          ((a.etalePasted v).counit.app M.obj))
    rw [Adjunction.homEquiv_counit] at h
    change _ ≫ ((locallyClosedProEtaleExtension A c v).map _ ≫ _) = _
    erw [show (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
        (a.proetalePasted v).counit.app _ = _ from h]
    simp
  let CS := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let CT := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let U := (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
  let X := locallyClosedEtaleExceptional A (c ≫ v)
  let r := locallyClosedEtaleRightIso v a
  let eta := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit
  let rho : (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ a.etaleRight v ⋙ CS ⟶
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ CT ⋙ U ⋙ X ⋙ CS := {
    app M := CS.map (r.hom.app M.obj ≫ X.map (eta.app M.obj))
    naturality M N f := by
      have hr := r.hom.naturality f.hom
      change (a.etaleRight v).map f.hom ≫ r.hom.app N.obj =
        r.hom.app M.obj ≫ X.map f.hom at hr
      have he := eta.naturality f.hom
      change f.hom ≫ eta.app N.obj = eta.app M.obj ≫ U.map (CT.map f.hom) at he
      change CS.map ((a.etaleRight v).map f.hom) ≫
        CS.map (r.hom.app N.obj ≫ X.map (eta.app N.obj)) =
          CS.map (r.hom.app M.obj ≫ X.map (eta.app M.obj)) ≫
            CS.map (X.map (U.map (CT.map f.hom)))
      rw [← CS.map_comp, ← CS.map_comp]
      congr 1
      rw [← Category.assoc, hr, Category.assoc, ← X.map_comp, he,
        X.map_comp, Category.assoc] }
  have hrho (M : Etale.BoundedConstructibleDerivedCategory A T) : IsIso (rho.app M) := by
    obtain ⟨k, b, hkb, hz⟩ := M.property.2
    have hM : _root_.DerivedCategory.TStructure.t.plus M.obj :=
      ⟨k, (_root_.DerivedCategory.isGE_iff M.obj k).2 (fun i hi ↦ hz i (.inl hi))⟩
    have : IsIso (eta.app M.obj) :=
      isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) T M.obj hM
    dsimp [rho]
    infer_instance
  have : IsIso rho := NatIso.isIso_of_isIso_app rho
  let theta := gamma.symm ≪≫ asIso rho
  refine ⟨inferInstance, inferInstance, ⟨{
    adjoints := a
    bounded := bounded
    gamma := gamma
    counit := hc
    transport := theta
    unit_normalization := ?_
    relative_hom := ?_ }⟩⟩
  · intro M
    change gamma.hom.app M ≫ (gamma.inv.app M ≫ rho.app M) = rho.app M
    simp
  · exact locallyClosedRelativeHomIdentity A c v a bounded gamma hc

end AlgebraicGeometry.ProEtale
