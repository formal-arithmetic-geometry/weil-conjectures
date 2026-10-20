/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparablyGenerated
import Sheaf.AlgebraicGeometry.SeparableFieldExtensionExchange
import Sheaf.AlgebraicGeometry.FieldExtensionPerfectComparison

/-!
# Canonical derived exchange for an extension of the ground field

Source: Stacks Project, Lemma 59.90.1, Tag 0F1C, statement and proof
(blueprint: lem-kun-0f1c-exchange).

The scalar extensions are the chosen pullbacks over Spec K. Their induced morphism is
the map of `Over.pullback`. Its first-projection equation supplies commutativity of
the canonical Cartesian square to the existing derived exchange transformation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical exchange for a field extension and a qcqs morphism is invertible on
bounded below abelian etale complexes with torsion cohomology of orders invertible in K.
Source: Stacks Project, Lemma 59.90.1, Tag 0F1C (blueprint: lem-kun-0f1c-exchange).

Proof plan, following the nine steps of the node:
1. Geometric stalk pullback, inverse-image composition and stalks of cohomology
   (lem-kun-stalk-as-pullback, lem-weil-pbc-derived-inverse-image-composition,
   lem-kun-stalks-of-cohomology) identify the stalks after extension with the original
   stalks. An integer invertible in K remains invertible in any extension field and
   on every scheme over that field. Exact inverse image preserves bounded belowness.
2. For separable L/K, lem-kun-separable-smooth-colimit expresses L as the filtered
   union of smooth finitely generated K-subalgebras. Base change preserves smoothness
   (lem-pc-proper-base-change); their spectra and all transition maps are affine.
   Lem-weil-pbc-affine-morphism-permanence gives the necessary qcqs properties.
3. The universal properties of limits and pullbacks identify S_L with the limit of
   these base changes of S, even when S is not quasi-compact. Apply lem-kun-0f09 with
   direct-image leg g, using its given qcqs assumptions, to obtain the separable case.
4. By lem-weil-pbc-perfect-purely-inseparable-overfield choose a perfect closure L'.
   In positive characteristic define K' inside L' by the elements having a p-power
   in K; Frobenius shows that it is a perfect purely inseparable field extension of K.
   In characteristic zero use K'=K and L'=L.
5. Lem-weil-pbc-perfect-field-separating-basis applied to finitely generated intermediate
   extensions proves that L'/K' is separable in the sense of
   def-weil-pbc-separable-field-extension; no algebraicity assumption is needed.
6. Lem-pc-homeo-pure-insep and arbitrary pullback identify the projections for K'/K
   and L'/L as universal homeomorphisms (def-weil-universal-homeomorphism).
7. Thm-weil-pbc-universal-homeomorphism-invariance gives exact equivalences on abelian
   etale sheaves. Apply them termwise and localize to get equivalences on D+; they
   preserve homology and bounded belowness, and agree with the recorded inverse image.
8. Lem-weil-pbc-qcqs-morphism-permanence preserves qcqs. Apply the separable case over
   K' to L'/K'. For the purely inseparable legs, use
   lem-weil-mate-iso-along-equivalences and the derived adjunctions
   (prop-weil-pbc-derived-inverse-image-adjunction). The mates are the specified
   derived exchanges (def-weil-pbc-derived-exchange), so those exchanges are invertible.
9. The horizontal pasting identities of lem-kun-bc-base-change identify the two
   composites through K' and through L. All composition comparisons are invertible.
   Cancel the invertible factors to obtain invertibility of the pullback of the
   requested exchange along S_L' to S_L. This inverse-image equivalence reflects
   isomorphisms, proving invertibility of the requested canonical map itself. -/
theorem isIso_derivedBaseChangeMapPlus_fieldExtension
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (T S : Over (Spec (.of K))) (g : T ⟶ S)
    [QuasiCompact g.left] [QuasiSeparated g.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (⟨by simp [Over.pullback_map_left]⟩ : CommSq
        (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left)
        g.left (pullback.fst S.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))))).app E) := by
  classical
  let M := perfectClosure L (AlgebraicClosure L)
  let : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  let P := perfectClosure K M
  have hsep : Algebra.IsSeparableExtension P M := by
    intro F hF
    let : Algebra.EssFiniteType P F := IntermediateField.essFiniteType_iff.mpr hF
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField P F
    exact ⟨(s : Set F), hs, hsep⟩
  let a := Spec.map (CommRingCat.ofHom (algebraMap K P))
  let TP := (Over.pullback a).obj T
  let SP := (Over.pullback a).obj S
  let gP := (Over.pullback a).map g
  let F := upperStar AddCommGrpCat.{u + 1} (pullback.fst T.hom a)
  let EP := F.mapDerivedCategoryPlus.obj E
  have sq : IsPullback (pullback.fst T.hom a) gP.left g.left
      (pullback.fst S.hom a) := by
    have outer : IsPullback (gP.left ≫ pullback.snd S.hom a)
        (pullback.fst T.hom a) a (g.left ≫ S.hom) := by
      simpa only [gP, Over.pullback_map_left, pullback.lift_snd, Over.w] using
        (IsPullback.of_hasPullback T.hom a).flip
    exact (outer.of_right (by simp [gP, Over.pullback_map_left])
      (IsPullback.of_hasPullback S.hom a).flip).flip
  let : QuasiCompact gP.left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let : QuasiSeparated gP.left :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hEP : HasTorsionCohomologyOfInvertibleOrder P TP EP.obj := by
    intro q Ω _ _ t x
    let H := (DerivedCategory.homologyFunctor
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj E.obj
    let e := ((Scheme.pointSmallEtale t).sheafFiber.mapIso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app E.obj).symm) ≪≫
        (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
          (pullback.fst T.hom a) t).app H
    obtain ⟨n, ⟨hn, hnK⟩, hx⟩ := hE q Ω (t ≫ pullback.fst T.hom a) (e.hom x)
    refine ⟨n, ⟨hn, ?_⟩, ?_⟩
    · simpa only [map_natCast] using
        (map_ne_zero_iff (algebraMap K P) (algebraMap K P).injective).mpr hnK
    · apply (ConcreteCategory.bijective_of_isIso e.hom).injective
      simpa only [map_nsmul, map_zero] using hx
  apply (isIso_fieldExtension_iff_of_purelyInseparable K L P M T S g E).mpr
  exact isIso_derivedBaseChangeMapPlus_separableFieldExtension P M hsep TP SP gP EP hEP

end AlgebraicGeometry.Etale
