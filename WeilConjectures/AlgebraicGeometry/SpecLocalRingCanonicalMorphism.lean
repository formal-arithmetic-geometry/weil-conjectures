/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-!
# The canonical morphism from the spectrum of a local ring

Source: Stacks Project, Schemes, Tags 01J6, 02NA, 01J7; Cohomology of Schemes, Tag 02OD;
Sheaves, Tag 0098 (blueprint: lem-weil-pbc-spec-local-ring-canonical-morphism).

## Main statements
* `Scheme.fromSpecStalk_affine_description`: localization and affine factorization.
* `Scheme.fromSpecStalk_local_properties`: the image, stalk maps, and flatness.
* `Scheme.fromSpecStalk_module_stalk`: the unit induces an isomorphism at the closed point.
* `Scheme.fromSpecStalk_quotient_factorization`: factorization for proper quotients.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-- The closed point maps to `y`; the image is its generalizations, every neighborhood
pulls back to the whole spectrum, all stalk maps are isomorphisms, the closed stalk map
is the identity after the canonical identifications, and the morphism is flat.
Source: Stacks, Tags 01J6, 02NA, 01J7, 02OD
(blueprint: lem-weil-pbc-spec-local-ring-canonical-morphism).
Proof (node steps 3--6): localization prime correspondence gives the image and closed
point. Generalizations belong to every neighborhood. Factor each stalk map through
an affine open immersion and the spectrum of a localization; both maps are isomorphisms
by affine-open-stalk-localization and localization-prime-residue-field-iso. At the
closed point, germ compatibility shows the normalized stalk map is the identity,
first on affine germs, then on fractions. This identifies the pair in 01J6 as `(y,id)`.
Finally isomorphisms of rings are flat, so the stalkwise criterion gives flatness. -/
theorem fromSpecStalk_local_properties (Y : Scheme.{u}) (y : Y) :
    (Y.fromSpecStalk y) (closedPoint (Y.presheaf.stalk y)) = y ∧
    Set.range (Y.fromSpecStalk y) = {x : Y | x ⤳ y} ∧
    (∀ (V : Y.Opens), y ∈ V → (Y.fromSpecStalk y) ⁻¹ᵁ V = ⊤) ∧
    (∀ q : Spec (Y.presheaf.stalk y), IsIso ((Y.fromSpecStalk y).stalkMap q)) ∧
    stalkClosedPointTo (Y.fromSpecStalk y) =
      (Y.presheaf.stalkCongr
        (Inseparable.of_eq (fromSpecStalk_closedPoint (X := Y) (x := y)))).hom ∧
    Flat (Y.fromSpecStalk y) := by
  have hstalk : ∀ q : Spec (Y.presheaf.stalk y),
      IsIso ((Y.fromSpecStalk y).stalkMap q) := by
    intro q
    obtain ⟨V, hV, hy, _⟩ :=
      Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (show y ∈ (⊤ : Y.Opens) from trivial)
    rw [← hV.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk,
      Hom.stalkMap_comp]
    let : Algebra (Y.presheaf.obj (op V)) (Y.presheaf.stalk y) :=
      (Y.presheaf.germ V y hy).hom.toAlgebra
    have := hV.isLocalization_stalk ⟨y, hy⟩
    let R := Y.presheaf.obj (op V)
    let A := Y.presheaf.stalk y
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) q.asIdeal
    let e := IsLocalization.algEquiv
      (q.asIdeal.comap (algebraMap R A)).primeCompl
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (Localization.AtPrime q.asIdeal)
    have he : e.toRingHom = Localization.localRingHom
        (q.asIdeal.comap (algebraMap R A)) q.asIdeal (algebraMap R A) rfl := by
      apply IsLocalization.ringHom_ext (q.asIdeal.comap (algebraMap R A)).primeCompl
      ext r
      change e (algebraMap R _ r) = _
      simp only [RingHom.comp_apply]
      rw [AlgEquiv.commutes, Localization.localRingHom_to_map]
      rfl
    have : IsIso (CommRingCat.ofHom (Localization.localRingHom
        (q.comap (Y.presheaf.germ V y hy).hom).asIdeal q.asIdeal
        (Y.presheaf.germ V y hy).hom rfl)) := by
      change IsIso (CommRingCat.ofHom (Localization.localRingHom
        (q.asIdeal.comap (algebraMap (Y.presheaf.obj (op V)) (Y.presheaf.stalk y)))
        q.asIdeal (algebraMap (Y.presheaf.obj (op V)) (Y.presheaf.stalk y)) rfl))
      rw [← he]
      exact e.toRingEquiv.toCommRingCatIso.isIso_hom
    have : IsIso ((Spec.map (Y.presheaf.germ V y hy)).stalkMap q) := by
      rw [← localRingHom_comp_stalkIso]
      infer_instance
    infer_instance
  refine ⟨fromSpecStalk_closedPoint, range_fromSpecStalk, ?_, hstalk,
    stalkClosedPointTo_fromSpecStalk y, ?_⟩
  · intro V hy
    apply top_unique
    intro q _
    have hspec : (Y.fromSpecStalk y) q ⤳ y := by
      have h := Set.mem_range_self (f := Y.fromSpecStalk y) q
      rw [range_fromSpecStalk] at h
      exact h
    exact hspec.mem_open V.isOpen hy
  · apply Flat.of_stalkMap
    intro q
    have := hstalk q
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- The map on germs induced by the canonical tensor-pullback unit is an isomorphism
at the closed point. The source point is written as `c(y')`, equal to `y` by the
preceding statement, to avoid noncanonical casts. Restricting scalars along the closed
stalk map expresses the target as an `O_{Y,y}`-module.
Source: Stacks, Tags 0098, 02NA
(blueprint: lem-weil-pbc-spec-local-ring-canonical-morphism).
Proof (node step 7): module-stalk-pullback identifies the target with extension of
scalars along the closed stalk map and the unit on germs with `s_y ⊗ 1`. The ring map
is the identity under the closed-stalk identification (step 5). Hence the tensor map
has inverse `m ⊗ b ↦ b m`. Composing gives the claimed module isomorphism and its germ
formula; every stalk element is a germ by module-stalk. -/
theorem fromSpecStalk_module_stalk (Y : Scheme.{u}) (y : Y) (G : Y.Modules) :
    ∃ e :
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace
        ((Y.fromSpecStalk y) (closedPoint (Y.presheaf.stalk y)))).obj G ≅
      (ModuleCat.restrictScalars
        ((Y.fromSpecStalk y).stalkMap (closedPoint (Y.presheaf.stalk y))).hom).obj
        ((RingedSpace.moduleStalkFunctor (Spec (Y.presheaf.stalk y)).toRingedSpace
          (closedPoint (Y.presheaf.stalk y))).obj
            ((Modules.tensorPullback (Y.fromSpecStalk y)).obj G)),
      ∀ (V : Y.Opens)
        (hy : (Y.fromSpecStalk y) (closedPoint (Y.presheaf.stalk y)) ∈ V)
        (s : G.val.obj (op V)),
        e.hom (TopCat.Presheaf.germ G.val.presheaf V
          ((Y.fromSpecStalk y) (closedPoint (Y.presheaf.stalk y))) hy s) =
        TopCat.Presheaf.germ ((Modules.tensorPullback (Y.fromSpecStalk y)).obj G).val.presheaf
          ((Y.fromSpecStalk y) ⁻¹ᵁ V) (closedPoint (Y.presheaf.stalk y)) hy
          (((Classical.choose (Modules.exists_tensorPullbackAdjunction
            (Y.fromSpecStalk y))).unit.app G).val.app (op V) s) := by
  let f := Y.fromSpecStalk y
  let x := closedPoint (Y.presheaf.stalk y)
  have hf : IsIso (f.stalkMap x) := (fromSpecStalk_local_properties Y y).2.2.2.1 x
  have hr : (ModuleCat.restrictScalars (f.stalkMap x).hom).IsEquivalence := by
    let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    change (ModuleCat.restrictScalars e.toRingHom).IsEquivalence
    infer_instance
  obtain ⟨e, he⟩ := Modules.exists_tensorPullback_stalk_iso f x
  let M := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).obj G
  let η := (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app M
  have : IsIso η := inferInstance
  refine ⟨asIso η ≪≫ (ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
    (e.app G).symm, ?_⟩
  intro V hy s
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app G)).1
  change (e.hom.app G) ((e.inv.app G) (η
    (TopCat.Presheaf.germ G.val.presheaf V (f x) hy s))) = _
  rw [← ModuleCat.comp_apply, e.inv_hom_id_app, ModuleCat.id_apply, he]
  rfl


end
end AlgebraicGeometry.Scheme
