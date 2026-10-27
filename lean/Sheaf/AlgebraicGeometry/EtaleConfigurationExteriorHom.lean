/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Exterior free étale sheaves and distinct configurations

Source: Stacks Project, spaces-cohomology.tex, Tag 0726, lemma-compute
(blueprint: lem-sfb-etale-configuration-exterior-hom).

The finite product and its clopen distinct locus are specified by their universal
property and equality-locus complement. All maps in the Hom identification are
characterized by evaluation on the tautological wedge.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AddCommGrpCat

/-- Sectionwise integral exterior power, using the canonical integer module structure.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def integralExteriorPower (n : ℕ) : AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} where
  obj M := AddCommGrpCat.of (⋀[ℤ]^n M)
  map f := AddCommGrpCat.ofHom
    (_root_.exteriorPower.map n f.hom.toIntLinearMap).toAddMonoidHom
  map_id M := by
    apply AddCommGrpCat.hom_ext
    exact congrArg LinearMap.toAddMonoidHom (_root_.exteriorPower.map_id (R := ℤ) (n := n))
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact congrArg LinearMap.toAddMonoidHom
      (_root_.exteriorPower.map_comp f.hom.toIntLinearMap g.hom.toIntLinearMap)

end AddCommGrpCat

namespace AlgebraicGeometry.AlgebraicSpace

/-- Free abelian sheaf of an étale object, with coefficient size containing the site.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationFreeSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) : Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  (presheafToSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)

/-- The augmentation sending every represented generator to one in the constant integers.
Source: Stacks Tag 0726, the augmented exterior complex preceding lemma-compute
(blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationAugmentation {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) : configurationFreeSheaf X U ⟶
    (presheafToSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
      ((Functor.const X.EtaleSiteᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (presheafToSheaf X.etaleTopology AddCommGrpCat.{u + 1}).map
    { app := fun _ ↦ AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift (fun _ ↦ (1 : ULift.{u + 1} ℤ)))
      naturality := by
        intro V W f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp }

/-- Sheafification of sectionwise exterior powers over the constant integer sheaf.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationExteriorSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (n : ℕ) : Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  (presheafToSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
    ((configurationFreeSheaf X U).obj ⋙ AddCommGrpCat.integralExteriorPower n)

/-- The free sheaf generator attached to a lift to the covering scheme.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationGenerator {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U V : X.EtaleSite) (a : V ⟶ U) : (configurationFreeSheaf X U).obj.obj (op V) :=
  (toSheafify X.etaleTopology
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (op V)
      (FreeAbelianGroup.of (ULift.up a))

/-- The tautological wedge, followed by the exterior presheaf's sheafification unit.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationWedge {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U V : X.EtaleSite) (n : ℕ) (a : Fin n → (V ⟶ U)) :
    (configurationExteriorSheaf X U n).obj.obj (op V) :=
  (toSheafify X.etaleTopology
    ((configurationFreeSheaf X U).obj ⋙ AddCommGrpCat.integralExteriorPower n)).app (op V)
      (_root_.exteriorPower.ιMulti ℤ n (fun i ↦ configurationGenerator X U V (a i)))

/-- The complement of all scheme-theoretic pairwise equality loci.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
noncomputable def configurationDistinctSet {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U T : X.EtaleSite) (n : ℕ) (pr : Fin n → (T ⟶ U)) :
    Set ((X.etaleForget).obj T) :=
  {x | ∀ i j : Fin n, i ≠ j →
    x ∉ Set.range (equalizer.ι ((X.etaleForget).map (pr i))
      ((X.etaleForget).map (pr j))).base}

/-- Sections transformed by the sign of every coordinate permutation.
Source: Stacks Tag 0726 (blueprint: lem-sfb-etale-configuration-exterior-hom). -/
def configurationAntiInvariant {S : Scheme.{u}} (X : AlgebraicSpace S)
    (W : X.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W)
    (F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) :
    AddSubgroup (F.obj.obj (op W)) :=
  ⨅ σ : Equiv.Perm (Fin n),
    (F.obj.map (ρ σ).hom.op).hom.eqLocus
      (DistribSMul.toAddMonoidHom _ ((Equiv.Perm.sign σ : ℤˣ) : ℤ))

/-- The distinct locus is clopen and étale, coordinate permutations act freely, and
wedge evaluation gives the natural additive Hom identification.
Source: Stacks Project, Tag 0726, lemma-compute
(blueprint: lem-sfb-etale-configuration-exterior-hom).
Proof: form the nonempty finite fibre product by representable étale scheme base
change [lem-trf-space-fibre-products-etale-covers] and étale permanence
[lem-trf-space-chartwise-etale-permanence]. The diagonal is clopen by
[lem-sfb-space-separated-etale-diagonal-complement]. Pull it back for every pair
using [lem-weil-pbc-open-immersion-base-change] and
[lem-weil-pbc-closed-immersion-base-change]. Its complement is clopen and étale
by [lem-a1-etale-open-restriction]. Permutations preserve this complement; a
fixed tuple for a moved coordinate lies in an excluded equality locus.
Apply [lem-sfb-alternating-sheafification-universal-property] over the constant
integers. Evaluate an alternating family on tautological generators. Conversely,
pull back an anti-invariant section on the distinct part of each tuple and extend
by zero on its clopen complement, using [def-weil-pbc-sites-and-cohomology].
Expand over the free abelian basis and extend multilinearly. Equal entries yield
zero: repeated basis labels vanish, and the other summands pair with their
transposes and cancel, including for 2-torsion coefficients. The universal
property produces a unique map from the exterior sheaf. The constructions are
inverse by restriction to the distinct part and the equality-locus cover of its
complement, and preserve addition. Evaluation commutes with every coefficient
morphism, hence with every differential in a complex. Only integral sums and
restriction and gluing are used; no factorial is inverted. -/
theorem etale_configuration_exterior_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (hsurj : IsSurjective U.obj.hom)
    (hsep : IsSeparatedPresheafMap U.obj.hom) (p : ℕ) :
    ∃ (T : X.EtaleSite) (pr : Fin (p + 1) → (T ⟶ U)),
      Nonempty (IsLimit (Fan.mk T pr)) ∧
      ∃ (W : X.EtaleSite) (j : W ⟶ T)
        (ρ : Equiv.Perm (Fin (p + 1)) →* Aut W),
        IsOpenImmersion ((X.etaleForget).map j) ∧
        IsClosedImmersion ((X.etaleForget).map j) ∧
        Set.range ((X.etaleForget).map j).base =
          configurationDistinctSet X U T (p + 1) pr ∧
        (∀ (σ : Equiv.Perm (Fin (p + 1))) (i : Fin (p + 1)),
          (ρ σ).hom ≫ j ≫ pr i = j ≫ pr (σ.symm i)) ∧
        (∀ (V : Scheme.{u}) (a : V ⟶ (X.etaleForget).obj W)
          (σ : Equiv.Perm (Fin (p + 1))), Nonempty V →
            a ≫ (X.etaleForget).map (ρ σ).hom = a → σ = 1) ∧
        ∃ e : ∀ F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1},
          (configurationExteriorSheaf X U (p + 1) ⟶ F) ≃+
            configurationAntiInvariant X W (p + 1) ρ F,
          (∀ (F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1})
            (h : configurationExteriorSheaf X U (p + 1) ⟶ F),
            (e F h).val = h.hom.app (op W)
              (configurationWedge X U W (p + 1) (fun i ↦ j ≫ pr i))) ∧
          (∀ (F G : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G)
            (h : configurationExteriorSheaf X U (p + 1) ⟶ F),
            (e G (h ≫ φ)).val = φ.hom.app (op W) (e F h).val) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
