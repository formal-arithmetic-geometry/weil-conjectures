/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Conormal fibre sequence for a smooth closed subscheme

Source: Stacks Project, Morphisms, Tags 06AA and 02G1
(blueprint: lem-pur-conormal-sequence-smooth-immersion).

The two arrows are characterized on generators by their differential formulas. The conormal
fibre is written as `κ ⊗[R] I.Cotangent`: since `R → S` is surjective and `I` annihilates
`I.Cotangent`, this is canonically `κ ⊗[S] (I/I²)`. Tensor factors are in Mathlib's
extension-of-scalars order.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The conormal fibre at a point of a closed immersion, using the actual stalk kernel.
Source: Stacks Project, Tag 06AA; the quotient is Mathlib's `Ideal.Cotangent`.
The `R`-balanced tensor equals the `S`-balanced tensor because `S = R/I`.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def conormalStalkFibre {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    (RingHom.ker (i.stalkMap z).hom).Cotangent)

/-- The class of a stalk-kernel element, tensored with one in the residue field.
Source: Stacks Project, Tag 06AA, first arrow of the conormal sequence.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def conormalStalkFibreClass {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z)
    (a : RingHom.ker (i.stalkMap z).hom) : conormalStalkFibre i z :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  1 ⊗ₜ[X.presheaf.stalk (i z)] (RingHom.ker (i.stalkMap z).hom).toCotangent a

/-- The fibre of the existing relative differential sheaf at `i z`, extended to `κ(z)`.
Source: Stacks Project, Tags 01UM and 06AA; stalks use the canonical module structure.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibre {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) : ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i z)).obj f.relativeDifferentials))

/-- The germ of the differential of a section, tensored with one in the residue field.
Source: Stacks Project, Tags 01UM and 06AA; the derivation is the existing universal derivation.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibreGerm {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) (U : X.Opens) (hz : i z ∈ U)
    (a : Γ(X, U)) : relativeDifferentialsStalkFibre f i z :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  1 ⊗ₜ[X.presheaf.stalk (i z)]
    (TopCat.Presheaf.germ f.relativeDifferentials.val.presheaf U (i z) hz
      (f.relativeDifferentialsDerivation.d (X := op U) a))

section Proof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v w t

open TensorProduct CategoryTheory.Limits TopologicalSpace

-- Take the stalk of the additive sheaf derivation, preserving its germ formula.
private noncomputable def stalkDerivationAdd {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.presheaf.stalk x →+
      f.relativeDifferentials.presheaf.stalk x :=
  let d : X.presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      f.relativeDifferentials.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom f.relativeDifferentialsDerivation.d
      naturality := fun U V g ↦ by
        ext a
        exact f.relativeDifferentialsDerivation.d_map g a }
  ((preservesColimitIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map d).hom

private theorem stalkDerivationAdd_germ {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkDerivationAdd f x (X.presheaf.germ U x hx a) =
      f.relativeDifferentials.presheaf.germ U x hx (f.relativeDifferentialsDerivation.d a) := by
  unfold stalkDerivationAdd
  change (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
      (X.presheaf.germ U x hx) ≫
    (preservesColimitIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).hom ≫ _) a = _
  rw [← Category.assoc]
  erw [ι_preservesColimitIso_hom]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (G := f.relativeDifferentials.presheaf) U x hx _ a

private theorem stalkDerivationAdd_mul {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a b : X.presheaf.stalk x) :
    stalkDerivationAdd f x (a * b) =
      a • stalkDerivationAdd f x b + b • stalkDerivationAdd f x a := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, b, rfl⟩ := X.presheaf.exists_germ_eq b
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
    ← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx b,
    ← map_mul, stalkDerivationAdd_germ, f.relativeDifferentialsDerivation.d_mul, map_add,
    stalkDerivationAdd_germ, stalkDerivationAdd_germ]
  exact congrArg₂ (· + ·)
    (PresheafOfModules.germ_smul (R := X.presheaf) f.relativeDifferentials.val x _ hx _ _)
    (PresheafOfModules.germ_smul (R := X.presheaf) f.relativeDifferentials.val x _ hx _ _)

private theorem stalkDerivationAdd_stalkMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : S.presheaf.stalk (f x)) : stalkDerivationAdd f x (f.stalkMap x a) = 0 := by
  obtain ⟨U, hx, a, rfl⟩ := S.presheaf.exists_germ_eq a
  rw [← ConcreteCategory.comp_apply, f.germ_stalkMap, ConcreteCategory.comp_apply,
    stalkDerivationAdd_germ]
  exact (congrArg (f.relativeDifferentials.presheaf.germ _ x hx)
    (f.relativeDifferentialsDerivation.d_app_app U a)).trans (map_zero _)

private noncomputable def fieldStalkMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

private theorem fieldStalkMap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : fieldStalkMap f x =
      (f.stalkMap x).hom.comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫
          (Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom) := by
  unfold fieldStalkMap
  rw [← CommRingCat.hom_comp, Category.assoc, f.germ_stalkMap]
  rfl

private noncomputable def fieldStalkDerivation {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI := (fieldStalkMap f x).toAlgebra
    letI := Module.compHom (f.relativeDifferentials.presheaf.stalk x) (fieldStalkMap f x)
    Derivation k (X.presheaf.stalk x) (f.relativeDifferentials.presheaf.stalk x) := by
  letI := (fieldStalkMap f x).toAlgebra
  letI := Module.compHom (f.relativeDifferentials.presheaf.stalk x) (fieldStalkMap f x)
  refine { (stalkDerivationAdd f x) with
    map_smul' := ?_
    map_one_eq_zero' := ?_
    leibniz' := stalkDerivationAdd_mul f x }
  · intro a b
    change stalkDerivationAdd f x (fieldStalkMap f x a * b) = _
    rw [stalkDerivationAdd_mul, fieldStalkMap_eq, RingHom.comp_apply,
      stalkDerivationAdd_stalkMap, smul_zero, add_zero]
    rfl
  · change stalkDerivationAdd f x 1 = 0
    exact (congrArg (stalkDerivationAdd f x) (map_one (f.stalkMap x).hom).symm).trans
      (stalkDerivationAdd_stalkMap f x 1)

-- A derivation of the stalk gives a sheaf derivation into a skyscraper module.
private noncomputable def fieldStalkSheafDerivation {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (N : Type u) [AddCommGroup N] [Module (X.presheaf.stalk x) N]
    (D : letI := (fieldStalkMap f x).toAlgebra
      letI := Module.compHom N (fieldStalkMap f x)
      Derivation k (X.presheaf.stalk x) N) :
    (Scheme.Modules.skyscraper x N).val.Derivation' f.pullbackPresheafToPresheaf := by
  letI := (fieldStalkMap f x).toAlgebra
  letI := Module.compHom N (fieldStalkMap f x)
  apply f.derivationMk
    (fun {U} ↦ {
      toFun := fun a hx ↦ D (X.presheaf.germ U.unop x hx.down a)
      map_zero' := by
        apply Scheme.Modules.SkyscraperSections.ext
        intro hx
        change D (X.presheaf.germ _ x hx 0) = 0
        rw [map_zero, map_zero]
      map_add' := by
        intro a b
        apply Scheme.Modules.SkyscraperSections.ext
        intro hx
        change D (X.presheaf.germ _ x hx (a + b)) =
          D (X.presheaf.germ _ x hx a) + D (X.presheaf.germ _ x hx b)
        rw [map_add, map_add] })
  · intro U a b
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D (X.presheaf.germ U.unop x hx (a * b)) = _
    exact (congrArg D (map_mul (X.presheaf.germ U.unop x hx).hom a b)).trans
      (D.leibniz _ _)
  · intro U V g a
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D (X.presheaf.germ V.unop x hx (X.presheaf.map g a)) = _
    exact congrArg D (X.presheaf.germ_res_apply' g x hx a)
  · intro V a
    apply Scheme.Modules.SkyscraperSections.ext
    intro hx
    change D (X.presheaf.germ (f ⁻¹ᵁ V) x hx (f.app V a)) = 0
    have hV : V = ⊤ := by
      apply top_unique
      intro y _
      have he : y = f x := Subsingleton.elim _ _
      exact he ▸ hx
    subst V
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of k)).inv).2 a
    change D (fieldStalkMap f x a) = 0
    exact D.map_algebraMap a

private theorem stalkLinearMap_ext_d {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) {N : Type u} [AddCommGroup N]
    [Module (X.presheaf.stalk x) N]
    (l₁ l₂ : f.relativeDifferentials.presheaf.stalk x →ₗ[X.presheaf.stalk x] N)
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)),
      l₁ (f.relativeDifferentials.presheaf.germ U x hx
        (f.relativeDifferentialsDerivation.d a)) =
      l₂ (f.relativeDifferentials.presheaf.germ U x hx
        (f.relativeDifferentialsDerivation.d a))) : l₁ = l₂ := by
  apply (Scheme.Modules.skyscraperHomEquiv x N f.relativeDifferentials).injective
  apply (f.relativeDifferentialsHomEquiv _).injective
  ext U a
  apply Scheme.Modules.SkyscraperSections.ext
  intro hx
  exact h U.unop hx a

private noncomputable def fieldDifferentialsStalkToKaehler {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI := (fieldStalkMap f x).toAlgebra
    f.relativeDifferentials.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      KaehlerDifferential k (X.presheaf.stalk x) := by
  letI := (fieldStalkMap f x).toAlgebra
  exact (Scheme.Modules.skyscraperHomEquiv x _ _).symm
    ((f.relativeDifferentialsHomEquiv _).symm
      (fieldStalkSheafDerivation f x _ (KaehlerDifferential.D k (X.presheaf.stalk x))))

private theorem fieldDifferentialsStalkToKaehler_germ {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) (U : X.Opens)
    (hx : x ∈ U) (a : Γ(X, U)) :
    let := (fieldStalkMap f x).toAlgebra
    fieldDifferentialsStalkToKaehler f x
      (f.relativeDifferentials.presheaf.germ U x hx (f.relativeDifferentialsDerivation.d a)) =
      KaehlerDifferential.D k (X.presheaf.stalk x) (X.presheaf.germ U x hx a) := by
  let := (fieldStalkMap f x).toAlgebra
  dsimp only [fieldDifferentialsStalkToKaehler, Scheme.Modules.skyscraperHomEquiv,
    Equiv.coe_fn_symm_mk, LinearMap.comp_apply]
  rw [Scheme.Modules.Hom.stalkLinearMap_germ, Scheme.Modules.skyscraperStalkEval_germ]
  erw [relativeDifferentialsHomEquiv_symm_app_d]
  rfl

private theorem fieldDifferentialsStalkToKaehler_bijective {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    Function.Bijective (fieldDifferentialsStalkToKaehler f x) := by
  let := (fieldStalkMap f x).toAlgebra
  let := Module.compHom (f.relativeDifferentials.presheaf.stalk x) (fieldStalkMap f x)
  have : IsScalarTower k (X.presheaf.stalk x)
      (f.relativeDifferentials.presheaf.stalk x) :=
    ⟨fun a b m ↦ mul_smul (fieldStalkMap f x a) b m⟩
  let l := fieldDifferentialsStalkToKaehler f x
  let r := (fieldStalkDerivation f x).liftKaehlerDifferential
  have hrl : r.comp l = LinearMap.id := by
    apply stalkLinearMap_ext_d f x
    intro U hx a
    change r (l _) = _
    rw [fieldDifferentialsStalkToKaehler_germ, Derivation.liftKaehlerDifferential_comp_D]
    exact stalkDerivationAdd_germ f x U hx a
  have hlr : l.comp r = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq a
    change l (r (KaehlerDifferential.D k (X.presheaf.stalk x) _)) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    change l (stalkDerivationAdd f x _) = _
    rw [stalkDerivationAdd_germ, fieldDifferentialsStalkToKaehler_germ]
    rfl
  exact ⟨Function.LeftInverse.injective (g := r) (fun a ↦ LinearMap.congr_fun hrl a),
    Function.RightInverse.surjective (g := r) (fun a ↦ LinearMap.congr_fun hlr a)⟩

private theorem fieldStalkMap_isOver {k : Type u} [Field k] {X Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] (z : Z) :
    fieldStalkMap (Z ↘ Spec (.of k)) z =
      (i.stalkMap z).hom.comp (fieldStalkMap (X ↘ Spec (.of k)) (i z)) := by
  have hi := (Hom.isOver_iff (S := Spec (.of k)) (f := i)).mp
    (inferInstanceAs (i.IsOver (Spec (.of k))))
  unfold fieldStalkMap
  rw [← CommRingCat.hom_comp, Category.assoc, Category.assoc, i.germ_stalkMap]
  have htop : (Z ↘ Spec (.of k)).appTop =
      (X ↘ Spec (.of k)).appTop ≫ i.appTop := by
    rw [← comp_appTop, hi]
  change (((Scheme.ΓSpecIso (.of k)).inv) ≫ (Z ↘ Spec (.of k)).appTop ≫
      Z.presheaf.germ ⊤ z trivial).hom =
    (((Scheme.ΓSpecIso (.of k)).inv) ≫ (X ↘ Spec (.of k)).appTop ≫
      i.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom
  rw [htop, Category.assoc]

private theorem fieldStalkMap_formallySmooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    let := (fieldStalkMap f x).toAlgebra
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  let := (fieldStalkMap f x).toAlgebra
  apply RingHom.formallySmooth_algebraMap.mp
  change (fieldStalkMap f x).FormallySmooth
  rw [fieldStalkMap_eq]
  apply RingHom.FormallySmooth.comp
  · apply RingHom.FormallySmooth.of_bijective
    have hx : f x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hx]
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    simpa only [Iso.inv_hom_id_assoc] using
      ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of k)).inv
  · apply f.mem_smoothLocus.mp
    rw [f.smoothLocus_eq_top]
    trivial

private noncomputable def fieldDifferentialsStalkEquiv {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI := (fieldStalkMap f x).toAlgebra
    f.relativeDifferentials.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      KaehlerDifferential k (X.presheaf.stalk x) :=
  LinearEquiv.ofBijective _ (fieldDifferentialsStalkToKaehler_bijective f x)

private noncomputable def fieldDifferentialsFibreEquiv {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (z : Z) :
    letI := (fieldStalkMap f (i z)).toAlgebra
    letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
    relativeDifferentialsStalkFibre f i z ≃ₗ[Z.residueField z]
      Z.residueField z ⊗[X.presheaf.stalk (i z)]
        KaehlerDifferential k (X.presheaf.stalk (i z)) := by
  letI := (fieldStalkMap f (i z)).toAlgebra
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  exact (fieldDifferentialsStalkEquiv f (i z)).baseChange
    (X.presheaf.stalk (i z)) (Z.residueField z)

private theorem fieldDifferentialsFibreEquiv_germ {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (z : Z)
    (U : X.Opens) (hz : i z ∈ U) (a : Γ(X, U)) :
    let := (fieldStalkMap f (i z)).toAlgebra
    let := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
    fieldDifferentialsFibreEquiv f i z (relativeDifferentialsStalkFibreGerm f i z U hz a) =
      1 ⊗ₜ[X.presheaf.stalk (i z)]
        KaehlerDifferential.D k (X.presheaf.stalk (i z)) (X.presheaf.germ U (i z) hz a) := by
  let := (fieldStalkMap f (i z)).toAlgebra
  let := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  change 1 ⊗ₜ[X.presheaf.stalk (i z)] (fieldDifferentialsStalkToKaehler f (i z) _) = _
  exact congrArg (fun m ↦ (1 : Z.residueField z) ⊗ₜ[X.presheaf.stalk (i z)] m)
    (fieldDifferentialsStalkToKaehler_germ f (i z) U hz a)

private theorem compatible_of_surjective
    (R S K N : Type*) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (hs : Function.Surjective (algebraMap R S)) : CompatibleSMul R S K N := by
  constructor
  intro s m n
  obtain ⟨r, rfl⟩ := hs s
  rw [algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]

-- A square-zero lift splits the algebraic conormal sequence before residue-field base change.
private theorem conormal_algebra_fibre
    (k : Type u) (R : Type v) (S : Type w) (K : Type t)
    [CommRing k] [CommRing R] [CommRing S] [CommRing K]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [Algebra.FormallySmooth k S]
    (hs : Function.Surjective (algebraMap R S)) :
    ∃ (α : K ⊗[R] (RingHom.ker (algebraMap R S)).Cotangent →ₗ[K]
          K ⊗[R] KaehlerDifferential k R)
      (β : K ⊗[R] KaehlerDifferential k R →ₗ[K] K ⊗[S] KaehlerDifferential k S),
      Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β ∧
      (∀ a, α (1 ⊗ₜ (RingHom.ker (algebraMap R S)).toCotangent a) =
        1 ⊗ₜ KaehlerDifferential.D k R a.1) ∧
      (∀ a, β (1 ⊗ₜ KaehlerDifferential.D k R a) =
        1 ⊗ₜ KaehlerDifferential.D k S (algebraMap R S a)) := by
  classical
  let P : Algebra.Extension.{v} k S :=
    { Ring := R
      σ := fun x ↦ (hs x).choose
      algebraMap_σ := fun x ↦ (hs x).choose_spec }
  let f := IsScalarTower.toAlgHom k R S
  have hq : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hs
  have hn : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    exact ⟨2, by rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]; rfl⟩
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k S) f.kerSquareLift hq hn
  have hσ : f.kerSquareLift.comp σ = AlgHom.id k S :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨l, hl⟩ :=
    (retractionKerCotangentToTensorEquivSection (R := k) hs).symm ⟨σ, hσ⟩
  let e := P.cotangentEquivCotangentKer
  let l' : P.CotangentSpace →ₗ[S] P.Cotangent :=
    ((e.symm.toLinearMap.comp l).extendScalarsOfSurjective hs)
  have hl' : l'.comp P.cotangentComplex = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e.symm (l (KaehlerDifferential.kerCotangentToTensor k R S (e x))) = x
    rw [show l (KaehlerDifferential.kerCotangentToTensor k R S (e x)) = e x from
      LinearMap.congr_fun hl (e x)]
    exact e.symm_apply_apply x
  have hex := P.exact_cotangentComplex_toKaehler
  have hsurj := P.toKaehler_surjective
  let δ := P.cotangentComplex.baseChange K
  let ω := P.toKaehler.baseChange K
  have hδ : Function.Injective δ := by
    apply Function.LeftInverse.injective (g := l'.baseChange K)
    intro a
    change ((l'.baseChange K).comp (P.cotangentComplex.baseChange K)) a = a
    rw [← LinearMap.baseChange_comp, hl', LinearMap.baseChange_id]
    rfl
  have hω : Function.Surjective ω := LinearMap.lTensor_surjective K hsurj
  have heδω : Function.Exact δ ω := _root_.lTensor_exact K hex hsurj
  have : CompatibleSMul R S K P.Cotangent := compatible_of_surjective R S K _ hs
  let eN : K ⊗[R] (RingHom.ker (algebraMap R S)).Cotangent ≃ₗ[K]
      K ⊗[S] P.Cotangent :=
    (AlgebraTensorModule.congr (.refl K K) e.symm).trans
      (equivOfCompatibleSMul S R K K P.Cotangent)
  let eM : K ⊗[S] P.CotangentSpace ≃ₗ[K] K ⊗[R] KaehlerDifferential k R :=
    AlgebraTensorModule.cancelBaseChange R S K K (KaehlerDifferential k R)
  let α := eM.toLinearMap.comp (δ.comp eN.toLinearMap)
  let β := ω.comp eM.symm.toLinearMap
  refine ⟨α, β, eM.injective.comp (hδ.comp eN.injective), ?_,
    hω.comp eM.symm.surjective, ?_, ?_⟩
  · intro a
    change ω (eM.symm a) = 0 ↔ ∃ b, eM (δ (eN b)) = a
    rw [heδω]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨eN.symm b, by simp [hb]⟩
    · rintro ⟨b, hb⟩
      exact ⟨eN b, eM.injective (by simpa using hb)⟩
  · intro a
    change eM (δ (eN (1 ⊗ₜ[R] (RingHom.ker (algebraMap R S)).toCotangent a))) = _
    change eM (1 ⊗ₜ[S] P.cotangentComplex
      (e.symm ((RingHom.ker (algebraMap R S)).toCotangent a))) = _
    change eM (1 ⊗ₜ[S] (1 ⊗ₜ[R] KaehlerDifferential.D k R a.1)) = _
    exact (AlgebraTensorModule.cancelBaseChange_tmul (R := R) (A := S) (B := K)
      (M := K) (N := KaehlerDifferential k R) 1
      (KaehlerDifferential.D k R a.1) 1).trans (by rw [one_smul])
  · intro a
    change ω (eM.symm (1 ⊗ₜ[R] KaehlerDifferential.D k R a)) = _
    rw [AlgebraTensorModule.cancelBaseChange_symm_tmul]
    change 1 ⊗ₜ[S] KaehlerDifferential.mapBaseChange k R S
      (1 ⊗ₜ[R] KaehlerDifferential.D k R a) = _
    rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

-- Normalize the identity-morphism point in the type once, rather than in every tensor comparison.
private noncomputable def selfStalkResidueMap (Z : Scheme.{u}) (z : Z) :
    Z.presheaf.stalk z →+* Z.residueField z :=
  (stalkMap (𝟙 Z) z ≫ Z.residue z).hom

private noncomputable def fieldDifferentialsSelfFibreEquiv {k : Type u} [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (z : Z) :
    letI := (fieldStalkMap f z).toAlgebra
    letI : Algebra (Z.presheaf.stalk z) (Z.residueField z) :=
      (selfStalkResidueMap Z z).toAlgebra
    relativeDifferentialsStalkFibre f (𝟙 Z) z ≃ₗ[Z.residueField z]
      Z.residueField z ⊗[Z.presheaf.stalk z] KaehlerDifferential k (Z.presheaf.stalk z) :=
  fieldDifferentialsFibreEquiv f (𝟙 Z) z

private theorem fieldDifferentialsSelfFibreEquiv_germ {k : Type u} [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (z : Z) (U : Z.Opens)
    (hz : z ∈ U) (a : Γ(Z, U)) :
    let := (fieldStalkMap f z).toAlgebra
    let : Algebra (Z.presheaf.stalk z) (Z.residueField z) :=
      (selfStalkResidueMap Z z).toAlgebra
    fieldDifferentialsSelfFibreEquiv f z
        (relativeDifferentialsStalkFibreGerm f (𝟙 Z) z U hz a) =
      1 ⊗ₜ[Z.presheaf.stalk z]
        KaehlerDifferential.D k (Z.presheaf.stalk z) (Z.presheaf.germ U z hz a) :=
  fieldDifferentialsFibreEquiv_germ f (𝟙 Z) z U hz a

private theorem residue_stalkMap_comp {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    (i.stalkMap z ≫ Z.residue z).hom =
      (selfStalkResidueMap Z z).comp (i.stalkMap z).hom := by
  unfold selfStalkResidueMap
  have h : (stalkMap (𝟙 Z) z ≫ Z.residue z : Z.presheaf.stalk z ⟶ Z.residueField z) =
      Z.residue z :=
    (congrArg (fun g : Z.presheaf.stalk z ⟶ Z.presheaf.stalk z ↦ g ≫ Z.residue z)
      (stalkMap_id Z z)).trans (Category.id_comp _)
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The canonical conormal fibre sequence of a closed immersion with smooth source is short
exact. Both arrows are specified on generators: the first sends `[a] ⊗ 1` to `da ⊗ 1`,
and the second sends `da ⊗ 1` to `d(i(a)) ⊗ 1`.

Source: Stacks Project, Morphisms, Tag 06AA, with Tag 02G1 for passage to residue fields.
(blueprint: lem-pur-conormal-sequence-smooth-immersion).

Proof for stage 3, following the eight steps of the DAG node:
1. Choose an affine neighborhood `U = Spec A` of `i z`. The closed-immersion affine
   criterion (lem-weil-pbc-closed-immersion-affine-cover-criterion) identifies its preimage
   with `Spec B`, for a surjection `A → B = A/J`. Set `N = J/J²`,
   `M = B ⊗[A] Ω[A⁄k]`, and `P = Ω[B⁄k]` (def-weil-affine-spectrum,
   def-weil-pbc-kahler-differentials). The action of `B` on `N` is independent of lifts
   because changing a lift adds a product of two elements of `J`.
2. The square-zero kernel of `C = A/J² → B` defines an affine first-order thickening
   (def-sbc-first-order-thickening). Smoothness of `Z` over `k` lifts `Spec B → Z` to
   `Spec C → Z` (def-sbc-smooth-morphisms, Stacks Tag 02H0). Every prime of `C` contains
   the square-zero kernel, so this lift lands in the open `Spec B` of `Z`. Factoring
   through that open (def-weil-open-immersion) and the affine spectrum correspondence
   (def-weil-affine-spectrum) gives a `k`-algebra section `σ : B → C` of the quotient.
3. The quotient differential sequence gives `δ : N → M`, `[j] ↦ 1 ⊗ dj`, and a
   surjection `w : M → P`, `b ⊗ da ↦ b d(a mod J)`, with `ker w = im δ`
   (lem-weil-pbc-jacobi-zariski-differential-maps, Stacks Tag 00RU).
4. Define `D(a) = (a mod J²) - σ(a mod J)` in the square-zero kernel `N`. This vanishes
   on `k` and satisfies Leibniz because the kernel has square zero. Universality of
   differentials and extension of scalars give `τ : M → N`, `b ⊗ da ↦ b D(a)`
   (def-weil-pbc-kahler-differentials, def-weil-module-base-change, Tag 02HP).
   For `j ∈ J`, `D(j) = [j]`, hence `τ δ = id`.
5. For `p ∈ P`, choose a lift `m` under `w` and set `s(p) = m - δ(τ(m))`. Another lift
   differs by `δ(n)`, so `τ δ = id` proves independence and linearity. Then `w s = id`,
   `τ s = 0`, and `δ τ + s w = id`. Thus `M` is the direct sum of `N` and `P`.
6. Tensor these splitting identities with `κ(z)` over `B` (def-weil-module-base-change).
   They imply injectivity, surjectivity and middle exactness after base change: an
   element killed by the second arrow equals `δ τ` of itself. No flatness of `κ` is used.
7. The affine stalk and Spec-map formulas identify `R = Aₚ`, `S = B_q`, and the stalk
   map with the localized quotient (lem-weil-pbc-affine-open-stalk-localization,
   lem-weil-pbc-spec-map-stalk-localization). Quotient localization gives `I = JR`,
   `S = R/I`, and `I² = J²R` (lem-weil-pbc-localization-at-prime-of-quotient).
   Clearing denominators identifies the localization of `J/J²` with `I/I²`.
   Since denominators act invertibly on `κ`, balancing identifies its fibre with
   `κ ⊗[R] I.Cotangent` (def-weil-module-base-change), the first displayed module.
8. Affine agreement of the relative differential sheaf and localization of tilde stalks
   identify the other two fibres (def-sc-relative-differential-sheaf,
   lem-weil-pbc-spec-tilde-stalk-localization). For `f = j/t ∈ I`, Leibniz gives
   `d(j/t) = t⁻¹ dj - jt⁻² dt`; the second term vanishes in the fibre. Thus the first
   arrow is exactly `[f] ⊗ 1 ↦ df ⊗ 1`. The second sends `da` to `d(a mod J)` and
   obeys the same denominator rule, so it is induced by the local-ring map `R → S`.
   Cotangent classes and differential germs generate the respective fibres, so the two
   formulas in the statement determine the canonical arrows. No smoothness of `X` is used.
Source for these expansions: Stacks Tags 06AA, 00RU, 02HP and 06A8; Tag 02G1 also gives
an alternative passage to residue fields by local freeness of the final differential stalk. -/
theorem conormalStalkFibre_shortExact_of_smooth
    {k : Type u} [Field k] {X Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    [Smooth (Z ↘ Spec (.of k))] (z : Z) :
    ∃ (α : conormalStalkFibre i z →ₗ[Z.residueField z]
        relativeDifferentialsStalkFibre (X ↘ Spec (.of k)) i z)
      (β : relativeDifferentialsStalkFibre (X ↘ Spec (.of k)) i z →ₗ[Z.residueField z]
        relativeDifferentialsStalkFibre (Z ↘ Spec (.of k)) (𝟙 Z) z),
      Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β ∧
      (∀ (U : X.Opens) (hz : i z ∈ U) (a : Γ(X, U))
        (ha : (i.stalkMap z) (X.presheaf.germ U (i z) hz a) = 0),
        α (conormalStalkFibreClass i z ⟨X.presheaf.germ U (i z) hz a, ha⟩) =
          relativeDifferentialsStalkFibreGerm (X ↘ Spec (.of k)) i z U hz a) ∧
      (∀ (U : X.Opens) (hz : i z ∈ U) (a : Γ(X, U)),
        β (relativeDifferentialsStalkFibreGerm (X ↘ Spec (.of k)) i z U hz a) =
          relativeDifferentialsStalkFibreGerm (Z ↘ Spec (.of k)) (𝟙 Z) z
            (i ⁻¹ᵁ U) hz (i.app U a)) := by
  -- Apply the split conormal sequence to the actual stalk rings.
  classical
  let fX := X ↘ Spec (.of k)
  let fZ := Z ↘ Spec (.of k)
  let R := X.presheaf.stalk (i z)
  let S := Z.presheaf.stalk z
  let K := Z.residueField z
  let : Algebra k R := (fieldStalkMap fX (i z)).toAlgebra
  let : Algebra k S := (fieldStalkMap fZ z).toAlgebra
  let : Algebra R S := (i.stalkMap z).hom.toAlgebra
  have : IsScalarTower k R S :=
    IsScalarTower.of_algebraMap_eq' (fieldStalkMap_isOver i z)
  let : Algebra S K := (selfStalkResidueMap Z z).toAlgebra
  let : Algebra R K := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  have : IsScalarTower R S K :=
    IsScalarTower.of_algebraMap_eq' (residue_stalkMap_comp i z)
  have : Algebra.FormallySmooth k S := fieldStalkMap_formallySmooth fZ z
  obtain ⟨α₀, β₀, hα₀, he₀, hβ₀, hαg, hβg⟩ :=
    conormal_algebra_fibre k R S K (i.stalkMap_surjective z)
  let eX := fieldDifferentialsFibreEquiv fX i z
  let eZ := fieldDifferentialsSelfFibreEquiv fZ z
  let α := eX.symm.toLinearMap.comp α₀
  let β := eZ.symm.toLinearMap.comp (β₀.comp eX.toLinearMap)
  refine ⟨α, β, eX.symm.injective.comp hα₀, ?_,
    eZ.symm.surjective.comp (hβ₀.comp eX.surjective), ?_, ?_⟩
  · intro a
    change eZ.symm (β₀ (eX a)) = 0 ↔ ∃ b, eX.symm (α₀ b) = a
    rw [LinearEquiv.map_eq_zero_iff, he₀]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, by rw [hb, eX.symm_apply_apply]⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, by rw [← hb, eX.apply_symm_apply]⟩
  · intro U hz a ha
    apply eX.injective
    change eX (eX.symm (α₀ _)) = _
    rw [eX.apply_symm_apply, fieldDifferentialsFibreEquiv_germ fX i z U hz a]
    exact hαg ⟨X.presheaf.germ U (i z) hz a, ha⟩
  · intro U hz a
    apply eZ.injective
    change eZ (eZ.symm (β₀ (eX _))) = _
    rw [eZ.apply_symm_apply, fieldDifferentialsFibreEquiv_germ fX i z U hz a]
    erw [fieldDifferentialsSelfFibreEquiv_germ fZ z (i ⁻¹ᵁ U) hz (i.app U a),
      hβg (X.presheaf.germ U (i z) hz a)]
    congr 2
    exact i.germ_stalkMap_apply U z hz a

end Proof

end AlgebraicGeometry.Scheme.Hom
