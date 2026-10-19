/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups X2 and V3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Extensionality on tensors of wedges of locally lifted sections

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-tensor-lift-hom-ext).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_section_map {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (f : V ⟶ U) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheaf M n).val.map f.op (exteriorSheafSection M n U a) =
      exteriorSheafSection M n V (fun i ↦ M.val.map f.op (a i)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit.app (exteriorSheafPresheaf M n)
  have hn := PresheafOfModules.naturality_apply η f.op
    (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)
  have hr := (Classical.choose_spec
    (exteriorSheafRestriction_existsUnique M n f.op)).1 a
  exact hn.symm.trans (congrArg (η.app (op V)) hr)

private theorem exterior_section_induction {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (P : ∀ U : X.Opens, (exteriorSheaf M n).val.obj (op U) → Prop)
    (hzero : ∀ U, P U 0)
    (hadd : ∀ U x y, P U x → P U y → P U (x + y))
    (hsmul : ∀ U (c : X.presheaf.obj (op U)) x, P U x → P U (c • x))
    (hwedge : ∀ U a, P U (exteriorSheafSection M n U a))
    (hlocal : ∀ U x (S : Sieve U), S ∈ Opens.grothendieckTopology X U →
      (∀ (V : X.Opens) (f : V ⟶ U), S f →
        P V ((exteriorSheaf M n).val.map f.op x)) → P U x) :
    ∀ U x, P U x := by
  intro U x
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit.app (exteriorSheafPresheaf M n)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  apply hlocal U x (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map η) x)
    (Presheaf.imageSieve_mem _ _ _)
  intro V f hf
  obtain ⟨z, hz⟩ := hf
  change η.app (op V) z = (exteriorSheaf M n).val.map f.op x at hz
  rw [← hz]
  have hzspan : z ∈ Submodule.span (X.presheaf.obj (op V))
      (Set.range (exteriorPower.ιMulti (X.presheaf.obj (op V)) n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  clear hz
  induction hzspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact hwedge V a
  | zero => rw [map_zero]; exact hzero V
  | add x y _ _ hx hy => rw [map_add]; exact hadd V _ _ hx hy
  | smul c x _ hx =>
    rw [(η.app (op V)).hom.map_smul]
    exact hsmul V c _ hx

private theorem tensor_section_ext {X : Scheme.{v}} {M N D : X.Modules}
    (φ ψ : M ⊗ N ⟶ D)
    (h : ∀ U (x : M.val.obj (op U)) (y : N.val.obj (op U)),
      φ.val.app (op U) (tmulSection x y) = ψ.val.app (op U) (tmulSection x y)) :
    φ = ψ := by
  let e := SheafOfModules.tensorObjIsoSheafification M N
  apply (cancel_epi e.inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).homEquiv _ D).injective
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => exact h U.unop x y
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_section_map {X : Scheme.{v}} {M N : X.Modules}
    {U V : X.Opens} (f : V ⟶ U) (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (M ⊗ N).presheaf.map f.op (tmulSection x y) =
      tmulSection (M.val.map f.op x) (N.val.map f.op y) := by
  have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have hm := tmulSection_map (M := M) (N := N) (leOfHom f) x y
  rw [hf] at hm
  exact hm

set_option backward.isDefEq.respectTransparency false in
private theorem finite_local_lifts {X : Scheme.{v}} {B C : X.Modules}
    (g : B ⟶ C) [Epi g] (s : ℕ) (U : X.Opens)
    (c : Fin s → C.val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ b : Fin s → B.val.obj (op V), ∀ i,
        g.val.app (op V) (b i) = C.val.map (homOfLE hV).op (c i) := by
  classical
  let T := SheafOfModules.toSheaf.{v} X.ringCatSheaf
  have : Epi (T.map g) := inferInstance
  have hl := (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map g.val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (T.map g)).mpr inferInstance)
  choose V hV hb hxV using fun i : Fin s ↦ hl U (c i) x hx
  choose b hb using hb
  let W : X.Opens := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : Fin s) : W ≤ V i := inf_le_right.trans (iInf_le _ i)
  refine ⟨W, hWU, ?_, fun i ↦ B.val.map (homOfLE (hWV i)).op (b i), ?_⟩
  · exact ⟨hx, by
      change x ∈ ((⨅ i, V i : X.Opens) : Set X)
      rw [TopologicalSpace.Opens.coe_iInf]
      exact Set.mem_iInter.mpr hxV⟩
  · intro i
    change g.app W (B.presheaf.map (homOfLE (hWV i)).op (b i)) = _
    rw [Hom.app_presheaf_map]
    change C.val.map (homOfLE (hWV i)).op (g.val.app (op (V i)) (b i)) = _
    have hb' : g.val.app (op (V i)) (b i) =
        C.val.map (homOfLE (hV i)).op (c i) := hb i
    rw [hb', ← PresheafOfModules.map_comp_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of a tensor of exterior powers are determined on wedges in the first
factor and on wedges of images of sections under an epimorphism in the second factor.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph: pure wedges
and their tensors generate locally (blueprint: lem-sc-exterior-tensor-lift-hom-ext).

Proof: An epimorphism of sheaves of modules is locally surjective. Given a finite
family of sections of `C`, lift each section under `g` on a covering and take a common
refinement of the finitely many coverings. The displayed hypothesis and naturality
then imply equality on the tensor of any two pure wedges, by separatedness of `D`.
The case `s = 0` requires no lifts. Pure wedges span sectionwise exterior powers.
The sheafification maps are locally surjective, so sections of `exteriorSheaf A r`
and `exteriorSheaf C s` are locally finite linear combinations of pure wedges.
The tensor sheafification map is also locally surjective, so every section of their
tensor product is locally a finite sum of elementary tensors. Bilinearity and
linearity extend the equality to these sums, and separatedness glues it. Finally
extensionality of sheaf morphisms gives `φ = ψ`. This uses neither finite local
freeness, nor a rank relation, nor injectivity of any map. -/
theorem exteriorTensor_lift_hom_ext {X : Scheme.{v}} {A B C D : X.Modules}
    (g : B ⟶ C) [Epi g] (r s : ℕ)
    (φ ψ : exteriorSheaf A r ⊗ exteriorSheaf C s ⟶ D)
    (h : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)),
      φ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)))) =
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))))) :
    φ = ψ := by
  have hpure (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → C.val.obj (op U)) :
      φ.val.app (op U) (tmulSection (exteriorSheafSection A r U a)
        (exteriorSheafSection C s U c)) =
      ψ.val.app (op U) (tmulSection (exteriorSheafSection A r U a)
        (exteriorSheafSection C s U c)) := by
    apply D.isSheaf.section_ext
    intro x hx
    obtain ⟨V, hV, hxV, b, hb⟩ := finite_local_lifts g s U c x hx
    refine ⟨V, hV, hxV, ?_⟩
    change D.presheaf.map (homOfLE hV).op (φ.app U _) =
      D.presheaf.map (homOfLE hV).op (ψ.app U _)
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map,
        tensor_section_map (M := exteriorSheaf A r) (N := exteriorSheaf C s)
          (homOfLE hV)]
    rw [exterior_section_map A r (homOfLE hV) a,
      exterior_section_map C s (homOfLE hV) c]
    rw [← funext hb]
    exact h V (fun i ↦ A.val.map (homOfLE hV).op (a i)) b
  have hsecond := exterior_section_induction C s
    (fun U y ↦ ∀ a : Fin r → A.val.obj (op U),
      φ.val.app (op U) (tmulSection (exteriorSheafSection A r U a) y) =
        ψ.val.app (op U) (tmulSection (exteriorSheafSection A r U a) y))
    (by intro U a; simp only [tmulSection_zero, map_zero])
    (by
      intro U x y hx hy a
      rw [tmulSection_add (M := exteriorSheaf A r) (N := exteriorSheaf C s),
        map_add, map_add, hx a, hy a])
    (by
      intro U c x hx a
      rw [tmulSection_smul, (φ.val.app (op U)).hom.map_smul,
        (ψ.val.app (op U)).hom.map_smul, hx a])
    (by intro U c a; exact hpure U a c)
    (by
      intro U y S hS hl a
      apply (D.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
      intro V f hf
      change D.presheaf.map f.op (φ.app U _) = D.presheaf.map f.op (ψ.app U _)
      rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map,
        tensor_section_map (M := exteriorSheaf A r) (N := exteriorSheaf C s)
          f (exteriorSheafSection A r U a) y]
      rw [exterior_section_map A r f a]
      exact hl V f hf (fun i ↦ A.val.map f.op (a i)))
  apply tensor_section_ext
  apply exterior_section_induction A r
    (fun U x ↦ ∀ y : (exteriorSheaf C s).val.obj (op U),
      φ.val.app (op U) (tmulSection x y) = ψ.val.app (op U) (tmulSection x y))
  · intro U y
    simp only [zero_tmulSection, map_zero]
  · intro U x y hx hy z
    rw [add_tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s),
      map_add, map_add, hx z, hy z]
  · intro U c x hx y
    rw [smul_tmulSection, (φ.val.app (op U)).hom.map_smul,
      (ψ.val.app (op U)).hom.map_smul, hx y]
  · intro U a y
    exact hsecond U y a
  · intro U x S hS hl y
    apply (D.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
    intro V f hf
    change D.presheaf.map f.op (φ.app U _) = D.presheaf.map f.op (ψ.app U _)
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map,
        tensor_section_map (M := exteriorSheaf A r) (N := exteriorSheaf C s) f x y]
    exact hl V f hf ((exteriorSheaf C s).val.map f.op y)

end AlgebraicGeometry.Scheme.Modules
