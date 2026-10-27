/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricHomogeneousSections
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore

/-! # Degreewise surjectivity of the symmetric algebra sheaf map

Source: Stacks Project, Modules, Tag 01CJ and Section 01CF
(blueprint: lem-trf-symmetric-sheaf-map-degreewise-surjective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.SymmetricAlgebraSheaf

private noncomputable def sectionSymMap {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E) (U : X.Opensᵒᵖ) : sections F U →ₐ[X.presheaf.obj U] sections E U :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι _ _).comp (u.val.app U).hom)

private theorem sectionSymMap_ι {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E) (U : X.Opensᵒᵖ) (x : F.val.obj U) :
    sectionSymMap u U (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (u.val.app U x) :=
  SymmetricAlgebra.lift_ι_apply _ x

private theorem sectionSymMap_mem {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E) (U : X.Opensᵒᵖ) (n : ℕ) (s : sections F U)
    (hs : s ∈ (SymmetricAlgebra.ι _ _).range ^ n) :
    sectionSymMap u U s ∈ (SymmetricAlgebra.ι _ _).range ^ n := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact Submodule.algebraMap_mem _
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, sectionSymMap_ι, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

private theorem restriction_mem_degree {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (n : ℕ) (s : sections F U)
    (hs : s ∈ (SymmetricAlgebra.ι _ _).range ^ n) :
    restriction F i s ∈ (SymmetricAlgebra.ι _ _).range ^ n := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [restriction_algebraMap]
    exact Submodule.algebraMap_mem _
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, restriction_ι, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

private theorem sectionMap_restriction {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : sections F U) :
    sectionMap F V (restriction F i s) =
      (algebra F).right.obj.map i (sectionMap F U s) := by
  exact congrArg (fun t ↦ t s)
    ((toSheafify (Opens.grothendieckTopology X) (presheaf F)).naturality i)

private theorem sectionMap_homogeneous {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (U : X.Opens) (s : sections F (op U))
    (hs : s ∈ (SymmetricAlgebra.ι _ _).range ^ n) :
    IsHomogeneousSection F n U (sectionMap F (op U) s) := by
  intro V h
  exact ⟨restriction F (homOfLE h).op s,
    restriction_mem_degree F _ n s hs, sectionMap_restriction F _ s⟩

private theorem map_sectionMap {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E) (a : algebra F ⟶ algebra E)
    (ha : ∀ (U : X.Opens) (x : F.val.obj (op U)),
      a.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
        (inclusion E).val.app (op U) (u.val.app (op U) x))
    (U : X.Opens) (s : sections F (op U)) :
    a.right.hom.app (op U) (sectionMap F (op U) s) =
      sectionMap E (op U) (sectionSymMap u (op U) s) := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact congrArg (fun t ↦ t.hom.app (op U) r) (Under.w a)
  | ι x =>
    rw [sectionSymMap_ι]
    exact ha U x
  | add s t hs ht => simp only [map_add, hs, ht]
  | mul s t hs ht => simp only [map_mul, hs, ht]

private theorem map_homogeneous {X : Scheme.{u}} {F E : X.Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (u : F ⟶ E)
    (a : algebra F ⟶ algebra E)
    (ha : ∀ (U : X.Opens) (x : F.val.obj (op U)),
      a.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
        (inclusion E).val.app (op U) (u.val.app (op U) x))
    (n : ℕ) (U : X.Opens) (s : (algebra F).right.obj.obj (op U))
    (hs : IsHomogeneousSection F n U s) :
    IsHomogeneousSection E n U (a.right.hom.app (op U) s) := by
  intro V h
  obtain ⟨t, ht, heq⟩ := hs V h
  refine ⟨sectionSymMap u (op V.1) t, sectionSymMap_mem u _ n t ht, ?_⟩
  rw [← map_sectionMap u a ha, heq]
  exact congrArg (fun t ↦ t s) (a.right.hom.naturality (homOfLE h).op)

private theorem sectionSymMap_restriction {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E) {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : sections F U) :
    sectionSymMap u V (restriction F i s) =
      restriction E i (sectionSymMap u U s) := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [restriction_algebraMap, AlgHom.commutes, AlgHom.commutes,
      restriction_algebraMap]
  | ι x =>
    rw [restriction_ι, sectionSymMap_ι, sectionSymMap_ι, restriction_ι]
    exact congrArg (SymmetricAlgebra.ι _ _) (PresheafOfModules.naturality_apply u.val i x)
  | add s t hs ht => simp only [map_add, hs, ht]
  | mul s t hs ht => simp only [map_mul, hs, ht]

private theorem restriction_restriction {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : sections F (op U)) :
    restriction F (homOfLE k).op (restriction F (homOfLE h).op s) =
      restriction F (homOfLE (k.trans h)).op s := by
  exact (congrArg (fun t ↦ t.hom s)
    ((presheaf F).map_comp (homOfLE h).op (homOfLE k).op)).symm

private theorem module_local_lift {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) u.val]
    (U : X.Opens) (s : E.val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
      ∃ t : F.val.obj (op V), u.val.app (op V) t = E.val.map (homOfLE h).op s := by
  have h := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map u.val) s
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := h x hx
  exact ⟨V, leOfHom i, hxV, t, ht⟩

private theorem section_local_lift {X : Scheme.{u}} {F E : X.Modules}
    (u : F ⟶ E)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) u.val]
    (U : X.Opens) (n : ℕ) (s : sections E (op U))
    (hs : s ∈ (SymmetricAlgebra.ι _ _).range ^ n) :
    ∀ (x : X), x ∈ U → ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
      ∃ t : sections F (op V), t ∈ (SymmetricAlgebra.ι _ _).range ^ n ∧
        sectionSymMap u (op V) t = restriction E (homOfLE h).op s := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    intro x hx
    refine ⟨U, le_rfl, hx, algebraMap _ _ r, Submodule.algebraMap_mem _, ?_⟩
    rw [AlgHom.commutes]
    exact (congrArg (fun t ↦ t.hom
      (algebraMap (X.presheaf.obj (op U)) (sections E (op U)) r))
      ((presheaf E).map_id (op U))).symm
  | add s t i hs ht ihs iht =>
    intro x hx
    obtain ⟨V, hV, hxV, b, hb, heqb⟩ := ihs x hx
    obtain ⟨W, hW, hxW, c, hc, heqc⟩ := iht x hx
    refine ⟨V ⊓ W, inf_le_left.trans hV, ⟨hxV, hxW⟩,
      restriction F (homOfLE inf_le_left).op b +
        restriction F (homOfLE inf_le_right).op c,
      add_mem (restriction_mem_degree F _ i b hb) (restriction_mem_degree F _ i c hc), ?_⟩
    simp only [map_add, sectionSymMap_restriction, heqb, heqc,
      restriction_restriction]
  | mem_mul m hm i s hs ih =>
    obtain ⟨m, rfl⟩ := hm
    intro x hx
    obtain ⟨V, hV, hxV, f, hf⟩ := module_local_lift u U m x hx
    obtain ⟨W, hW, hxW, b, hb, heqb⟩ := ih x hx
    let f' : F.val.obj (op (V ⊓ W)) :=
      F.val.map (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op f
    let b' := restriction F (homOfLE (show V ⊓ W ≤ W from inf_le_right)).op b
    refine ⟨V ⊓ W, inf_le_left.trans hV, ⟨hxV, hxW⟩,
      SymmetricAlgebra.ι _ _ f' * b', ?_, ?_⟩
    · rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _)
        (restriction_mem_degree F _ i b hb)
    · have hf' : u.val.app (op (V ⊓ W)) f' =
          E.val.map (homOfLE (inf_le_left.trans hV)).op m := by
        dsimp only [f']
        rw [PresheafOfModules.naturality_apply, hf]
        exact (E.val.map_comp_apply (homOfLE hV).op
          (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op m).symm
      dsimp only [b']
      rw [map_mul, sectionSymMap_ι, hf', sectionSymMap_restriction, heqb,
        restriction_restriction, map_mul, restriction_ι]

/-- A locally surjective map of quasi-coherent modules induces the unique symmetric
algebra sheaf map extending its degree-one map. It preserves degrees, acts identically
on scalars, and every homogeneous section locally lifts in the same degree.
Source: Stacks Project, Modules, Tag 01CJ and Section 01CF
(blueprint: lem-trf-symmetric-sheaf-map-degreewise-surjective).

Proof:
1. Apply lem-weil-pbc-quasi-coherent-symmetric-algebra to inclusion E composed with u.
   The universal property gives a unique algebra-sheaf map. On each open it takes a
   scalar times a product of n generators to the same scalar times the product of their
   images. In degree zero the empty product is one, giving the scalar identity.
2. On an affine open use the canonical affine comparison of that lemma and the grades
   of def-trf-canonical-symmetric-graded-algebra. By lem-weil-pbc-symmetric-algebra-graded
   the degree-n part is spanned by products of n generators. The generator formula
   preserves these spans. Test on affine subopens to obtain preservation on all opens;
   lem-weil-pbc-affine-opens-basis says these subopens form a basis.
3. For n positive, cover the domain of a homogeneous section by affine opens. The same
   comparison, grading and spanning lemma express each restriction as a finite sum of
   scalar multiples of products of n module sections; the sum may be empty.
4. At each point lift the finitely many module sections using local surjectivity of u.
   Intersect their finitely many lifting neighbourhoods and restrict every lift there.
   The corresponding finite sum of products is homogeneous of degree n, as can be
   checked on affine subopens. For an empty sum use zero on the original affine open.
5. The generator formula sends this section to the given restricted section. These
   neighbourhoods cover the domain and supply the requested lifts. For n zero the
   scalar identity gives a lift on the domain itself. An empty domain admits the empty
   covering, so it is included. -/
theorem exists_map_degreewise_locallySurjective {X : Scheme.{u}} (F E : X.Modules)
    [F.IsQuasicoherent] [E.IsQuasicoherent] (u : F ⟶ E)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      u.val] :
    ∃ a : algebra F ⟶ algebra E,
      (∀ (U : X.Opens) (x : F.val.obj (op U)),
        a.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
          (inclusion E).val.app (op U) (u.val.app (op U) x)) ∧
      (∀ b : algebra F ⟶ algebra E,
        (∀ (U : X.Opens) (x : F.val.obj (op U)),
          b.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
            (inclusion E).val.app (op U) (u.val.app (op U) x)) → b = a) ∧
      (∀ (n : ℕ) (U : X.Opens) (s : (algebra F).right.obj.obj (op U)),
        IsHomogeneousSection F n U s →
          IsHomogeneousSection E n U (a.right.hom.app (op U) s)) ∧
      (∀ (U : X.Opens) (r : X.presheaf.obj (op U)),
        a.right.hom.app (op U) ((algebra F).hom.hom.app (op U) r) =
          (algebra E).hom.hom.app (op U) r) ∧
      (∀ (n : ℕ) (U : X.Opens) (t : (algebra E).right.obj.obj (op U)),
        IsHomogeneousSection E n U t →
          ∃ (I : Type u) (V : I → X.Opens) (hV : ∀ i : I, V i ≤ U),
            iSup V = U ∧
            ∃ v : ∀ i : I, (algebra F).right.obj.obj (op (V i)),
              (∀ i : I, IsHomogeneousSection F n (V i) (v i)) ∧
              ∀ i : I, a.right.hom.app (op (V i)) (v i) =
                (algebra E).right.obj.map (homOfLE (hV i)).op t) := by
  obtain ⟨a, ha, huniq⟩ := exists_quasiCoherentSymmetricAlgebra_core X F (algebra E)
    (u ≫ inclusion E)
  change (∀ (U : X.Opens) (x : F.val.obj (op U)),
    a.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
      (inclusion E).val.app (op U) (u.val.app (op U) x)) at ha
  refine ⟨a, ha, huniq, map_homogeneous u a ha, ?_, ?_⟩
  · intro U r
    exact congrArg (fun t ↦ t.hom.app (op U) r) (Under.w a)
  · intro n U t ht
    have lifts (x : U) : ∃ (V : X.Opens) (hV : V ≤ U), x.1 ∈ V ∧
        ∃ v : (algebra F).right.obj.obj (op V),
          IsHomogeneousSection F n V v ∧ a.right.hom.app (op V) v =
            (algebra E).right.obj.map (homOfLE hV).op t := by
      obtain ⟨V, hVa, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset x.2
      obtain ⟨s, hs, heqs⟩ := ht ⟨V, hVa⟩ hVU
      obtain ⟨W, hWV, hxW, b, hb, heqb⟩ := section_local_lift u V n s hs x.1 hxV
      refine ⟨W, hWV.trans hVU, hxW, sectionMap F (op W) b,
        sectionMap_homogeneous F n W b hb, ?_⟩
      rw [map_sectionMap u a ha, heqb, sectionMap_restriction, heqs]
      exact (congrArg (fun f ↦ f t)
        ((algebra E).right.obj.map_comp (homOfLE hVU).op (homOfLE hWV).op)).symm
    choose V hV hxV v hv heq using lifts
    refine ⟨U, V, hV, ?_, v, hv, heq⟩
    apply le_antisymm (iSup_le hV)
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩

end AlgebraicGeometry.SymmetricAlgebraSheaf
