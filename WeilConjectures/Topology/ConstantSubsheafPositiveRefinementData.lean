/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSheafLocallyConstantUnitComparison

/-! # Finite positive refinements of integer subsheaf sections

## References

* Stacks Project, Tags 0A38, 00A5 and 0081.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- A finite disjoint partition of each original domain, with zero pieces and signed
positive component sections. The equations `hs`, `hzero`, and `hsigned` retain the
connection to the original map; positive values alone would not suffice. -/
structure PositiveRefinementData
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C)
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) where
  n : ℕ
  A : Fin n → Opens X
  hA : ∀ i, IsCompact (A i : Set X)
  c : Fin n → ℕ
  hc : ∀ i, 0 < c i
  f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K
  hv : ∀ i,
    (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ))

  parent : Fin n → Fin m
  hAU : ∀ j, A j ≤ U (parent j)
  Z : Fin m → Opens X
  hZU : ∀ i, Z i ≤ U i
  hdisjoint : ∀ j k, parent j = parent k → j ≠ k → Disjoint (A j) (A k)
  hdisjointZ : ∀ j, Disjoint (A j) (Z (parent j))
  hcover : ∀ i, U i = Z i ⊔ ⨆ j : {j // parent j = i}, A j.1
  sign : Fin n → ℤ
  s : ∀ i, K.obj.obj (op (U i))
  hs : ∀ i, s i = (Sigma.ι _ i ≫ g).hom.app (op (U i))
      (abelianOpenExtensionSection (U i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (U i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (U i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (U i).inclusion').obj (U i))) (ULift.up 1)))
  hzero : ∀ i, K.obj.map (homOfLE (hZU i)).op (s i) = 0
  hsigned : ∀ j, K.obj.map (homOfLE (hAU j)).op (s (parent j)) =
    sign j • (f j).hom.app (op (A j))
      (abelianOpenExtensionSection (A j)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A j) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A j)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A j).inclusion').obj (A j))) (ULift.up 1)))

/-- A section gives a map from the integer extension by zero, sending its canonical
unit to that section. -/
private theorem extension_integer_section (X : TopCat.{u})
    (K : Sheaf AddCommGrpCat X) (U : Opens X) (t : K.obj.obj (op U)) :
    ∃ f : (abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K,
      f.hom.app (op U) (abelianOpenExtensionSection U
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) U le_rfl
        ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op ((Opens.map U.inclusion').obj U)) (ULift.up 1))) = t := by
  classical
  let : DecidableEq (U ⟶ U) := Classical.decEq _
  let Y := (Opens.toTopCat X).obj U
  let P := (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let R := abelianOpenRestriction U K
  have hle (V : Opens Y) : U.isOpenEmbedding.functor.obj V ≤ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  let a : P ⟶ R.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down • K.obj.map (homOfLE (hle V.unop)).op t
          map_zero' := by simp
          map_add' := by intro z w; simp [add_zsmul] }
      naturality := by
        intro V W i
        apply AddCommGrpCat.hom_ext
        ext z
        change z.down • K.obj.map (homOfLE (hle W.unop)).op t =
          K.obj.map (U.isOpenEmbedding.functor.map i.unop).op
            (z.down • K.obj.map (homOfLE (hle V.unop)).op t)
        rw [map_zsmul, ← ConcreteCategory.comp_apply, ← K.obj.map_comp]
        rfl }
  let b : ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ R :=
    ObjectProperty.homMk (sheafifyLift (Opens.grothendieckTopology Y) a R.property)
  let f := (abelianOpenExtensionByZero U).map b ≫ abelianOpenCounit U K
  refine ⟨f, ?_⟩
  let W := (Opens.map U.inclusion').obj U
  let z := (toSheafify (Opens.grothendieckTopology Y) P).app (op W) (ULift.up 1)
  have hb : b.hom.app (op W) z = a.app (op W) (ULift.up 1) :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_sheafifyLift
        (Opens.grothendieckTopology Y) a R.property) (op W)) (ULift.up 1)
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology X)
      ((abelianOpenExtensionPresheaf U).map b)) (op U))
  have hc := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_sheafifyLift (Opens.grothendieckTopology X)
      (abelianOpenPresheafCounit U K) K.property) (op U))
  dsimp [f, abelianOpenExtensionSection]
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ConcreteCategory.comp_apply]
  erw [← hf, hc]
  dsimp [abelianOpenPresheafCounit, abelianOpenCounitApp,
    abelianOpenExtensionPresheaf, siteExtensionByZeroPresheaf,
    siteExtensionByZeroHom, siteExtensionByZeroHomApp]
  erw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
  change (eqToHom (congrArg (fun V : Opens X ↦ K.obj.obj (op V))
    (openImage_preimage_eq U U le_rfl))) (b.hom.app (op W) z) = t
  rw [hb]
  change (eqToHom (congrArg (fun V : Opens X ↦ K.obj.obj (op V))
    (openImage_preimage_eq U U le_rfl)))
    ((1 : ℤ) • K.obj.map (homOfLE (hle W)).op t) = t
  rw [one_zsmul]
  erw [← eqToHom_map K.obj (congrArg op (openImage_preimage_eq U U le_rfl))]
  rw [← ConcreteCategory.comp_apply, ← K.obj.map_comp]
  have hid : (homOfLE (hle W)).op ≫
      eqToHom (congrArg op (openImage_preimage_eq U U le_rfl)) = 𝟙 (op U) :=
    Subsingleton.elim _ _
  rw [hid, K.obj.map_id]
  rfl

-- The existing statement names an existential witness whose predicate is True.
/-- Construct a finite signed partition and positive component maps, without yet
constructing a morphism between the coproducts. -/
theorem positive_refinement_data
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (hU : ∀ i, IsCompact (U i : Set X))
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) :
    ∃ d : PositiveRefinementData X K C ι isoC m U g, True := by
  classical
  let η := toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let q := ι ≫ isoC.hom
  let s (i : Fin m) := (Sigma.ι _ i ≫ g).hom.app (op (U i))
    (abelianOpenExtensionSection (U i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (U i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (U i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (U i).inclusion').obj (U i))) (ULift.up 1)))
  obtain ⟨e, hres, hunit⟩ :=
    constantSheaf_locallyConstant_unit_comparison X (ULift.{u} ℤ)
  let l (i : Fin m) := e (U i) (q.hom.app (op (U i)) (s i))
  let B (i : Fin m) (a : ULift.{u} ℤ) : Opens X :=
    ⟨Subtype.val '' {x : U i | l i x = a},
      (U i).isOpen.isOpenMap_subtype_val _ ((l i).isLocallyConstant.isOpen_fiber a)⟩
  have hBU (i : Fin m) (a : ULift.{u} ℤ) : B i a ≤ U i := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have hBval (i : Fin m) (a : ULift.{u} ℤ) (x : B i a) :
      l i ⟨x.1, hBU i a x.2⟩ = a := by
    obtain ⟨y, hy, hxy⟩ := x.2
    have heq : (⟨x.1, hBU i a x.2⟩ : U i) = y := Subtype.ext hxy.symm
    rw [heq]
    exact hy
  have hBcompact (i : Fin m) (a : ULift.{u} ℤ) : IsCompact (B i a : Set X) := by
    have : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hU i)
    exact ((l i).isLocallyConstant.isClopen_fiber a).isClosed.isCompact.image
      continuous_subtype_val
  have hfinite (i : Fin m) : ({a | a ∈ Set.range (l i) ∧ a ≠ 0} :
      Set (ULift.{u} ℤ)).Finite := by
    have : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hU i)
    exact (l i).range_finite.subset (fun _ h ↦ h.1)
  let T := (i : Fin m) × {a : ULift.{u} ℤ // a ∈ Set.range (l i) ∧ a ≠ 0}
  let : ∀ i, Fintype {a : ULift.{u} ℤ // a ∈ Set.range (l i) ∧ a ≠ 0} :=
    fun i ↦ (hfinite i).fintype
  let n := Fintype.card T
  let r : Fin n ≃ T := (Fintype.equivFin T).symm
  let p (j : Fin n) := (r j).1
  let a (j : Fin n) := (r j).2.1
  let A (j : Fin n) := B (p j) (a j)
  have ha (j : Fin n) : (a j).down ≠ 0 := by
    intro h
    exact (r j).2.2.2 (ULift.ext h)
  have hrestrict (i : Fin m) (b : ULift.{u} ℤ) :
      q.hom.app (op (B i b)) (K.obj.map (homOfLE (hBU i b)).op (s i)) =
        η.app (op (B i b)) b := by
    rw [← ConcreteCategory.comp_apply]
    erw [q.hom.naturality]
    rw [ConcreteCategory.comp_apply]
    apply (e (B i b)).injective
    apply LocallyConstant.ext
    intro x
    exact (hres (U i) (B i b) (hBU i b) _ x).trans
      ((hBval i b x).trans (hunit (B i b) b x).symm)
  let sign (j : Fin n) := (a j).down.sign
  let t (j : Fin n) := sign j • K.obj.map (homOfLE (hBU (p j) (a j))).op (s (p j))
  have ht (j : Fin n) : q.hom.app (op (A j)) (t j) =
      η.app (op (A j)) (ULift.up ((a j).down.natAbs : ℤ)) := by
    dsimp [t, A]
    rw [map_zsmul, hrestrict]
    change sign j • η.app (op (B (p j) (a j))) (a j) =
      η.app (op (B (p j) (a j))) (ULift.up ((a j).down.natAbs : ℤ))
    rw [← map_zsmul]
    congr 1
    apply ULift.ext
    change sign j * (a j).down = _
    exact Int.sign_mul_self_eq_natAbs _
  choose f hf using fun j ↦ extension_integer_section X K (A j) (t j)
  refine ⟨{
    n := n
    A := A
    hA := fun j ↦ hBcompact (p j) (a j)
    c := fun j ↦ (a j).down.natAbs
    hc := fun j ↦ Int.natAbs_pos.mpr (ha j)
    f := f
    hv := fun j ↦ (congrArg (q.hom.app (op (A j))) (hf j)).trans (ht j)
    parent := p
    hAU := fun j ↦ hBU (p j) (a j)
    Z := fun i ↦ B i 0
    hZU := fun i ↦ hBU i 0
    hdisjoint := ?_
    hdisjointZ := ?_
    hcover := ?_
    sign := sign
    s := s
    hs := fun _ ↦ rfl
    hzero := ?_
    hsigned := ?_ }, True.intro⟩
  · intro j k hparent hne
    have hab : a j ≠ a k := by
      intro hb
      have hr : r j = r k := by
        apply Sigma.ext hparent
        apply (Subtype.heq_iff_coe_eq (fun b ↦ ?_)).mpr hb
        change (b ∈ Set.range (l (p j)) ∧ b ≠ 0) ↔
          (b ∈ Set.range (l (p k)) ∧ b ≠ 0)
        rw [hparent]
      exact hne (r.injective hr)
    change Disjoint (B (p j) (a j)) (B (p k) (a k))
    rw [← hparent]
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hj := hBval (p j) (a j) ⟨x, hx.1⟩
    have hk := hBval (p j) (a k) ⟨x, hx.2⟩
    exact (hab (hj.symm.trans hk)).elim
  · intro j
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hj := hBval (p j) (a j) ⟨x, hx.1⟩
    have hz := hBval (p j) 0 ⟨x, hx.2⟩
    exact ((r j).2.2.2 (hj.symm.trans hz)).elim
  · intro i
    apply le_antisymm
    · intro x hx
      by_cases hz : l i ⟨x, hx⟩ = 0
      · exact Or.inl ⟨⟨x, hx⟩, hz, rfl⟩
      · let v : T := ⟨i, ⟨l i ⟨x, hx⟩, ⟨⟨⟨x, hx⟩, rfl⟩, hz⟩⟩⟩
        let j := r.symm v
        have hpj : p j = i := congrArg Sigma.fst (r.apply_symm_apply v)
        have haj : a j = l i ⟨x, hx⟩ :=
          congrArg (fun w : T ↦ w.2.1) (r.apply_symm_apply v)
        apply Or.inr
        apply Opens.mem_iSup.mpr
        refine ⟨⟨j, hpj⟩, ?_⟩
        change x ∈ B (p j) (a j)
        rw [hpj, haj]
        exact ⟨⟨x, hx⟩, rfl, rfl⟩
    · apply sup_le (hBU i 0)
      apply iSup_le
      intro j
      simpa only [A, j.2] using hBU (p j.1) (a j.1)
  · intro i
    have : Mono q := inferInstance
    have : Mono q.hom := inferInstance
    have : Mono (q.hom.app (op (B i 0))) := inferInstance
    apply (AddCommGrpCat.mono_iff_injective (q.hom.app (op (B i 0)))).mp inferInstance
    rw [map_zero, hrestrict]
    exact map_zero _
  · intro j
    rw [hf j]
    dsimp [t]
    rw [smul_smul]
    have hsign : sign j * sign j = 1 := by
      rcases lt_or_gt_of_ne (ha j) with h | h
      · simp [sign, Int.sign_eq_neg_one_of_neg h]
      · simp [sign, Int.sign_eq_one_of_pos h]
    rw [hsign, one_smul]

end TopCat.Sheaf
