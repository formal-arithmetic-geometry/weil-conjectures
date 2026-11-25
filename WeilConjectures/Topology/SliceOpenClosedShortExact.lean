/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.Topology.InverseImageStalk

/-! # Exactness for the slice-site open extension

For an open `U` with closed complement, the extension by zero from `U`, the sheaf, and the
pushforward of its restriction to the complement form a short exact sequence.

## Implementation details

The extension by zero is the sheafification of the slice-site extension-by-zero presheaf; on an
open `V ≤ U` the index type `V ⟶ U` has exactly one member, and otherwise none. Exactness is
checked on stalks at points of `U` and of its complement.

## References

* [Stacks Project, Tag 02UT](https://stacks.math.columbia.edu/tag/02UT)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- For an open `U`, a map `a` from the slice-site extension by zero of `F|_U` to `F` which is
the identity on the summands, followed by the unit `F → i_* i^{-1} F` for the closed complement
`i`, is a short exact sequence. -/
theorem slice_open_closed_short_exact
    (X : TopCat.{u}) (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      ((siteExtensionByZeroPresheaf U).obj (F.over U).obj) ⟶ F)
    (ha : ∀ (V : Opens X) (φ : V ⟶ U) (s : F.obj.obj (Opposite.op V)),
      (a.hom.app (Opposite.op V))
        ((toSheafify (Opens.grothendieckTopology X)
          ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)).app (Opposite.op V)
          (DirectSum.of (fun ψ : V ⟶ U ↦
            (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)) = s) :
    ∃ h : a ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F = 0,
      (ShortComplex.mk a
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F) h).ShortExact := by
  classical
  let i : TopCat.of ↥((U : Set X)ᶜ) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let A := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)
  let G := (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F
  let b := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F
  let T (x : X) := Sheaf.forget AddCommGrpCat.{u} X ⋙
    Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have (x : X) : (T x).PreservesZeroMorphisms := by
    dsimp only [T]
    infer_instance
  have hopen :
    (∀ (x : X), x ∈ U →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a.hom)) ∧
    (∀ (x : X), x ∉ U →
      IsZero (TopCat.Presheaf.stalk
        (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)).obj) x)) := by
    let P := (siteExtensionByZeroPresheaf U).obj (F.over U).obj
    let A := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P
    let η := toSheafify (Opens.grothendieckTopology X) P
    let k := η ≫ a.hom
    have hk (V : Opens X) (φ : V ⟶ U) (s : F.obj.obj (Opposite.op V)) :
        (k.app (Opposite.op V))
          (DirectSum.of (fun ψ : V ⟶ U ↦
            (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s) = s := ha V φ s
    have hinj (V : Opens X) : Function.Injective (k.app (Opposite.op V)) := by
      by_cases hv : Nonempty (V ⟶ U)
      · obtain ⟨φ⟩ := hv
        let j := DirectSum.of (fun ψ : V ⟶ U ↦
          (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ
        have hj (s : P.obj (Opposite.op V)) : j (k.app (Opposite.op V) s) = s := by
          change DirectSum (V ⟶ U)
            (fun ψ ↦ (F.over U).obj.obj (Opposite.op (Over.mk ψ))) at s
          induction s using DirectSum.induction_on with
          | zero => simp [j]
          | of ψ s =>
            have hψ : ψ = φ := Subsingleton.elim _ _
            subst ψ
            exact congrArg j (hk V φ s)
          | add s t hs ht =>
            change j ((k.app (Opposite.op V)).hom (s + t)) = s + t
            rw [map_add, map_add, hs, ht]
        exact Function.LeftInverse.injective hj
      · have : IsEmpty (V ⟶ U) := not_nonempty_iff.mp hv
        intro s t _
        change DirectSum (V ⟶ U)
          (fun φ ↦ (F.over U).obj.obj (Opposite.op (Over.mk φ))) at s t
        exact Subsingleton.elim s t
    constructor
    · intro x hx
      let S := Presheaf.stalkFunctor AddCommGrpCat.{u} x
      have hη : IsIso (S.map η) :=
        Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
      have hki := Presheaf.stalkFunctor_map_injective_of_app_injective hinj x
      have hai : Function.Injective (S.map a.hom) := by
        have hηs := ConcreteCategory.bijective_of_isIso (S.map η)
        intro s t h
        obtain ⟨s', rfl⟩ := hηs.2 s
        obtain ⟨t', rfl⟩ := hηs.2 t
        apply congrArg (S.map η)
        apply hki
        change (S.map k) s' = (S.map k) t'
        simpa only [k, Functor.map_comp, ConcreteCategory.comp_apply] using h
      have has : Function.Surjective (S.map a.hom) := by
        intro t
        obtain ⟨V, hVU, hxV, s, hs⟩ := Presheaf.exists_le_germ_eq F.obj t hx
        let φ : V ⟶ U := homOfLE hVU
        let q : P.obj (Opposite.op V) := DirectSum.of
          (fun ψ : V ⟶ U ↦ (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s
        refine ⟨Presheaf.germ A.obj V x hxV (η.app (Opposite.op V) q), ?_⟩
        rw [Presheaf.stalkFunctor_map_germ_apply]
        exact (congrArg (Presheaf.germ F.obj V x hxV) (ha V φ s)).trans hs
      have : Mono (S.map a.hom) := (AddCommGrpCat.mono_iff_injective _).mpr hai
      have : Epi (S.map a.hom) := (AddCommGrpCat.epi_iff_surjective _).mpr has
      exact isIso_of_mono_of_epi _
    · intro x hx
      have hp : IsZero (Presheaf.stalk P x) := by
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        suffices hh : ∀ t : Presheaf.stalk (C := AddCommGrpCat.{u}) P x, t = 0 from
          ⟨fun a b ↦ (hh a).trans (hh b).symm⟩
        intro t
        obtain ⟨V, hxV, s, rfl⟩ := Presheaf.exists_germ_eq P t
        have : IsEmpty (V ⟶ U) := ⟨fun f ↦ hx (f.le hxV)⟩
        change DirectSum (V ⟶ U)
          (fun φ ↦ (F.over U).obj.obj (Opposite.op (Over.mk φ))) at s
        have hs : s = 0 := Subsingleton.elim _ _
        erw [hs]
        exact map_zero _
      have := Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
      exact hp.of_iso (asIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η)).symm
  obtain ⟨haU, haC⟩ := hopen
  obtain ⟨hbU, hbC, _⟩ := closedPushforwardAbelianStalks
    ((U : Set X)ᶜ) U.isOpen.isClosed_compl G
  have hbIso (x : X) (hx : x ∉ U) : IsIso ((T x).map b) := by
    let z : TopCat.of ↥((U : Set X)ᶜ) := ⟨x, hx⟩
    obtain ⟨c, hc, _⟩ := Sheaf.exists_inverseImage_stalk_iso_ab i z
    have hp := hbC z
    have he : (T x).map b ≫ Presheaf.stalkPushforward AddCommGrpCat.{u} i G.obj z =
        (c.app F).hom := by
      apply Presheaf.stalk_hom_ext F.obj
      intro V hxV
      change Presheaf.germ F.obj V x hxV ≫
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map b.hom ≫
          Presheaf.stalkPushforward AddCommGrpCat.{u} i G.obj z = _
      rw [← Category.assoc, Presheaf.stalkFunctor_map_germ, Category.assoc]
      erw [Presheaf.stalkPushforward_germ AddCommGrpCat.{u} i G.obj V z hxV]
      apply AddCommGrpCat.hom_ext
      ext s
      exact (hc F V hxV s).symm
    have : IsIso ((T x).map b ≫
        Presheaf.stalkPushforward AddCommGrpCat.{u} i G.obj z) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right ((T x).map b)
      (Presheaf.stalkPushforward AddCommGrpCat.{u} i G.obj z)
  have hz (x : X) : (T x).map (a ≫ b) = 0 := by
    rw [Functor.map_comp]
    by_cases hx : x ∈ U
    · exact (hbU x (by simpa using hx)).eq_of_tgt _ _
    · exact (haC x hx).eq_of_src _ _
  have hab : a ≫ b = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext s
    apply Presheaf.section_ext ((Sheaf.pushforward AddCommGrpCat.{u} i).obj G) V.unop
    intro x hxV
    have hh : (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (a ≫ b).hom = 0 := hz x
    have ht := ConcreteCategory.congr_hom hh (Presheaf.germ A.obj V.unop x hxV s)
    rw [Presheaf.stalkFunctor_map_germ_apply] at ht
    change (Presheaf.germ ((Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj
      V.unop x hxV).hom ((b.hom.app V).hom ((a.hom.app V).hom s)) =
        (Presheaf.germ ((Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj
          V.unop x hxV).hom 0
    rw [map_zero]
    exact ht
  refine ⟨hab, (shortExact_iff_stalkFunctor_map_shortExact _).mpr ?_⟩
  intro x
  let S := (ShortComplex.mk a b hab).map (T x)
  change S.ShortExact
  by_cases hx : x ∈ U
  · have hzero : IsZero S.X₃ := hbU x (by simpa using hx)
    have : IsIso S.f := haU x hx
    exact { exact := (ShortComplex.exact_iff_epi S (hzero.eq_of_tgt _ _)).mpr
              inferInstance
            mono_f := inferInstance
            epi_g := ⟨fun _ _ _ ↦ hzero.eq_of_src _ _⟩ }
  · have hzero : IsZero S.X₁ := haC x hx
    have : IsIso S.g := hbIso x hx
    exact { exact := (ShortComplex.exact_iff_mono S (hzero.eq_of_src _ _)).mpr
              inferInstance
            mono_f := ⟨fun _ _ _ ↦ hzero.eq_of_tgt _ _⟩
            epi_g := inferInstance }

end TopCat
