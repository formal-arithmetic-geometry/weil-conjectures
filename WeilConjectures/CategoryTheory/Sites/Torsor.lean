/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Torsors under a sheaf of abelian groups

Let `G` be a sheaf of abelian groups on a site `(C, J)`. A `G`-torsor is a sheaf of sets `T`
with an action of `G` which is simply transitive on the sections over every object and such
that `T` has sections locally. The isomorphism classes of `G`-torsors are classified by
`H¹(G) = Ext¹(ℤ, G)`.

## Main definitions

- `CategoryTheory.Sheaf.Torsor`: a `G`-torsor.
- `CategoryTheory.Sheaf.Torsor.Iso`: an isomorphism of `G`-torsors, and
  `CategoryTheory.Sheaf.Torsor.setoid` the relation of being isomorphic.
- `CategoryTheory.Sheaf.Torsor.trivial`: the trivial torsor `G`.
- `CategoryTheory.Sheaf.Torsor.lifts`: the torsor of local lifts of a global section along an
  epimorphism `I → Q` with kernel `G`.

## Main statements

- `CategoryTheory.Sheaf.Torsor.exists_quotientEquiv_H_one`: on a site with a terminal object,
  `H¹(G)` is in bijection with the isomorphism classes of `G`-torsors, the class `0`
  corresponding to the torsors with a global section. The bijection sends a global section `s`
  of `Q`, for `0 → G → I → Q → 0` with `I` injective, to the torsor
  `CategoryTheory.Sheaf.Torsor.lifts` of local lifts of `s` to `I`.
- `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor`: `Ext¹(ℤ, G)` is in bijection with the
  isomorphism classes of `G`-torsors. The proof is `sorry`.
- `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor`: so is `H¹(G)`.
- `CategoryTheory.Sheaf.subsingleton_H_one_iff`: `H¹(G) = 0` if and only if every `G`-torsor
  is trivial.

## TODO

The bijections are only recorded as the existence of an equivalence of types. The canonical
map sends an extension `0 → G → E → ℤ → 0` to the torsor `π⁻¹(1)`, and it carries the Baer
sum to the contracted product of torsors.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Sheaf

open Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sieve on `U` of the morphisms `V ⟶ U` such that the presheaf `F` has a section
over `V`. -/
def nonemptySieve (F : Cᵒᵖ ⥤ Type w) (U : C) : Sieve U where
  arrows V _ := Nonempty (F.obj (op V))
  downward_closed {_ _} _ := fun ⟨t⟩ g ↦ ⟨F.map g.op t⟩

/-- A *torsor* under a sheaf `G` of abelian groups: a sheaf of sets `T` with an action
`G × T → T` of `G` which is simply transitive on the sections over every object, and such
that `T` has sections locally, i.e. every object is covered by objects over which `T` has a
section. Equivalently, `T` is locally isomorphic to `G` with its translation action.
(blueprint: `def-sc-gm-torsor`, for a general abelian sheaf `G` on a general site; the étale
`𝔾ₘ`-torsors and the Zariski `𝒪ˣ`-torsors of the blueprint are the cases
`G = AlgebraicGeometry.Scheme.gmSheaf X` and `G = AlgebraicGeometry.Scheme.unitsSheaf X`) -/
structure Torsor (G : Sheaf J AddCommGrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of `G` on `T`. -/
  vadd (U : Cᵒᵖ) : G.obj.obj U → sheaf.obj.obj U → sheaf.obj.obj U
  zero_vadd (U : Cᵒᵖ) (t : sheaf.obj.obj U) : vadd U 0 t = t
  add_vadd (U : Cᵒᵖ) (g h : G.obj.obj U) (t : sheaf.obj.obj U) :
    vadd U (g + h) t = vadd U g (vadd U h t)
  map_vadd {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (t : sheaf.obj.obj U) :
    sheaf.obj.map f (vadd U g t) = vadd V (G.obj.map f g) (sheaf.obj.map f t)
  /-- The action is simply transitive on the sections over every object. -/
  bijective_vadd (U : Cᵒᵖ) (t : sheaf.obj.obj U) : Function.Bijective (vadd U · t)
  /-- The torsor has sections locally. -/
  nonemptySieve_mem (U : C) : nonemptySieve sheaf.obj U ∈ J U

namespace Torsor

variable {G : Sheaf J AddCommGrpCat.{w}}

/-- An isomorphism of `G`-torsors: an isomorphism of the underlying sheaves of sets which
commutes with the action of `G`. -/
structure Iso (T T' : Torsor G) where
  /-- The isomorphism of underlying sheaves of sets. -/
  iso : T.sheaf ≅ T'.sheaf
  map_vadd (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
    iso.hom.hom.app U (T.vadd U g t) = T'.vadd U g (iso.hom.hom.app U t)

/-- The identity isomorphism of a torsor. -/
def Iso.refl (T : Torsor G) : Iso T T where
  iso := CategoryTheory.Iso.refl _
  map_vadd _ _ _ := rfl

/-- The inverse of an isomorphism of torsors. -/
def Iso.symm {T T' : Torsor G} (e : Iso T T') : Iso T' T where
  iso := e.iso.symm
  map_vadd U g t := by
    let f := ((sheafSections J (Type w)).obj U).mapIso e.iso
    have h (x : T'.sheaf.obj.obj U) : e.iso.hom.hom.app U (e.iso.inv.hom.app U x) = x :=
      Iso.inv_hom_id_apply f x
    apply f.toEquiv.injective
    change e.iso.hom.hom.app U (e.iso.inv.hom.app U _) = e.iso.hom.hom.app U _
    rw [h, e.map_vadd]
    exact congr_arg _ (h t).symm

/-- The composition of two isomorphisms of torsors. -/
def Iso.trans {T T' T'' : Torsor G} (e : Iso T T') (e' : Iso T' T'') : Iso T T'' where
  iso := e.iso ≪≫ e'.iso
  map_vadd U g t := by
    change e'.iso.hom.hom.app U (e.iso.hom.hom.app U _) = _
    rw [e.map_vadd, e'.map_vadd]
    rfl

/-- Being isomorphic is an equivalence relation on `G`-torsors; its quotient is the set of
isomorphism classes of `G`-torsors. -/
instance setoid : Setoid (Torsor G) where
  r T T' := Nonempty (Iso T T')
  iseqv := ⟨fun T ↦ ⟨Iso.refl T⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

variable (G) in
/-- The trivial `G`-torsor: `G` acting on itself by translation. -/
def trivial : Torsor G where
  sheaf := (sheafCompose J (forget AddCommGrpCat.{w})).obj G
  vadd U g t := (g + show G.obj.obj U from t : G.obj.obj U)
  zero_vadd U t := zero_add (show G.obj.obj U from t)
  add_vadd U g h t := add_assoc g h (show G.obj.obj U from t)
  map_vadd f g _ := map_add (G.obj.map f).hom g _
  bijective_vadd U t := (Equiv.addRight (show G.obj.obj U from t)).bijective
  nonemptySieve_mem U := J.superset_covering (fun _ _ _ ↦ ⟨(0 : G.obj.obj _)⟩) (J.top_mem U)

end Torsor

section ShortExact

variable {I Q : Sheaf J AddCommGrpCat.{w}}

/-- A monomorphism of abelian sheaves is injective on sections. -/
lemma injective_hom_app_of_mono [HasSheafify J AddCommGrpCat.{w}] {F : Sheaf J AddCommGrpCat.{w}}
    (f : F ⟶ I) [Mono f] (U : Cᵒᵖ) : Function.Injective (f.hom.app U) := by
  rw [← AddCommGrpCat.mono_iff_injective]
  exact ((sheafToPresheaf J _ ⋙ (evaluation _ _).obj U).map_mono f :)

/-- Sections are left exact: in a short exact sequence `0 → F → I → Q → 0` of abelian sheaves,
a section of `I` which maps to zero in `Q` comes from a section of `F`. -/
lemma exists_hom_app_eq_of_shortExact [HasSheafify J AddCommGrpCat.{w}]
    {F : Sheaf J AddCommGrpCat.{w}} {ι : F ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0}
    (hS : (ShortComplex.mk ι d w).ShortExact) {U : Cᵒᵖ} (x : I.obj.obj U)
    (hx : d.hom.app U x = 0) : ∃ a, ι.hom.app U a = x := by
  have := hS.mono_f
  have h := hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf J _ ⋙ (evaluation _ _).obj U) inferInstance inferInstance
  rw [ShortComplex.ab_exact_iff] at h
  exact h x hx

/-- If `ι ≫ d = 0`, then `d` kills the sections in the image of `ι`. -/
lemma hom_app_hom_app_of_comp_eq_zero {F : Sheaf J AddCommGrpCat.{w}} {ι : F ⟶ I}
    {d : I ⟶ Q} (w : ι ≫ d = 0) {U : Cᵒᵖ} (a : F.obj.obj U) :
    d.hom.app U (ι.hom.app U a) = 0 := by
  simpa using congr_arg (fun f : F ⟶ Q ↦ f.hom.app U a) w

end ShortExact

namespace Torsor

variable {G : Sheaf J AddCommGrpCat.{w}}

/-- Two sections of a sheaf of sets agree if they agree over every object over which the torsor
`P` has a section. -/
lemma ext_of_nonempty (P : Torsor G) (F : Sheaf J (Type w)) {U : C} {σ σ' : F.obj.obj (op U)}
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U), Nonempty (P.sheaf.obj.obj (op V)) →
      F.obj.map f.op σ = F.obj.map f.op σ') : σ = σ' :=
  ((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _ (P.nonemptySieve_mem U)).isSeparatedFor.ext
    fun _ f hf ↦ h f hf

/-- A section-wise map `g` from a torsor `P` to a sheaf of sets `F` which is natural and
invariant under the action of `G` is the restriction of a global section of `F`: the values
on the local sections of `P` glue. -/
lemma exists_section_of_invariant (P : Torsor G) (F : Sheaf J (Type w)) {T : C}
    (hT : IsTerminal T) (g : ∀ U, P.sheaf.obj.obj U → F.obj.obj U)
    (hg : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (x : P.sheaf.obj.obj U),
      F.obj.map f (g U x) = g V (P.sheaf.obj.map f x))
    (hinv : ∀ U (a : G.obj.obj U) (x : P.sheaf.obj.obj U), g U (P.vadd U a x) = g U x) :
    ∃ σ : F.obj.obj (op T), ∀ U (x : P.sheaf.obj.obj U),
      g U x = F.obj.map (hT.from U.unop).op σ := by
  have hg' : ∀ U (x y : P.sheaf.obj.obj U), g U x = g U y := fun U x y ↦ by
    obtain ⟨a, rfl⟩ := (P.bijective_vadd U x).2 y
    rw [hinv]
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _ (P.nonemptySieve_mem T)
  let x : Presieve.FamilyOfElements F.obj (nonemptySieve P.sheaf.obj T).arrows :=
    fun V _ hf ↦ g (op V) hf.some
  have hx : x.Compatible := by
    intro W₁ W₂ V f₁ f₂ g₁ g₂ h₁ h₂ _
    simp only [x]
    rw [hg, hg]
    exact hg' _ _ _
  refine ⟨hF.amalgamate x hx, fun U y ↦ ?_⟩
  rw [hF.valid_glue hx _ ⟨y⟩]
  exact hg' _ _ _

/-- A morphism of the underlying sheaves of two `G`-torsors which commutes with the action of
`G` is an isomorphism of torsors. -/
noncomputable def Iso.ofHom {P P' : Torsor G} (f : P.sheaf ⟶ P'.sheaf)
    (hf : ∀ U (a : G.obj.obj U) (x : P.sheaf.obj.obj U),
      f.hom.app U (P.vadd U a x) = P'.vadd U a (f.hom.app U x)) : Iso P P' where
  iso :=
    have hinj : IsLocallyInjective f := Presheaf.isLocallyInjective_of_injective _ _
      fun U x y hxy ↦ by
        obtain ⟨a, rfl⟩ := (P.bijective_vadd U x).2 y
        have h := hf U a x
        rw [← hxy] at h
        have ha : a = 0 := (P'.bijective_vadd U _).1 (h.symm.trans (P'.zero_vadd U _).symm)
        simp [ha, P.zero_vadd]
    have hsurj : IsLocallySurjective f := ⟨fun {U} y ↦ by
      refine J.superset_covering (fun V g hg ↦ ?_) (P.nonemptySieve_mem U)
      obtain ⟨x⟩ := hg
      obtain ⟨a, ha⟩ := (P'.bijective_vadd _ (f.hom.app _ x)).2 (P'.sheaf.obj.map g.op y)
      exact ⟨P.vadd _ a x, (hf _ _ _).trans ha⟩⟩
    have := (isLocallyBijective_iff_isIso f).1 ⟨hinj, hsurj⟩
    asIso f
  map_vadd := hf

section Lifts

variable {I Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0}

variable {T : C} (hT : IsTerminal T)

private lemma map_map_from {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {U V : Cᵒᵖ} (f : U ⟶ V)
    (s : F.obj (op T)) :
    F.map f (F.map (hT.from U.unop).op s) = F.map (hT.from V.unop).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  exact congr_arg (fun g : V.unop ⟶ T ↦ F.map g.op s) (hT.hom_ext _ _)

variable (d) in
/-- The subpresheaf of `I` of the sections lifting the restrictions of a global section `s`
of `Q`. -/
def liftsSubfunctor (s : Q.obj.obj (op T)) : Subfunctor (I.obj ⋙ forget AddCommGrpCat) where
  obj U := {x | d.hom.app U x = Q.obj.map (hT.from U.unop).op s}
  map {U V} f x hx := by
    change d.hom.app V (I.obj.map f x) = _
    rw [← ConcreteCategory.comp_apply, d.hom.naturality, ConcreteCategory.comp_apply]
    rw [hx, map_map_from]

/-- The sections of `I` lifting `s` form a sheaf. -/
lemma isSheaf_liftsSubfunctor (s : Q.obj.obj (op T)) :
    Presheaf.IsSheaf J (liftsSubfunctor d hT s).toFunctor := by
  have hI : Presieve.IsSheaf J (I.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget _)).obj I).property
  have hQ : Presieve.IsSheaf J (Q.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget _)).obj Q).property
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hI]
  intro U x hx
  refine (hQ _ hx).isSeparatedFor.ext fun V f hf ↦ ?_
  change Q.obj.map f.op (d.hom.app U x) = Q.obj.map f.op (Q.obj.map (hT.from U.unop).op s)
  rw [map_map_from, ← ConcreteCategory.comp_apply, ← d.hom.naturality,
    ConcreteCategory.comp_apply]
  exact hf

/-- Translating a lift of `s` by a section of `G` gives a lift of `s`. -/
lemma add_mem_liftsSubfunctor (s : Q.obj.obj (op T)) (hw : ι ≫ d = 0) {U : Cᵒᵖ} (a : G.obj.obj U)
    (x : (liftsSubfunctor d hT s).obj U) :
    (show I.obj.obj U from x.1) + ι.hom.app U a ∈ (liftsSubfunctor d hT s).obj U := by
  change d.hom.app U ((show I.obj.obj U from x.1) + ι.hom.app U a) = _
  rw [map_add, hom_app_hom_app_of_comp_eq_zero hw, add_zero]
  exact x.2

/-- The *lifting torsor* `P_s` of a global section `s` of `Q`, for a short exact sequence
`0 → G → I → Q → 0` of abelian sheaves: the sheaf of local lifts of `s` to `I`, on which `G`
acts by translation. The action is simply transitive because two lifts differ by a section of
the kernel `G` of `I → Q`, and `P_s` has sections locally because `I → Q` is an epimorphism.
(blueprint: `thm-galois-torsor-h1`, Steps 1 and 2) -/
def lifts [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hS : (ShortComplex.mk ι d w).ShortExact) (s : Q.obj.obj (op T)) : Torsor G where
  sheaf := ⟨(liftsSubfunctor d hT s).toFunctor, isSheaf_liftsSubfunctor hT s⟩
  vadd U a x := ⟨(show I.obj.obj U from x.1) + ι.hom.app U a, add_mem_liftsSubfunctor hT s w a x⟩
  zero_vadd U x := Subtype.ext (by simp)
  add_vadd U a b x := Subtype.ext (by
    change (show I.obj.obj U from x.1) + ι.hom.app U (a + b) =
      (show I.obj.obj U from x.1) + ι.hom.app U b + ι.hom.app U a
    rw [map_add, add_comm (ι.hom.app U a), add_assoc])
  map_vadd {U V} f a x := Subtype.ext (by
    change I.obj.map f ((show I.obj.obj U from x.1) + ι.hom.app U a) =
      I.obj.map f x.1 + ι.hom.app V (G.obj.map f a)
    rw [map_add, ← ConcreteCategory.comp_apply, ← ι.hom.naturality, ConcreteCategory.comp_apply])
  bijective_vadd U x := by
    have := hS.mono_f
    refine ⟨fun a b h ↦ injective_hom_app_of_mono ι U ?_, fun y ↦ ?_⟩
    · simpa using congr_arg Subtype.val h
    · obtain ⟨a, ha⟩ := exists_hom_app_eq_of_shortExact hS
        ((show I.obj.obj U from y.1) - (show I.obj.obj U from x.1)) (by
        rw [map_sub, sub_eq_zero]
        exact y.2.trans x.2.symm)
      exact ⟨a, Subtype.ext (by
        change (show I.obj.obj U from x.1) + ι.hom.app U a = y.1
        rw [ha, add_sub_cancel])⟩
  nonemptySieve_mem U := by
    have : IsLocallySurjective d := (isLocallySurjective_iff_epi' (φ := d)).2 hS.epi_g
    refine J.superset_covering (fun V f hf ↦ ?_)
      (Presheaf.imageSieve_mem J d.hom (Q.obj.map (hT.from U).op s))
    obtain ⟨x, hx⟩ := hf
    refine ⟨⟨x, ?_⟩⟩
    change d.hom.app _ x = _
    rw [hx, map_map_from]

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (hS : (ShortComplex.mk ι d w).ShortExact)

/-- The sections of the lifting torsor lift `s`. -/
lemma lifts_val {U : Cᵒᵖ} {s : Q.obj.obj (op T)} (x : (lifts hT hS s).sheaf.obj.obj U) :
    d.hom.app U x.1 = Q.obj.map (hT.from U.unop).op s := x.2

/-- Translation by a global section `x` of `I` identifies the lifting torsors of `s` and of
`s + d x`, so the class of `P_s` only depends on the class of `s` in the cokernel of `d`.
(blueprint: `thm-galois-torsor-h1`, Step 3) -/
lemma lifts_equiv_lifts_add (s : Q.obj.obj (op T)) (x : I.obj.obj (op T)) :
    lifts hT hS s ≈ lifts hT hS (s + d.hom.app (op T) x) := by
  refine ⟨Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun y ↦
        ⟨(show I.obj.obj U from y.1) + I.obj.map (hT.from U.unop).op x, ?_⟩
      naturality U V f := ?_ }) fun U a y ↦ ?_⟩
  · change d.hom.app U (_ + _) = Q.obj.map _ (s + _)
    rw [map_add, map_add, lifts_val, ← ConcreteCategory.comp_apply,
      d.hom.naturality, ConcreteCategory.comp_apply]
  · ext y
    apply Subtype.ext
    change I.obj.map f y.1 + I.obj.map (hT.from V.unop).op x =
      I.obj.map f ((show I.obj.obj U from y.1) + I.obj.map (hT.from U.unop).op x)
    rw [map_add, map_map_from]
  · apply Subtype.ext
    change (show I.obj.obj U from y.1) + ι.hom.app U a + _ = (show I.obj.obj U from y.1) + _ + _
    abel

/-- If the lifting torsors of `s` and `s'` are isomorphic, then `s' - s` lifts to a global
section of `I`: the differences `φ(x) - x`, for `φ : P_s ≅ P_{s'}` and `x` a local section
of `P_s`, do not depend on `x` and glue to such a lift.
(blueprint: `thm-galois-torsor-h1`, Step 4) -/
lemma exists_hom_app_eq_sub_of_lifts_equiv {s s' : Q.obj.obj (op T)}
    (h : lifts hT hS s ≈ lifts hT hS s') : ∃ x : I.obj.obj (op T), d.hom.app (op T) x = s' - s := by
  obtain ⟨e⟩ := h
  have he {U V : Cᵒᵖ} (f : U ⟶ V) (y : (lifts hT hS s).sheaf.obj.obj U) :
      (e.iso.hom.hom.app V ((lifts hT hS s).sheaf.obj.map f y)).1 =
        I.obj.map f (e.iso.hom.hom.app U y).1 := by
    rw [← ConcreteCategory.comp_apply, e.iso.hom.hom.naturality]
    rfl
  obtain ⟨σ, hσ⟩ := exists_section_of_invariant (lifts hT hS s)
    ((sheafCompose J (forget _)).obj I) hT
    (fun U y ↦ (show I.obj.obj U from (e.iso.hom.hom.app U y).1) - (show I.obj.obj U from y.1))
    (fun U V f y ↦ by
      change I.obj.map f (_ - _) = _
      rw [map_sub, he]
      rfl)
    (fun U a y ↦ by
      change (show I.obj.obj U from (e.iso.hom.hom.app U ((lifts hT hS s).vadd U a y)).1) - _ = _
      rw [e.map_vadd]
      change (show I.obj.obj U from (e.iso.hom.hom.app U y).1) + ι.hom.app U a -
        ((show I.obj.obj U from y.1) + ι.hom.app U a) = _
      abel)
  refine ⟨σ, ext_of_nonempty (lifts hT hS s) ((sheafCompose J (forget _)).obj Q)
    fun V f ⟨y⟩ ↦ ?_⟩
  have hf : f = hT.from V := hT.hom_ext _ _
  subst hf
  change Q.obj.map _ (d.hom.app (op T) σ) = Q.obj.map _ (s' - s)
  erw [← ConcreteCategory.comp_apply, ← d.hom.naturality, ConcreteCategory.comp_apply]
  change d.hom.app (op V) (I.obj.map _ σ) = _
  rw [show I.obj.map (hT.from V).op σ = _ from (hσ (op V) y).symm, map_sub, map_sub,
    lifts_val, lifts_val]

/-- The lifting torsor of `s` has a global section if and only if `s` lifts to `I`. -/
lemma nonempty_lifts_iff (s : Q.obj.obj (op T)) :
    Nonempty ((lifts hT hS s).sheaf.obj.obj (op T)) ↔
      ∃ x : I.obj.obj (op T), d.hom.app _ x = s := by
  have h : Q.obj.map (hT.from T).op s = s := by
    rw [hT.hom_ext (hT.from T) (𝟙 T), op_id, Q.obj.map_id]
    rfl
  refine ⟨fun ⟨x⟩ ↦ ⟨x.1, (lifts_val hT hS x).trans h⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, ?_⟩⟩⟩
  exact hx.trans h.symm

end Lifts

/-- Isomorphic torsors have sections over the same objects. -/
lemma nonempty_iff_of_equiv {P P' : Torsor G} (h : P ≈ P') (U : Cᵒᵖ) :
    Nonempty (P.sheaf.obj.obj U) ↔ Nonempty (P'.sheaf.obj.obj U) := by
  obtain ⟨e⟩ := h
  exact ⟨fun ⟨x⟩ ↦ ⟨e.iso.hom.hom.app U x⟩, fun ⟨x⟩ ↦ ⟨e.iso.inv.hom.app U x⟩⟩

section Sub

variable (P : Torsor G)

/-- The difference of two sections of a torsor: the unique section `a` of `G` with
`a +ᵥ x = y`. -/
noncomputable def sub {U : Cᵒᵖ} (x y : P.sheaf.obj.obj U) : G.obj.obj U :=
  ((P.bijective_vadd U x).2 y).choose

@[simp]
lemma sub_vadd {U : Cᵒᵖ} (x y : P.sheaf.obj.obj U) : P.vadd U (P.sub x y) x = y :=
  ((P.bijective_vadd U x).2 y).choose_spec

@[simp]
lemma sub_vadd_eq {U : Cᵒᵖ} (x : P.sheaf.obj.obj U) (a : G.obj.obj U) :
    P.sub x (P.vadd U a x) = a :=
  (P.bijective_vadd U x).1 (P.sub_vadd _ _)

lemma sub_eq_iff {U : Cᵒᵖ} (x y : P.sheaf.obj.obj U) (a : G.obj.obj U) :
    P.sub x y = a ↔ P.vadd U a x = y :=
  ⟨fun h ↦ h ▸ P.sub_vadd x y, fun h ↦ h ▸ P.sub_vadd_eq x a⟩

lemma sub_sub_sub {U : Cᵒᵖ} (x₀ x y : P.sheaf.obj.obj U) :
    P.sub x₀ y - P.sub x₀ x = P.sub x y := by
  obtain ⟨a, rfl⟩ := (P.bijective_vadd U x₀).2 x
  obtain ⟨b, rfl⟩ := (P.bijective_vadd U x₀).2 y
  refine ((P.sub_eq_iff _ _ _).2 ?_).symm
  simp only [sub_vadd_eq, ← P.add_vadd, sub_add_cancel]

lemma map_sub_apply {U V : Cᵒᵖ} (f : U ⟶ V) (x y : P.sheaf.obj.obj U) :
    G.obj.map f (P.sub x y) = P.sub (P.sheaf.obj.map f x) (P.sheaf.obj.map f y) := by
  conv_rhs => rw [← P.sub_vadd x y, P.map_vadd, sub_vadd_eq]

/-- The presheaf `P × P` of pairs of sections of a torsor. -/
def pairs : Cᵒᵖ ⥤ Type w where
  obj U := P.sheaf.obj.obj U × P.sheaf.obj.obj U
  map f := TypeCat.ofHom (Prod.map (P.sheaf.obj.map f) (P.sheaf.obj.map f))
  map_id U := by ext ⟨a, b⟩ <;> simp
  map_comp f g := by ext ⟨a, b⟩ <;> simp

@[simp]
lemma pairs_map_apply {U V : Cᵒᵖ} (f : U ⟶ V) (p : P.pairs.obj U) :
    P.pairs.map f p = (P.sheaf.obj.map f p.1, P.sheaf.obj.map f p.2) :=
  rfl

/-- The map `ℤ[P × P] → ℤ[P]` sending a pair `(x, y)` to `[y] - [x]`. -/
noncomputable def pairsDiff : P.pairs ⋙ AddCommGrpCat.free ⟶ P.sheaf.obj ⋙ AddCommGrpCat.free where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun p ↦ .of p.2 - .of p.1)
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of p)) =
      FreeAbelianGroup.map _ (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p))
    simp only [FreeAbelianGroup.map_of_apply]
    exact FreeAbelianGroup.lift_apply_of _ _

/-- The map `ℤ[P × P] → G` sending a pair `(x, y)` to the difference `y - x`. -/
noncomputable def pairsSub : P.pairs ⋙ AddCommGrpCat.free ⟶ G.obj where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun p ↦ P.sub p.1 p.2)
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of p)) =
      G.obj.map f (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p))
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of, Torsor.map_sub_apply]
    rfl

/-- The difference map `ℤ[P × P] → G` vanishes on the kernel of `ℤ[P × P] → ℤ[P]`: over an
object where `P` has a section `x₀`, it factors as `ℤ[P × P] → ℤ[P] → G`, `[y] ↦ y - x₀`. -/
lemma kernel_ι_pairsDiff_comp_pairsSub : kernel.ι P.pairsDiff ≫ P.pairsSub = 0 := by
  ext U : 2
  rw [NatTrans.comp_app, NatTrans.app_zero]
  by_cases hU : Nonempty (P.sheaf.obj.obj U)
  · obtain ⟨x₀⟩ := hU
    have : P.pairsSub.app U = P.pairsDiff.app U ≫
        AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun y ↦ P.sub x₀ y) := by
      ext : 1
      refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
      change FreeAbelianGroup.lift _ (FreeAbelianGroup.of p) =
        FreeAbelianGroup.lift _ (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p))
      simp only [FreeAbelianGroup.lift_apply_of]
      rw [_root_.map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
        sub_sub_sub]
    have h0 : (kernel.ι P.pairsDiff).app U ≫ P.pairsDiff.app U = 0 := by
      rw [← NatTrans.comp_app, kernel.condition, NatTrans.app_zero]
    rw [this]
    exact (Category.assoc _ _ _).symm.trans (by rw [h0]; exact zero_comp)
  · have : P.pairsSub.app U = 0 := by
      ext : 1
      exact FreeAbelianGroup.lift_ext _ _ fun p ↦ (hU ⟨p.1⟩).elim
    rw [this, comp_zero]

end Sub

section Surjective

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {I Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0}
  {T : C} (hT : IsTerminal T) (hS : (ShortComplex.mk ι d w).ShortExact)

/-- If `I` is injective, every `G`-torsor `P` is isomorphic to a lifting torsor.

Since `I` is injective, the map `ℤ[P × P] → G → I` extends along `ℤ[P × P] → ℤ[P]`; this gives
a map `b : P → I` with `b(a + x) = b(x) + a`. Then `d ∘ b` is invariant, hence a global
section `s` of `Q`, and `b` is an isomorphism `P ≅ P_s`.
(blueprint: `thm-galois-torsor-h1`, Step 5, where the Čech argument with the Godement sheaf is
replaced by the injectivity of `I`) -/
theorem exists_equiv_lifts [Injective I] (P : Torsor G) : ∃ s, P ≈ lifts hT hS s := by
  have : Injective I.obj :=
    Injective.injective_of_adjoint (sheafificationAdjunction J AddCommGrpCat.{w}) I
  obtain ⟨β, hβ⟩ := Injective.exists_comp_eq_of_kernel_ι_comp_eq_zero P.pairsDiff
    (P.pairsSub ≫ ι.hom) (by
    rw [← Category.assoc, kernel_ι_pairsDiff_comp_pairsSub, zero_comp])
  let b (U : Cᵒᵖ) (x : P.sheaf.obj.obj U) : I.obj.obj U := β.app U (FreeAbelianGroup.of x)
  have hb_vadd (U : Cᵒᵖ) (a : G.obj.obj U) (x : P.sheaf.obj.obj U) :
      b U (P.vadd U a x) = b U x + ι.hom.app U a := by
    have h := congr_arg (fun φ ↦ φ.app U (FreeAbelianGroup.of ((x, P.vadd U a x) : P.pairs.obj U)))
      hβ
    change β.app U (P.pairsDiff.app U _) = ι.hom.app U (P.pairsSub.app U _) at h
    have e₁ : P.pairsDiff.app U (FreeAbelianGroup.of ((x, P.vadd U a x) : P.pairs.obj U)) =
        FreeAbelianGroup.of (P.vadd U a x) - FreeAbelianGroup.of x :=
      FreeAbelianGroup.lift_apply_of _ _
    have e₂ : P.pairsSub.app U (FreeAbelianGroup.of ((x, P.vadd U a x) : P.pairs.obj U)) =
        P.sub x (P.vadd U a x) :=
      FreeAbelianGroup.lift_apply_of _ _
    rw [e₁, e₂, sub_vadd_eq] at h
    have e₃ := (β.app U).hom.map_sub (FreeAbelianGroup.of (P.vadd U a x)) (FreeAbelianGroup.of x)
    rw [eq_sub_iff_add_eq] at e₃
    exact e₃.symm.trans ((add_comm _ _).trans (congr_arg (b U x + ·) h))
  have hb_nat {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.sheaf.obj.obj U) :
      I.obj.map f (b U x) = b V (P.sheaf.obj.map f x) := by
    have h := congr_arg (fun φ ↦ φ (FreeAbelianGroup.of x)) (β.naturality f)
    exact h.symm
  obtain ⟨s, hs⟩ := exists_section_of_invariant P ((sheafCompose J (forget _)).obj Q) hT
    (fun U x ↦ d.hom.app U (b U x))
    (fun U V f x ↦ by
      change Q.obj.map f (d.hom.app U (b U x)) = _
      rw [← ConcreteCategory.comp_apply, ← d.hom.naturality, ConcreteCategory.comp_apply]
      exact congr_arg (d.hom.app V) (hb_nat f x))
    (fun U a x ↦ by
      change d.hom.app U (b U _) = d.hom.app U (b U x)
      rw [hb_vadd, _root_.map_add, hom_app_hom_app_of_comp_eq_zero w, add_zero])
  refine ⟨s, ⟨Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun x ↦ ⟨b U x, hs U x⟩
      naturality U V f := ?_ }) fun U a x ↦ Subtype.ext (hb_vadd U a x)⟩⟩
  ext x
  exact Subtype.ext (hb_nat f x).symm

end Surjective

section Main

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

variable (G) in
/-- **Torsors and first cohomology.** For an abelian sheaf `G` on a site with a terminal object
`T`, the isomorphism classes of `G`-torsors are in bijection with `H¹(G)`, by a bijection under
which a torsor has class `0` exactly when it has a global section.

Choose `0 → G → I → Q → 0` with `I` injective (`lem-galois-flasque`), so that `H¹(G)` is the
cokernel of `d_T : Γ(I) → Γ(Q)`, and send the class of `s ∈ Γ(Q)` to the lifting torsor
`P_s`.
(blueprint: `thm-galois-torsor-h1`) -/
theorem exists_quotientEquiv_H_one {T : C} (hT : IsTerminal T) :
    ∃ c : _root_.Quotient (Torsor.setoid (G := G)) ≃ H G 1,
      ∀ P : Torsor G, c ⟦P⟧ = 0 ↔ Nonempty (P.sheaf.obj.obj (op T)) := by
  obtain ⟨I, Q, ι, d, w, hS, hI, -, ⟨e⟩⟩ := exists_shortExact_injective_addEquiv_H_one hT G
  let Φ : Q.obj.obj (op T) ⧸ (d.hom.app (op T)).hom.range →
      _root_.Quotient (Torsor.setoid (G := G)) :=
    _root_.Quotient.lift (fun s ↦ ⟦lifts hT hS s⟧) fun s s' h ↦ by
      obtain ⟨x, hx⟩ := (QuotientAddGroup.leftRel_apply).1 h
      have := lifts_equiv_lifts_add hT hS s x
      rw [hx, add_neg_cancel_left] at this
      exact _root_.Quotient.sound this
  have hΦ : ∀ s, Φ (QuotientAddGroup.mk s) = ⟦lifts hT hS s⟧ := fun _ ↦ rfl
  have hΦb : Function.Bijective Φ := by
    refine ⟨fun s s' h ↦ ?_, fun P ↦ ?_⟩
    · induction s using QuotientAddGroup.induction_on with | H s => ?_
      induction s' using QuotientAddGroup.induction_on with | H s' => ?_
      rw [hΦ, hΦ] at h
      obtain ⟨x, hx⟩ := exists_hom_app_eq_sub_of_lifts_equiv hT hS (_root_.Quotient.exact h)
      exact QuotientAddGroup.eq.2 ⟨x, hx.trans (neg_add_eq_sub _ _).symm⟩
    · induction P using _root_.Quotient.inductionOn with | h P => ?_
      obtain ⟨s, hs⟩ := exists_equiv_lifts hT hS P
      exact ⟨QuotientAddGroup.mk s, _root_.Quotient.sound (Setoid.symm hs)⟩
  let Ψ := Equiv.ofBijective Φ hΦb
  refine ⟨Ψ.symm.trans e.symm.toEquiv, fun P ↦ ?_⟩
  obtain ⟨s, hs⟩ := exists_equiv_lifts hT hS P
  have hP : (⟦P⟧ : _root_.Quotient (Torsor.setoid (G := G))) = Ψ (QuotientAddGroup.mk s) :=
    _root_.Quotient.sound hs
  rw [Equiv.trans_apply, hP, Equiv.symm_apply_apply]
  change e.symm _ = 0 ↔ _
  rw [AddEquivClass.map_eq_zero_iff, QuotientAddGroup.eq_zero_iff, nonempty_iff_of_equiv hs,
    nonempty_lifts_iff]
  rfl

end Main

end Torsor

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **Extensions and torsors.** For a sheaf `G` of abelian groups on a site, the group
`Ext¹(ℤ, G)` of extensions `0 → G → E → ℤ → 0` is in bijection with the set of isomorphism
classes of `G`-torsors. The canonical bijection sends an extension `E` with projection
`π : E → ℤ` to the torsor `π⁻¹(1)`; its inverse sends `T` to `⊔_{n ∈ ℤ} T^{⊗ n}`.

Only the existence of a bijection is recorded. The proof is `sorry`.
(blueprint: `lem-sc-ext-torsor`) -/
theorem nonempty_equiv_ext_torsor (G : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (Abelian.Ext ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ))) G 1 ≃ _root_.Quotient (Torsor.setoid (G := G))) :=
  sorry

/-- **First cohomology classifies torsors.** For a sheaf `G` of abelian groups on a site,
`H¹(G)` is in bijection with the set of isomorphism classes of `G`-torsors: it is
`Ext¹(ℤ, G)`, to which `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor` applies.

The vanishing direction is also proved directly, without torsors, in
`CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`.
(blueprint: `lem-sc-torsor-h1`) -/
theorem nonempty_equiv_H_one_torsor (G : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (H G 1 ≃ _root_.Quotient (Torsor.setoid (G := G))) :=
  nonempty_equiv_ext_torsor G

/-- `H¹(G)` vanishes if and only if every `G`-torsor is trivial. -/
theorem subsingleton_H_one_iff (G : Sheaf J AddCommGrpCat.{w}) :
    Subsingleton (H G 1) ↔ ∀ T : Torsor G, T ≈ Torsor.trivial G := by
  obtain ⟨e⟩ := nonempty_equiv_H_one_torsor G
  rw [e.subsingleton_congr]
  refine ⟨fun h T ↦ _root_.Quotient.exact (Subsingleton.elim (h := h) ⟦T⟧ ⟦Torsor.trivial G⟧),
    fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  induction a using _root_.Quotient.inductionOn
  induction b using _root_.Quotient.inductionOn
  exact _root_.Quotient.sound (Setoid.trans (h _) (Setoid.symm (h _)))

end CategoryTheory.Sheaf
