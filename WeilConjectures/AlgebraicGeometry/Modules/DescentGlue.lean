/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FpqcSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-!
# The module of compatible sections of a descent datum

Let `f a : W a ⟶ S` be a family of morphisms of schemes indexed by `a : J` with `J : Type u`, and
let `D` be a descent datum for `modulesPseudofunctor` relative to `f`. We construct the
`𝒪_S`-module `AlgebraicGeometry.Scheme.Modules.descentGlue D` whose sections over `V` are the
families `(s a)_a` of sections `s a ∈ Γ(D a, f a ⁻¹ᵁ V)` which are compatible: for every scheme
`Y` with morphisms `y₁ : Y ⟶ W a`, `y₂ : Y ⟶ W b` over `S`, the descent datum identifies the
pullbacks of `s a` and `s b` to `Y`. There are counit morphisms `(f a)^* (descentGlue D) ⟶ D a`,
forming a morphism of descent data `AlgebraicGeometry.Scheme.Modules.glueToDescentData`.

The compatibility is required for all test schemes `Y` (this is a proposition, so there is no
size issue), which avoids choosing fibre products, and on all opens `O` of `Y` contained in both
preimages of `V`, which avoids transporting sections along equalities of opens.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} {J : Type u} {W : J → Scheme.{u}} {f : ∀ a, W a ⟶ S}
  (D : modulesPseudofunctor.DescentData f)

/-- The object `D.obj a` of a descent datum, as a sheaf of modules on `W a`. -/
abbrev descentObj (a : J) : (W a).Modules := D.obj a

/-- Two sections `s` of `D a` and `t` of `D b` over the preimages of `V` are compatible if for
all `y₁ : Y ⟶ W a`, `y₂ : Y ⟶ W b` over `S` the descent datum `D.hom` sends the pullback of `s`
to the pullback of `t`, on every open of `Y` contained in both preimages of `V`. -/
def DescentCompat (V : S.Opens) {a b : J} (s : Γ(descentObj D a, f a ⁻¹ᵁ V))
    (t : Γ(descentObj D b, f b ⁻¹ᵁ V)) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (y₁ : Y ⟶ W a) (y₂ : Y ⟶ W b) (h : y₁ ≫ f a = y₂ ≫ f b) (O : Y.Opens)
    (h₁ : O ≤ y₁ ⁻¹ᵁ f a ⁻¹ᵁ V) (h₂ : O ≤ y₂ ⁻¹ᵁ f b ⁻¹ᵁ V),
    (D.hom (y₁ ≫ f a) y₁ y₂ rfl h.symm).app O
      (((pullback y₁).obj (descentObj D a)).presheaf.map (homOfLE h₁).op
        (pullbackUnitApp y₁ _ _ s)) =
      ((pullback y₂).obj (descentObj D b)).presheaf.map (homOfLE h₂).op
        (pullbackUnitApp y₂ _ _ t)

/-- The compatible families of sections of `D` over `V`. -/
def descentSections (V : S.Opens) :
    AddSubgroup (∀ a, Γ(descentObj D a, f a ⁻¹ᵁ V)) where
  carrier := {s | ∀ a b, DescentCompat D V (s a) (s b)}
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry

/-- The `𝒪_S`-module of compatible families of sections of a descent datum `D`. -/
noncomputable def descentGlue (D : modulesPseudofunctor.DescentData f) : S.Modules :=
  sorry

/-- The component at `a` of a section of `descentGlue D`. -/
noncomputable def glueVal {V : S.Opens} (a : J) :
    Γ(descentGlue D, V) →+ Γ(descentObj D a, f a ⁻¹ᵁ V) :=
  sorry

variable {D}

lemma glueVal_compat {V : S.Opens} (s : Γ(descentGlue D, V)) (a b : J) :
    DescentCompat D V (glueVal D a s) (glueVal D b s) :=
  sorry

lemma glueVal_ext {V : S.Opens} {s t : Γ(descentGlue D, V)}
    (h : ∀ a, glueVal D a s = glueVal D a t) : s = t :=
  sorry

/-- Every compatible family of sections is a section of `descentGlue D`. -/
lemma exists_glueVal_eq {V : S.Opens} (s : ∀ a, Γ(descentObj D a, f a ⁻¹ᵁ V))
    (hs : ∀ a b, DescentCompat D V (s a) (s b)) :
    ∃ t : Γ(descentGlue D, V), ∀ a, glueVal D a t = s a :=
  sorry

lemma glueVal_smul {V : S.Opens} (r : Γ(S, V)) (s : Γ(descentGlue D, V)) (a : J) :
    glueVal D a (r • s) = (f a).app V r • glueVal D a s :=
  sorry

lemma glueVal_presheaf_map {V V' : S.Opens} (i : V' ⟶ V) (s : Γ(descentGlue D, V)) (a : J) :
    glueVal D a ((descentGlue D).presheaf.map i.op s) =
      (descentObj D a).presheaf.map (homOfLE ((f a).preimage_mono i.le)).op
        (glueVal D a s) :=
  sorry

variable (D) in
/-- The counit `(f a)^* (descentGlue D) ⟶ D a`, adjoint to the projection to the `a`-th
component. -/
noncomputable def glueCounit (a : J) :
    (pullback (f a)).obj (descentGlue D) ⟶ descentObj D a :=
  sorry

lemma glueCounit_app_pullbackUnitApp (a : J) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    (glueCounit D a).app (f a ⁻¹ᵁ V) (pullbackUnitApp (f a) _ V s) = glueVal D a s :=
  sorry

variable (D) in
/-- The counits `(f a)^* (descentGlue D) ⟶ D a` form a morphism of descent data. -/
noncomputable def glueToDescentData :
    (modulesPseudofunctor.toDescentData f).obj (descentGlue D) ⟶ D :=
  sorry

lemma glueToDescentData_hom (a : J) : (glueToDescentData D).hom a = glueCounit D a :=
  sorry

/-- The morphism `P ⟶ descentGlue D` induced by a morphism of descent data
`φ : (toDescentData f).obj P ⟶ D`: a section `p` is sent to the family `φ a (f a ^* p)`. -/
noncomputable def toGlue {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) : P ⟶ descentGlue D :=
  sorry

lemma glueVal_toGlue_app {P : S.Modules} (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D)
    {V : S.Opens} (p : Γ(P, V)) (a : J) :
    glueVal D a ((toGlue φ).app V p) = (φ.hom a).app _ (pullbackUnitApp (f a) P V p) :=
  sorry

lemma pullback_map_toGlue_comp_glueCounit {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) (a : J) :
    (pullback (f a)).map (toGlue φ) ≫ glueCounit D a = φ.hom a :=
  sorry

end AlgebraicGeometry.Scheme.Modules
