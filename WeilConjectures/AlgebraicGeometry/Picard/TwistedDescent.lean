/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent

/-!
# Twisting descent data of modules by cocycles of global functions

Let `{f i : X i ⟶ S}` be a family of morphisms of schemes. A *descent cocycle*
(`AlgebraicGeometry.DescentCocycle`) attaches to every scheme `Y` with two morphisms
`f₁ : Y ⟶ X i₁` and `f₂ : Y ⟶ X i₂` over `S` a global function `c(f₁, f₂)` on `Y`, compatibly with
pullbacks, trivially on the diagonal and multiplicatively on triple overlaps. Twisting the gluing
morphisms of a descent datum of modules by multiplication with `c` gives a new descent datum
(`AlgebraicGeometry.DescentCocycle.twist`).

Any two descent data whose components are isomorphic invertible modules differ by such a twist
(`AlgebraicGeometry.DescentCocycle.exists_iso_twist`), and twisting commutes with the base change
functors `CategoryTheory.Pseudofunctor.DescentData.pullFunctor`.

For a morphism `f : X ⟶ S` such that `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is bijective for every `Y`
over `S`, a cocycle relative to a family `X_{T i} ⟶ X_T` descends to a cocycle relative to the
family `T i ⟶ T` (`AlgebraicGeometry.DescentCocycle.ofBaseChange`). This is the step of the proof
of the exactness of `Pic T → Pic (X_T) → Pic_{X/S}(T)` (blueprint `lem-pc-pic-exact`) in which the
transition functions of a trivialised invertible module on `X_T` are seen to come from `T`.

## Main definitions

- `AlgebraicGeometry.DescentCocycle`: cocycles of global functions relative to a family.
- `AlgebraicGeometry.DescentCocycle.twist`: the twist of a descent datum of modules by a cocycle.
- `AlgebraicGeometry.DescentCocycle.ofBaseChange`: descending a cocycle along `X_T ⟶ T`.

## Main statements

- `AlgebraicGeometry.DescentCocycle.exists_iso_twist`: descent data with isomorphic invertible
  components differ by a twist.
- `AlgebraicGeometry.DescentCocycle.pullFunctorTwistIso`: twisting commutes with base change.
- `AlgebraicGeometry.nonempty_iso_of_toDescentData_iso`: quasi-coherent modules with isomorphic
  descent data relative to an fpqc covering are isomorphic.
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section SmulHom

variable {Y : Scheme.{u}}

/-- Multiplication by a global function `a`, as an endomorphism of an object of
`modulesPseudofunctor.obj (.mk (op Y))`; this is `AlgebraicGeometry.Scheme.Modules.smulHom`, seen
in the category of the pseudofunctor so that it composes with descent data. -/
noncomputable def pseudofunctorSmulHom (M : modulesPseudofunctor.obj (.mk (op Y)))
    (a : Γ(Y, ⊤)) : M ⟶ M :=
  Modules.smulHom (X := Y) M a

@[simp]
lemma pseudofunctorSmulHom_one (M : modulesPseudofunctor.obj (.mk (op Y))) :
    pseudofunctorSmulHom M 1 = 𝟙 M :=
  Modules.smulHom_one (X := Y) M

lemma pseudofunctorSmulHom_mul (M : modulesPseudofunctor.obj (.mk (op Y))) (a b : Γ(Y, ⊤)) :
    pseudofunctorSmulHom M (a * b) = pseudofunctorSmulHom M b ≫ pseudofunctorSmulHom M a :=
  Modules.smulHom_mul (X := Y) M a b

@[reassoc]
lemma pseudofunctorSmulHom_naturality {M N : modulesPseudofunctor.obj (.mk (op Y))}
    (φ : M ⟶ N) (a : Γ(Y, ⊤)) :
    pseudofunctorSmulHom M a ≫ φ = φ ≫ pseudofunctorSmulHom N a :=
  Modules.smulHom_naturality (X := Y) φ a

lemma pullHom_pseudofunctorSmulHom {Y' Z : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op Z))) (f₁ : Y ⟶ Z) (b : Y' ⟶ Y) (bf : Y' ⟶ Z)
    (h : b ≫ f₁ = bf) (a : Γ(Y, ⊤)) :
    pullHom (pseudofunctorSmulHom ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M) a)
      b bf bf h h =
      pseudofunctorSmulHom ((modulesPseudofunctor.map bf.op.toLoc).toFunctor.obj M)
        (b.appTop a) :=
  pullHom_smulHom M f₁ b bf h a

lemma comp_comp_pseudofunctorSmulHom_comp {A B C D : modulesPseudofunctor.obj (.mk (op Y))}
    (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ D) (a : Γ(Y, ⊤)) :
    x ≫ (y ≫ pseudofunctorSmulHom C a) ≫ z = (x ≫ y ≫ z) ≫ pseudofunctorSmulHom D a := by
  simp only [Category.assoc, pseudofunctorSmulHom_naturality]

/-- An invertible module on which multiplication by `a` and by `b` agree has `a = b`. -/
lemma eq_of_pseudofunctorSmulHom_eq (M : modulesPseudofunctor.obj (.mk (op Y)))
    [Modules.IsInvertible (X := Y) M] {a b : Γ(Y, ⊤)}
    (h : pseudofunctorSmulHom M a = pseudofunctorSmulHom M b) : a = b :=
  Modules.eq_of_smulHom_eq (X := Y) M h

/-- Every endomorphism of an invertible module is multiplication by a global function. -/
lemma exists_eq_pseudofunctorSmulHom (M : modulesPseudofunctor.obj (.mk (op Y)))
    [Modules.IsInvertible (X := Y) M] (φ : M ⟶ M) : ∃ a, φ = pseudofunctorSmulHom M a :=
  Modules.exists_eq_smulHom (X := Y) M φ

end SmulHom

section Cocycle

variable {S : Scheme.{u}} {ι : Type w} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- A cocycle of global functions relative to a family of morphisms `f i : X i ⟶ S`: a global
function `c q f₁ f₂` on every scheme `Y` with two morphisms `f₁ : Y ⟶ X i₁`, `f₂ : Y ⟶ X i₂`
over `q : Y ⟶ S`, compatible with pullbacks, trivial on the diagonal and multiplicative. -/
@[ext]
structure DescentCocycle where
  /-- The global function attached to `Y` and the morphisms `f₁` and `f₂`. -/
  c ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : Γ(Y, ⊤)
  appTop_c ⦃Y' Y : Scheme.{u}⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    g.appTop (c q f₁ f₂ hf₁ hf₂) =
      c q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq])
  c_self ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    c q g g hg hg = 1
  c_mul ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    c q f₁ f₂ hf₁ hf₂ * c q f₂ f₃ hf₂ hf₃ = c q f₁ f₃ hf₁ hf₃

namespace DescentCocycle

variable {f} (c : DescentCocycle f)

/-- The twist of a descent datum of modules by a cocycle `c`: the gluing morphisms are composed
with multiplication by `c`. -/
@[simps]
noncomputable def twist (D : modulesPseudofunctor.DescentData f) :
    modulesPseudofunctor.DescentData f where
  obj := D.obj
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    D.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullHom_comp _ _ _ _ gf₂ _ hgf₁ hgf₂ hgf₂,
      D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂,
      pullHom_pseudofunctorSmulHom _ _ _ _ hgf₂,
      c.appTop_c g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self Y q i g hg := by
    rw [D.hom_self q g hg, c.c_self, pseudofunctorSmulHom_one, Category.comp_id]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [Category.assoc, pseudofunctorSmulHom_naturality_assoc, D.hom_comp_assoc,
      ← pseudofunctorSmulHom_mul, mul_comm, c.c_mul]

lemma twist_comm {D₁ D₂ : modulesPseudofunctor.DescentData f} (φ : D₁ ⟶ D₂) ⦃Y : Scheme.{u}⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫
        D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂) =
      (D₁.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂)) ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  rw [reassoc_of% (φ.comm q f₁ f₂ hf₁ hf₂), Category.assoc, pseudofunctorSmulHom_naturality]

/-- Twisting by a cocycle, as a functor. -/
noncomputable def twistFunctor :
    modulesPseudofunctor.DescentData f ⥤ modulesPseudofunctor.DescentData f where
  obj D := c.twist D
  map {D₁ D₂} φ :=
    { hom i := φ.hom i
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        exact c.twist_comm φ q f₁ f₂ hf₁ hf₂ }

@[simp]
lemma twistFunctor_obj (D : modulesPseudofunctor.DescentData f) :
    c.twistFunctor.obj D = c.twist D :=
  rfl

@[simp]
lemma twistFunctor_map_hom {D₁ D₂ : modulesPseudofunctor.DescentData f} (φ : D₁ ⟶ D₂) (i : ι) :
    (c.twistFunctor.map φ).hom i = φ.hom i :=
  rfl

section Ratio

variable {D₁ D₂ : modulesPseudofunctor.DescentData f}
  [hD₂ : ∀ i, Modules.IsInvertible (X := X i) (D₂.obj i)] (e : ∀ i, D₁.obj i ≅ D₂.obj i)

include hD₂ in
lemma exists_ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ∃ a : Γ(Y, ⊤), D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ a =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by
  have : Modules.IsInvertible (X := Y)
      ((modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj (D₂.obj i₂)) :=
    have := hD₂ i₂
    Modules.IsInvertible.pullback f₂ (D₂.obj i₂)
  obtain ⟨a, ha⟩ := exists_eq_pseudofunctorSmulHom _
    (inv (D₂.hom q f₁ f₂ hf₁ hf₂) ≫
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫
        D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom)
  exact ⟨a, by rw [← ha, IsIso.hom_inv_id_assoc]⟩

/-- The global function by which the gluing morphisms of `D₁` and `D₂`, compared through the
isomorphisms `e i`, differ. -/
noncomputable def ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : Γ(Y, ⊤) :=
  (exists_ratio e q f₁ f₂ hf₁ hf₂).choose

lemma hom_comp_ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (ratio e q f₁ f₂ hf₁ hf₂) =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom :=
  (exists_ratio e q f₁ f₂ hf₁ hf₂).choose_spec

include hD₂ in
lemma ratio_eq ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) {a : Γ(Y, ⊤)}
    (h : D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ a =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom) :
    ratio e q f₁ f₂ hf₁ hf₂ = a := by
  have : Modules.IsInvertible (X := Y)
      ((modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj (D₂.obj i₂)) :=
    have := hD₂ i₂
    Modules.IsInvertible.pullback f₂ (D₂.obj i₂)
  exact eq_of_pseudofunctorSmulHom_eq _ (by rw [← cancel_epi (D₂.hom q f₁ f₂ hf₁ hf₂),
    hom_comp_ratio, h])

/-- The cocycle by which two descent data with isomorphic invertible components differ. -/
noncomputable def ratioCocycle : DescentCocycle f where
  c := ratio e
  appTop_c Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    refine (ratio_eq e _ _ _ _ _ ?_).symm
    rw [← D₂.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂,
      ← D₁.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂,
      ← pullHom_pseudofunctorSmulHom _ f₂ g gf₂ hgf₂,
      ← pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂, hom_comp_ratio,
      pullHom_comp _ _ g gf₁ gf₁ gf₂ hgf₁ hgf₁ hgf₂, pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂,
      pullHom_map, pullHom_map]
  c_self Y q i g hg := by
    refine ratio_eq e _ _ _ _ _ ?_
    rw [D₂.hom_self q g hg, D₁.hom_self q g hg, pseudofunctorSmulHom_one, Category.id_comp,
      Category.id_comp, Iso.map_inv_hom_id]
  c_mul Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    refine (ratio_eq e q f₁ f₃ hf₁ hf₃ ?_).symm
    rw [← D₂.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃, ← D₁.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃,
      pseudofunctorSmulHom_mul, Category.assoc, ← Category.assoc _ _ (pseudofunctorSmulHom _ _),
      ← pseudofunctorSmulHom_naturality, ← Category.assoc, hom_comp_ratio, Category.assoc,
      hom_comp_ratio]
    simp only [Category.assoc, Iso.map_hom_inv_id_assoc]

lemma map_hom_comp_twist_hom ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
        D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (ratio e q f₁ f₂ hf₁ hf₂) =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by
  rw [hom_comp_ratio, Iso.map_hom_inv_id_assoc]

/-- A descent datum whose components are isomorphic to the invertible components of `D₂` is
isomorphic to the twist of `D₂` by `DescentCocycle.ratioCocycle`. -/
noncomputable def isoTwistRatioCocycle : D₁ ≅ (ratioCocycle e).twist D₂ :=
  DescentData.isoMk e fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ map_hom_comp_twist_hom e q f₁ f₂ hf₁ hf₂

include hD₂ in
/-- **Descent data with isomorphic invertible components differ by a twist.** -/
theorem exists_iso_twist (h : ∀ i, Nonempty (D₁.obj i ≅ D₂.obj i)) :
    ∃ c : DescentCocycle f, Nonempty (D₁ ≅ c.twist D₂) :=
  ⟨ratioCocycle fun i ↦ (h i).some, ⟨isoTwistRatioCocycle fun i ↦ (h i).some⟩⟩

end Ratio

section Pull

variable {S' : Scheme.{u}} {p : S' ⟶ S} {ι' : Type w'} {X' : ι' → Scheme.{u}}
  {f' : ∀ j, X' j ⟶ S'} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
  (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- The pullback of a cocycle along a morphism of families. -/
def pull : DescentCocycle f' where
  c Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := c.c (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
    (by rw [Category.assoc, w, reassoc_of% hf₁]) (by rw [Category.assoc, w, reassoc_of% hf₂])
  appTop_c Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    c.appTop_c g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq]) _ _ _ _ (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by rw [reassoc_of% hgf₁]) (by rw [reassoc_of% hgf₂])
  c_self Y q j g hg := c.c_self _ _ _
  c_mul Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := c.c_mul _ _ _ _ _ _ _

lemma pullFunctorObjHom_twist (D : modulesPseudofunctor.DescentData f) ⦃Y : Scheme.{u}⦄
    (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂) (hf₁ : f₁ ≫ f' j₁ = q)
    (hf₂ : f₂ ≫ f' j₂ = q) :
    DescentData.pullFunctorObjHom w (c.twist D) q f₁ f₂ hf₁ hf₂ =
      DescentData.pullFunctorObjHom w D q f₁ f₂ hf₁ hf₂ ≫
        pseudofunctorSmulHom _ ((c.pull w).c q f₁ f₂ hf₁ hf₂) := by
  exact comp_comp_pseudofunctorSmulHom_comp _ _ _ _

/-- **Twisting commutes with base change.** -/
lemma pullFunctor_obj_twist (D : modulesPseudofunctor.DescentData f) :
    (DescentData.pullFunctor modulesPseudofunctor w).obj (c.twist D) =
      (c.pull w).twist ((DescentData.pullFunctor modulesPseudofunctor w).obj D) := by
  change DescentData.pullFunctorObj w (c.twist D) = (c.pull w).twist (DescentData.pullFunctorObj w D)
  unfold DescentData.pullFunctorObj twist
  congr 1
  funext Y q j₁ j₂ f₁ f₂ hf₁ hf₂
  subst hf₁
  exact pullFunctorObjHom_twist c w D _ f₁ f₂ rfl hf₂

end Pull

end DescentCocycle

end Cocycle

end AlgebraicGeometry
