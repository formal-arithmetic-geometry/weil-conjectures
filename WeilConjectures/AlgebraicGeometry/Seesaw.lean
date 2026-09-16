/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The seesaw theorem

Let `X` be a proper variety over a field `K`, let `T` be a reduced `K`-scheme of finite type and
let `L` be a line bundle on `X × T` whose restriction `L_t` to the fibre `X_t` is trivial for
every closed point `t` of `T`. The **seesaw theorem** says that `M := p_{T*} L` is again a line
bundle and that the counit `ε : p_T^* M ⟶ L` of the adjunction `p_T^* ⊣ p_{T*}` is an
isomorphism: `L` is the pullback of a line bundle on the base. Its **triviality form** adds the
hypothesis that `L` is trivial on one slice `{x₀} × T` and concludes that `L` itself is trivial.

The two inputs which are `sorry` by design are consumed as black boxes: the semicontinuity of
`h⁰` (`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrankFiberSections`) and Grauert's
theorem (`AlgebraicGeometry.Scheme.Modules.invertible_pushforward_of_finrankFiberSections_eq_one`
and `AlgebraicGeometry.Scheme.Modules.isIso_fiberBaseChangeMap_of_finrankFiberSections_eq`).
Nothing else in this file is `sorry`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.flatOver_of_invertible` and
  `AlgebraicGeometry.Scheme.Modules.isCoherent_of_invertible` (blueprint
  `lem:cube-projection-proper-flat` (4)): **a line bundle on the source of a flat morphism is
  coherent and flat over the base.**
- `AlgebraicGeometry.Scheme.Modules.finrankFiberSections_pullbackSnd_eq_one` (blueprint
  `lem:cube-h0-constant`): **`h⁰` is identically one** on a `K`-scheme of finite type `T`, as
  soon as the restriction of `L` to the fibre over every closed point of `T` is trivial.
- `AlgebraicGeometry.Scheme.Modules.isIso_counit_pullbackSnd` together with
  `AlgebraicGeometry.Scheme.Modules.invertible_pushforward_pullbackSnd` (blueprint
  `thm:cube-seesaw`): **the seesaw theorem.**
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_pullbackSnd` (blueprint
  `cor:cube-seesaw-trivial`): **the triviality form of the seesaw theorem.**

The last three are also proved in the generality they are used in: for an arbitrary proper
morphism `f : W ⟶ T` over a reduced Noetherian Jacobson base, see
`AlgebraicGeometry.Scheme.Modules.finrankFiberSections_eq_one_of_isClosed_singleton`,
`AlgebraicGeometry.Scheme.Modules.isIso_counit_of_restrictToFiber_iso` and
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_of_section`.

## Implementation notes

* **Closed points, not `K`-rational points.** The blueprint states the hypothesis "`L_t` is
  trivial" for `t ∈ T(k)`, over an algebraically closed `k`; the statements below ask for it at
  every *closed point* of `T` instead. Over an algebraically closed field the two agree
  (`AlgebraicGeometry.pointEquivClosedPoint`), and the closed-point form is what the Jacobson
  argument uses and what holds over any field.
* Along the way the file proves that **restricting to an open subscheme does not change
  stalks**, as a module over the local ring of the ambient scheme
  (`AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfRestrictIso`), and that **the stalk of
  the structure sheaf viewed as a sheaf of modules is the local ring**
  (`AlgebraicGeometry.Scheme.Modules.stalkStructureModulesLinearEquiv`). Both belong in the
  mirror file `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, which other pull
  requests currently own; they are kept here to avoid two copies of one declaration.
* `SheafOfModules.Invertible` is a `Prop`-valued `def`, not a class, so every statement below
  takes it as an explicit hypothesis `hL : L.Invertible`. In particular
  `AlgebraicGeometry.Scheme.Modules.flatOver_of_invertible` is a theorem and not an instance.

## Blueprint

`lem:cube-projection-proper-flat` (4), `lem:cube-h0-constant`, `thm:cube-seesaw` and
`cor:cube-seesaw-trivial` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-! ### Stalks and restriction to an open subscheme -/

section StalkRestriction

variable {Y W : Scheme.{u}}

/-- The stalk map of an open immersion `f` sends the germ of the section corresponding to
`a ∈ Γ(Y, U)` under `Γ(W, f(U)) ≅ Γ(Y, U)` to the germ of `a`. -/
lemma stalkMap_germ_appIso_inv (f : Y ⟶ W) [IsOpenImmersion f] (y : Y) (U : Y.Opens)
    (hy : y ∈ U) (a : Γ(Y, U)) :
    f.stalkMap y (W.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hy, rfl⟩ ((f.appIso U).inv a)) =
      Y.presheaf.germ U y hy a := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact Y.presheaf.germ_res_apply _ y _ a

/-- **Restriction along an open immersion does not change stalks**, as an additive
equivalence. -/
noncomputable def restrictStalkEquiv (f : Y ⟶ W) [IsOpenImmersion f] (y : Y) (M : W.Modules) :
    ((restrictFunctor f).obj M).presheaf.stalk y ≃+ M.presheaf.stalk (f y) where
  toFun := (restrictStalkNatIso f y).hom.app M
  invFun := (restrictStalkNatIso f y).inv.app M
  left_inv z := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
    rfl
  right_inv z := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
    rfl
  map_add' _ _ := map_add _ _ _

@[simp]
lemma restrictStalkEquiv_germ (f : Y ⟶ W) [IsOpenImmersion f] (y : Y) (M : W.Modules)
    {U : Y.Opens} (hyU : y ∈ U) (s : Γ((restrictFunctor f).obj M, U)) :
    restrictStalkEquiv f y M (((restrictFunctor f).obj M).presheaf.germ U y hyU s) =
      M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ s :=
  ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app f y M hyU) s

/-- The comparison of stalks under restriction along an open immersion is semilinear over the
stalk map of the open immersion. -/
lemma restrictStalkEquiv_smul (f : Y ⟶ W) [IsOpenImmersion f] (y : Y) (M : W.Modules)
    (r : Y.presheaf.stalk y) (z : ((restrictFunctor f).obj M).presheaf.stalk y) :
    restrictStalkEquiv f y M (r • z) = inv (f.stalkMap y) r • restrictStalkEquiv f y M z := by
  obtain ⟨V, hyV, a, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨U, hUV, hyU, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (C := Ab.{u})
    ((restrictFunctor f).obj M).presheaf z hyV
  rw [← Y.presheaf.germ_res_apply (homOfLE hUV) y hyU a, ← germ_smul, restrictStalkEquiv_germ,
    restrictStalkEquiv_germ]
  have key : ∀ b : Γ(Y, U),
      M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ (b • s) =
        inv (f.stalkMap y) (Y.presheaf.germ U y hyU b) •
          M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ s := by
    intro b
    have hsmul : b • s =
        (f.appIso U).inv b • (show ToType Γ(M, f ''ᵁ U) from s) := rfl
    have hscal : inv (f.stalkMap y) (Y.presheaf.germ U y hyU b) =
        W.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ ((f.appIso U).inv b) := by
      rw [← stalkMap_germ_appIso_inv f y U hyU b, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
      rfl
    rw [hsmul, germ_smul M (f y) (⟨y, hyU, rfl⟩ : f y ∈ f ''ᵁ U) ((f.appIso U).inv b)
        (show ToType Γ(M, f ''ᵁ U) from s), hscal]
  exact key _

variable (f : Y ⟶ W) [IsOpenImmersion f] (y : Y)

lemma restrictStalkEquiv_symm_smul (M : W.Modules) (r : W.presheaf.stalk (f y))
    (z : M.presheaf.stalk (f y)) :
    (restrictStalkEquiv f y M).symm (r • z) =
      f.stalkMap y r • (restrictStalkEquiv f y M).symm z := by
  apply (restrictStalkEquiv f y M).injective
  rw [AddEquiv.apply_symm_apply, restrictStalkEquiv_smul, AddEquiv.apply_symm_apply,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
  rfl

/-- The linear map on stalks induced by a morphism between the restrictions of two sheaves of
modules to an open subscheme. -/
noncomputable def stalkMapOfRestrictHom {M N : W.Modules}
    (φ : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    M.presheaf.stalk (f y) →ₗ[W.presheaf.stalk (f y)] N.presheaf.stalk (f y) where
  toFun z := restrictStalkEquiv f y N
    (PresheafOfModules.stalkMapₗ φ.val y ((restrictStalkEquiv f y M).symm z))
  map_add' z z' := by simp only [map_add]
  map_smul' r z := by
    rw [RingHom.id_apply, restrictStalkEquiv_symm_smul, LinearMap.map_smul,
      restrictStalkEquiv_smul, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
    rfl

lemma stalkMapOfRestrictHom_comp {M N P : W.Modules}
    (φ : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N)
    (ψ : (restrictFunctor f).obj N ⟶ (restrictFunctor f).obj P)
    (z : M.presheaf.stalk (f y)) :
    stalkMapOfRestrictHom f y ψ (stalkMapOfRestrictHom f y φ z) =
      stalkMapOfRestrictHom f y (φ ≫ ψ) z := by
  simp only [stalkMapOfRestrictHom, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply,
    PresheafOfModules.stalkMapₗ_apply]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  rfl

lemma stalkMapOfRestrictHom_id (M : W.Modules) (z : M.presheaf.stalk (f y)) :
    stalkMapOfRestrictHom f y (𝟙 ((restrictFunctor f).obj M)) z = z := by
  simp only [stalkMapOfRestrictHom, LinearMap.coe_mk, AddHom.coe_mk,
    PresheafOfModules.stalkMapₗ_apply]
  rw [SheafOfModules.id_val, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp

/-- **Two sheaves of modules which agree on a neighbourhood of a point have the same stalk
there**, as a module over the local ring of the ambient scheme. -/
noncomputable def stalkLinearEquivOfRestrictIso {M N : W.Modules}
    (e : (restrictFunctor f).obj M ≅ (restrictFunctor f).obj N) :
    M.presheaf.stalk (f y) ≃ₗ[W.presheaf.stalk (f y)] N.presheaf.stalk (f y) :=
  { stalkMapOfRestrictHom f y e.hom with
    invFun := stalkMapOfRestrictHom f y e.inv
    left_inv z := by
      change stalkMapOfRestrictHom f y e.inv (stalkMapOfRestrictHom f y e.hom z) = z
      rw [stalkMapOfRestrictHom_comp, e.hom_inv_id, stalkMapOfRestrictHom_id]
    right_inv z := by
      change stalkMapOfRestrictHom f y e.hom (stalkMapOfRestrictHom f y e.inv z) = z
      rw [stalkMapOfRestrictHom_comp, e.inv_hom_id, stalkMapOfRestrictHom_id] }

end StalkRestriction

/-! ### The stalk of the structure sheaf as a sheaf of modules -/

section StructureModulesStalk

variable {X : Scheme.{u}}

/-- A multiple of the germ of the unit section of the structure sheaf vanishes exactly when the
multiplier does. -/
lemma smul_germ_oneSection_eq_zero_iff (x : X) (r : X.presheaf.stalk x) :
    r • X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤) = 0 ↔ r = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_smul]⟩
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [germ_oneSection_res x U hxU, ← germ_structureModules_eq_smul x U hxU a,
    show (0 : X.structureModules.presheaf.stalk x)
      = X.structureModules.presheaf.germ U x hxU 0 by simp] at h
  obtain ⟨V, hxV, iVU, _, heq⟩ := X.structureModules.presheaf.germ_eq x hxU hxU _ _ h
  rw [map_zero] at heq
  have hz : X.presheaf.map iVU.op a = 0 := heq
  rw [← X.presheaf.germ_res_apply iVU x hxV a, hz, map_zero]

/-- **The stalk of the structure sheaf, viewed as a sheaf of modules over itself, is the local
ring**, the unit section being a basis. -/
noncomputable def stalkStructureModulesLinearEquiv (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.structureModules.presheaf.stalk x :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x)
      (X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤)))
    ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro r hr
      exact (smul_germ_oneSection_eq_zero_iff x r).1 hr,
    by
      rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range]
      exact span_germ_oneSection x⟩

instance flat_stalk_structureModules (x : X) :
    Module.Flat (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x) :=
  Module.Flat.of_linearEquiv (stalkStructureModulesLinearEquiv X x).symm

end StructureModulesStalk

/-! ### A line bundle is coherent and flat over the base

This is `lem:cube-projection-proper-flat` (4) of the blueprint. -/

section Flatness

variable {W T : Scheme.{u}} {L : W.Modules}

/-- **A line bundle is coherent**: it is locally free, hence quasi-coherent, and of finite
type. -/
theorem isCoherent_of_invertible (hL : L.Invertible) : L.IsCoherent :=
  have := hL.isLocallyFree
  (SheafOfModules.isCoherent_iff L).2 ⟨inferInstance, hL.isFiniteType⟩

/-- **The stalks of a line bundle are free of rank one**, hence flat over the local rings of the
scheme. -/
theorem flat_stalk_of_invertible (hL : L.Invertible) (x : W) :
    Module.Flat (W.presheaf.stalk x) (L.presheaf.stalk x) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hL.exists_restrict_iso_unit x
  have e' : (restrictFunctor V.ι).obj L ≅ (restrictFunctor V.ι).obj W.structureModules :=
    e ≪≫ (restrictUnitIso V.ι).symm
  have key : Module.Flat (W.presheaf.stalk (V.ι ⟨x, hxV⟩)) (L.presheaf.stalk (V.ι ⟨x, hxV⟩)) :=
    Module.Flat.of_linearEquiv (stalkLinearEquivOfRestrictIso V.ι ⟨x, hxV⟩ e')
  exact key

/-- **A line bundle on the source of a flat morphism is flat over the base.** Its stalks are
free over the local rings of the source, which are flat over the local rings of the base. -/
theorem flatOver_of_invertible (hL : L.Invertible) (f : W ⟶ T) [_root_.AlgebraicGeometry.Flat f] :
    L.FlatOver f := by
  refine ⟨fun x ↦ ?_⟩
  let _ := moduleStalkBase L f x
  let _ : Algebra (T.presheaf.stalk (f x)) (W.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have hfs : Module.Flat (T.presheaf.stalk (f x)) (W.presheaf.stalk x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  have hst : IsScalarTower (T.presheaf.stalk (f x)) (W.presheaf.stalk x) (L.presheaf.stalk x) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have := flat_stalk_of_invertible hL x
  exact Module.Flat.trans _ (W.presheaf.stalk x) _

end Flatness

/-! ### Reading a morphism of sheaves of modules on a fibre -/

section Fibres

variable {W T : Scheme.{u}}

@[reassoc]
lemma fiberPullbackIso_hom_naturality (u : W ⟶ T) (x : W) [IsIso (u.residueFieldMap x)]
    {M N : T.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x ≫ (fiberPullbackIso u N x).hom =
      (fiberPullbackIso u M x).hom ≫
        (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).map (fiberMap φ (u x)) :=
  (fiberFunctorPullbackIso u x).hom.naturality φ

/-- **A morphism of sheaves of modules vanishes on the fibre at a point exactly when its
pullback does**, for a morphism inducing an isomorphism on the residue field at that point. -/
lemma fiberMap_pullback_map_eq_zero_iff (u : W ⟶ T) (x : W) [IsIso (u.residueFieldMap x)]
    {M N : T.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x = 0 ↔ fiberMap φ (u x) = 0 := by
  rw [← Preadditive.IsIso.comp_right_eq_zero (fiberMap ((Modules.pullback u).map φ) x)
      (fiberPullbackIso u N x).hom, fiberPullbackIso_hom_naturality,
    Preadditive.IsIso.comp_left_eq_zero, Functor.map_eq_zero_iff]

/-- A morphism of sheaves of modules taking a global section to one with non-zero image in the
fibre at `w` is non-zero on the fibre at `w`. -/
lemma fiberMap_ne_zero_of_fiberMk_ne_zero {Z : Scheme.{u}} {A G : Z.Modules} (ψ : A ⟶ G) (w : Z)
    (τ : Γ(A, ⊤)) (h : fiberMk G w (Hom.app ψ ⊤ τ) ≠ 0) : fiberMap ψ w ≠ 0 := by
  intro h0
  refine h ?_
  rw [← fiberMap_fiberMk ψ w τ, h0]
  simp

/-- **The evaluation map `Γ(W_t, G) ⊗_{κ(t)} 𝒪_{W_t} ⟶ G` is non-zero on the fibre at a point
where some global section of `G` is non-zero.** -/
lemma fiberMap_fiberFreeAdjunction_counit_ne_zero (f : W ⟶ T) (t : T) {G : (f.fiber t).Modules}
    (w : f.fiber t) (σ : Γ(G, ⊤)) (hσ : fiberMk G w σ ≠ 0) :
    fiberMap ((fiberFreeAdjunction f t).counit.app G) w ≠ 0 := by
  refine fiberMap_ne_zero_of_fiberMk_ne_zero _ w
    ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) ?_
  have h := ConcreteCategory.congr_hom ((fiberFreeAdjunction f t).right_triangle_components G) σ
  rw [ConcreteCategory.comp_apply] at h
  rw [show Hom.app ((fiberFreeAdjunction f t).counit.app G) ⊤
      ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) = σ from h]
  exact hσ

/-- **A trivial line bundle has a nowhere vanishing global section.** This is the fibrewise half
of `lem:cube-nowhere-vanishing` of the blueprint, read off from the trivialisation. -/
lemma exists_fiberMk_ne_zero {Z : Scheme.{u}} {G : Z.Modules} (e : G ≅ Z.structureModules) :
    ∃ σ : Γ(G, ⊤), ∀ w : Z, fiberMk G w σ ≠ 0 :=
  ⟨(sectionsEquivOfIsoUnit e).symm 1, fun w ↦ fiberMk_ne_zero_of_isUnit e (by simp) w⟩

end Fibres

/-! ### `h⁰` is identically one -/

section ConstantH0

variable {W T : Scheme.{u}}

/-- **The fibrewise dimension of the global sections of a line bundle is one at a point where
the fibre is trivial**, provided the fibre of `f` there is a proper geometrically integral
scheme over the residue field. -/
theorem finrankFiberSections_eq_one_of_restrictToFiber_iso (f : W ⟶ T) [IsProper f]
    (F : W.Modules) (t : T) [GeometricallyIntegral (f.fiberToSpecResidueField t)]
    (e : (restrictToFiber f t).obj F ≅ (f.fiber t).structureModules) :
    finrankFiberSections f F t = 1 := by
  let _ : (f.fiber t).Over (Spec (.of ↥(T.residueField t))) := ⟨f.fiberToSpecResidueField t⟩
  have hp : IsProper ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (IsProper (f.fiberToSpecResidueField t))
  have hg : GeometricallyIntegral ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField t))
  exact finrank_sections_eq_one_of_iso_unit_of_geometricallyIntegral
    (K := ↥(T.residueField t)) (X := f.fiber t) (L := (restrictToFiber f t).obj F) e

/-- **`h⁰` is identically one.** If the fibrewise dimension of the global sections is one at
every closed point of a Noetherian Jacobson base, then it is one everywhere: the locus
`{h⁰ ≥ 2}` is closed and misses every closed point, hence is empty, and the locus `{h⁰ ≥ 1}` is
closed and contains every closed point, hence is everything.

This is `lem:cube-h0-constant` of the blueprint. -/
theorem finrankFiberSections_eq_one_of_isClosed_singleton [JacobsonSpace T] [IsNoetherian T]
    (f : W ⟶ T) [IsProper f] (F : W.Modules) [F.IsCoherent] [F.FlatOver f]
    (h : ∀ t : T, IsClosed {t} → finrankFiberSections f F t = 1) (t : T) :
    finrankFiberSections f F t = 1 := by
  have hc2 : IsClosed {s : T | 2 ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F 2
  have hc1 : IsClosed {s : T | 1 ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F 1
  have hlt : finrankFiberSections f F t < 2 := by
    by_contra hcon
    obtain ⟨s, hs, hsc⟩ :=
      nonempty_inter_closedPoints (Z := {s : T | 2 ≤ finrankFiberSections f F s})
        ⟨t, not_lt.1 hcon⟩ hc2.isLocallyClosed
    rw [Set.mem_ofPred_eq, h s hsc] at hs
    omega
  have hge : (1 : ℕ) ≤ finrankFiberSections f F t := by
    have hsub : closedPoints T ⊆ {s : T | 1 ≤ finrankFiberSections f F s} :=
      fun x hx ↦ by simp [h x hx]
    have hcl := closure_mono hsub
    rw [closure_closedPoints, hc1.closure_eq] at hcl
    exact hcl (Set.mem_univ t)
  omega

end ConstantH0

/-! ### The seesaw theorem -/

section Seesaw

variable {W T : Scheme.{u}} (f : W ⟶ T) {L : W.Modules}

/-- **The counit is non-zero on the fibre at a point lying over a point where `L` is trivial.**
On the fibre over `t` the counit is, by `lem:cube-counit-fibre` and Grauert's theorem, the
evaluation map of the one-dimensional space `Γ(W_t, L_t)`, and a trivialisation of `L_t`
provides a nowhere vanishing section. -/
lemma fiberMap_counit_ne_zero_of_restrictToFiber_iso [IsReduced T] [IsNoetherian T] [IsProper f]
    (hL : L.Invertible) [L.FlatOver f] (h1 : ∀ s : T, finrankFiberSections f L s = 1) (t : T)
    (e : (restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) (w : W) (hw : f w = t) :
    fiberMap ((pullbackPushforwardAdjunction f).counit.app L) w ≠ 0 := by
  have hcoh : L.IsCoherent := isCoherent_of_invertible hL
  have hM : ((pushforward f).obj L).Invertible :=
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  have hqc : ((Modules.pullback (T.fromSpecResidueField t)).obj
      ((pushforward f).obj L)).IsQuasicoherent :=
    have := (SheafOfModules.Invertible.pullback (T.fromSpecResidueField t) hM).isLocallyFree
    inferInstance
  have hβ : IsIso (fiberBaseChangeMap f L t) :=
    isIso_fiberBaseChangeMap_of_finrankFiberSections_eq f L t h1
  obtain ⟨σ, hσ⟩ := exists_fiberMk_ne_zero e
  obtain ⟨w', hw'⟩ : w ∈ Set.range (f.fiberι t) := by
    rw [f.range_fiberι t]; exact hw
  intro hzero
  rw [← hw', ← fiberMap_pullback_map_eq_zero_iff (f.fiberι t) w'
    ((pullbackPushforwardAdjunction f).counit.app L)] at hzero
  have key := congrArg (fun ψ ↦ fiberMap ψ w') (fiberFreeComparison_comp_map_counit f L t)
  simp only [fiberMap_comp] at key
  rw [hzero, comp_zero] at key
  refine fiberMap_fiberFreeAdjunction_counit_ne_zero f t w' σ (hσ w') ?_
  rw [← Preadditive.IsIso.comp_left_eq_zero
    (fiberMap ((fiberFreeFunctor f t).map (fiberBaseChangeMap f L t)) w')]
  exact key.symm

/-- **The seesaw theorem.** Let `f : W ⟶ T` be a proper morphism over a reduced Noetherian
Jacobson base, let `L` be a line bundle on `W` which is flat over `T` with constant fibrewise
`h⁰ = 1`, and suppose that the restriction of `L` to the fibre over every closed point of `T` is
trivial. Then the counit `ε : f^* f_* L ⟶ L` is an isomorphism.

The direct image `f_* L` is a line bundle by Grauert's theorem, so `ε` is a morphism of line
bundles and it is enough to see that it is non-zero on every fibre. The locus where it vanishes
is closed, its image in `T` is closed because `f` is proper, and that image misses every closed
point of `T`; a non-empty closed subset of a Jacobson space contains a closed point, so the
locus is empty.

This is `thm:cube-seesaw` of the blueprint. -/
theorem isIso_counit_of_restrictToFiber_iso [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app L) := by
  have hM : ((pushforward f).obj L).Invertible :=
    have := isCoherent_of_invertible hL
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  refine isIso_of_forall_fiberMap_ne_zero (SheafOfModules.Invertible.pullback f hM) hL _
    fun w ↦ ?_
  by_contra hw
  have hNclosed :
      IsClosed {v : W | fiberMap ((pullbackPushforwardAdjunction f).counit.app L) v = 0} :=
    isClosed_setOf_fiberMap_eq_zero (SheafOfModules.Invertible.pullback f hM) hL _
  have himg := f.isClosedMap _ hNclosed
  obtain ⟨t, ⟨v, hv, hvt⟩, htc⟩ :=
    nonempty_inter_closedPoints (Z := f.base '' _) ⟨f w, w, hw, rfl⟩ himg.isLocallyClosed
  obtain ⟨e⟩ := htriv t htc
  exact fiberMap_counit_ne_zero_of_restrictToFiber_iso f hL h1 t e v hvt hv

/-- Pulling a sheaf of modules back along `f` and then along a section of `f` gives back the
sheaf. -/
noncomputable def pullbackSectionIso (s : T ⟶ W) (hs : s ≫ f = 𝟙 T) (M : T.Modules) :
    (Modules.pullback s).obj ((Modules.pullback f).obj M) ≅ M :=
  (Modules.pullbackComp s f).app M ≪≫ (Modules.pullbackCongr hs).app M ≪≫
    (Modules.pullbackId T).app M

/-- **The seesaw theorem, triviality form.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isIso_counit_of_restrictToFiber_iso`, if moreover the pullback
of `L` along some section `s` of `f` is trivial, then `L` itself is trivial: the counit
identifies `L` with `f^* (f_* L)`, and pulling that back along `s` identifies `f_* L` with
`s^* L`.

This is `cor:cube-seesaw-trivial` of the blueprint. -/
theorem nonempty_iso_structureModules_of_section [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules))
    (s : T ⟶ W) (hs : s ≫ f = 𝟙 T)
    (hsec : Nonempty ((Modules.pullback s).obj L ≅ T.structureModules)) :
    Nonempty (L ≅ W.structureModules) := by
  obtain ⟨e⟩ := hsec
  have hiso := isIso_counit_of_restrictToFiber_iso f hL h1 htriv
  let ε := asIso ((pullbackPushforwardAdjunction f).counit.app L)
  have hMtriv : (pushforward f).obj L ≅ T.structureModules :=
    (pullbackSectionIso f s hs ((pushforward f).obj L)).symm ≪≫
      (Modules.pullback s).mapIso ε ≪≫ e
  exact ⟨ε.symm ≪≫ (Modules.pullback f).mapIso hMtriv ≪≫ Modules.pullbackUnitIso f⟩

end Seesaw

/-! ### The seesaw theorem for the projection `X × T ⟶ T` -/

section Projection

variable {T : Scheme.{u}} {K : Type u} [Field K] {X : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) (πT : T ⟶ Spec (.of K))

/-- A scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_finiteType [LocallyOfFiniteType πT] [QuasiCompact πT] :
    IsNoetherian T :=
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian πT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace πT
  ⟨⟩

variable [IsProper πX] [GeometricallyIntegral πX] [LocallyOfFiniteType πT] [QuasiCompact πT]
  {L : (Limits.pullback πX πT).Modules} (hL : L.Invertible)

include hL in
/-- **`h⁰` is identically one for a line bundle on `X × T`** which is trivial on the fibre over
every closed point of `T`. This is `lem:cube-h0-constant` of the blueprint. -/
theorem finrankFiberSections_pullbackSnd_eq_one
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (t : T) : finrankFiberSections (Limits.pullback.snd πX πT) L t = 1 :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  have := isCoherent_of_invertible hL
  have := flatOver_of_invertible hL (Limits.pullback.snd πX πT)
  finrankFiberSections_eq_one_of_isClosed_singleton _ L
    (fun s hs ↦ finrankFiberSections_eq_one_of_restrictToFiber_iso _ L s (htriv s hs).some) t

include hL in
/-- **The direct image `p_{T*} L` is a line bundle on `T`.** This is the first half of
`thm:cube-seesaw` of the blueprint, and is Grauert's theorem in rank one. -/
theorem invertible_pushforward_pullbackSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    ((pushforward (Limits.pullback.snd πX πT)).obj L).Invertible :=
  have := isNoetherian_of_finiteType πT
  have := isCoherent_of_invertible hL
  have := flatOver_of_invertible hL (Limits.pullback.snd πX πT)
  invertible_pushforward_of_finrankFiberSections_eq_one _ L
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv)

include hL in
/-- **The seesaw theorem.** For a proper variety `X` over a field `K`, a reduced `K`-scheme `T`
of finite type and a line bundle `L` on `X × T` whose restriction to the fibre over every closed
point of `T` is trivial, the counit `p_T^* p_{T*} L ⟶ L` is an isomorphism; together with
`AlgebraicGeometry.Scheme.Modules.invertible_pushforward_pullbackSnd` this says that `L` is the
pullback of a line bundle on `T`.

This is `thm:cube-seesaw` of the blueprint. -/
theorem isIso_counit_pullbackSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction (Limits.pullback.snd πX πT)).counit.app L) :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  have := flatOver_of_invertible hL (Limits.pullback.snd πX πT)
  isIso_counit_of_restrictToFiber_iso _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv

include hL in
/-- **The seesaw theorem, triviality form.** If in addition the restriction of `L` to the slice
`{x₀} × T` through a rational point `x₀` of `X` is trivial, then `L` is trivial.

This is `cor:cube-seesaw-trivial` of the blueprint. -/
theorem nonempty_iso_structureModules_pullbackSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (hsec : Nonempty ((Modules.pullback (sliceInclusionSnd πX πT x₀ hx₀)).obj L ≅
      T.structureModules)) :
    Nonempty (L ≅ (Limits.pullback πX πT).structureModules) :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  have := flatOver_of_invertible hL (Limits.pullback.snd πX πT)
  nonempty_iso_structureModules_of_section _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv
    (sliceInclusionSnd πX πT x₀ hx₀) (sliceInclusionSnd_snd πX πT x₀ hx₀) hsec

end Projection

end AlgebraicGeometry.Scheme.Modules
