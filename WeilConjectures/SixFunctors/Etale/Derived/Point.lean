/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Detecting isomorphisms in the point category

Let `k` be a separably closed field and `s = Spec k`. Every étale `k`-scheme is covered by its
`k`-points, so an étale sheaf on `s` is determined by its global sections. In the derived
category `D(s_ét, Λ)` of étale sheaves of `Λ`-modules, the *point category*, the shifts
`Λ_s[r]` of the constant complex therefore detect isomorphisms.

## Main statements

- `AlgebraicGeometry.Scheme.eq_of_forall_restrict_eq_of_isSepClosed`: two sections of an étale
  sheaf on `Spec k` agreeing at every `k`-point are equal.
- `AlgebraicGeometry.Scheme.isZero_of_subsingleton_sections_of_isSepClosed`: an étale sheaf of
  modules on `Spec k` without nonzero global sections is zero.
- `AlgebraicGeometry.Etale.isIso_iff_bijective_comp_of_isSepClosed` (`lem-sf-detection`): a
  morphism `u : P ⟶ Q` of the point category is an isomorphism if and only if
  `Hom(Λ_s[r], u)` is bijective for every `r : ℤ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [IsSepClosed k]

/-- The terminal object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of k)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of k)))


/-- The terminal object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k`, as an object
of `(Spec k).Etale`. -/
noncomputable def etalePoint : (Spec (.of k)).Etale := 𝟙ₑ

variable {k}

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [(Spec (.of k)).smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Over a separably closed field `k`, two sections of an étale sheaf on `Spec k` over an étale
`k`-scheme `U` are equal as soon as they agree after restriction along every morphism
`V ⟶ U` from an étale `k`-scheme `V ≅ Spec k`: the `k`-points of `U` form an étale covering of
`U`. -/
theorem eq_of_forall_restrict_eq_of_isSepClosed (F : Sheaf (Spec (.of k)).smallEtaleTopology A)
    {U : (Spec (.of k)).Etale} {x y : ToType (F.obj.obj (op U))}
    (h : ∀ (V : (Spec (.of k)).Etale) (_ : IsIso V.hom) (f : V ⟶ U),
      F.obj.map f.op x = F.obj.map f.op y) :
    x = y := by
  have : AlgebraicGeometry.Etale U.hom := U.prop
  let pts := {l : Spec (.of k) ⟶ U.left // l ≫ U.hom = 𝟙 _}
  let T : (Spec (.of k)).Etale := etalePoint k
  let g : ∀ l : pts, T ⟶ U := fun l ↦ MorphismProperty.Over.homMk (A := T) (B := U) l.1
    (l.2.trans rfl)
  refine Sheaf.isSeparated F U (Sieve.ofArrows (fun _ : pts ↦ T) g) ?_ x y ?_
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨l, hl, hz⟩ := exists_fac_of_etale_of_isSepClosed U.hom (𝟙 _) z
      (Subsingleton.elim (α := Spec (.of k)) _ _)
    exact ⟨⟨l, hl⟩, (default : Spec (.of k)), hz⟩
  · rintro V f ⟨W, f', _, ⟨l⟩, rfl⟩
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      h T (inferInstanceAs (IsIso (𝟙 (Spec (.of k)))))]

omit [IsSepClosed k] in
/-- An étale `k`-scheme `V` whose structure morphism is an isomorphism is isomorphic, in the
small étale site of `Spec k`, to the terminal object `𝟙 : Spec k ⟶ Spec k`. -/
noncomputable def etaleIsoOfIsIso (V : (Spec (.of k)).Etale) (hV : IsIso V.hom) :
    V ≅ etalePoint k :=
  MorphismProperty.Over.isoMk (@asIso _ _ _ _ V.hom hV) (Category.comp_id V.hom)

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Over a separably closed field `k`, an étale sheaf of `Λ`-modules on `Spec k` whose global
sections vanish is zero. -/
theorem isZero_of_subsingleton_sections_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Subsingleton (F.obj.obj (op (etalePoint k)))) : IsZero F := by
  have := h
  have hU : ∀ U, Subsingleton (F.obj.obj (op U)) := fun U ↦ ⟨fun x y ↦
    eq_of_forall_restrict_eq_of_isSepClosed F fun V hV f ↦ by
      have : Subsingleton (F.obj.obj (op V)) :=
        (F.obj.mapIso (etaleIsoOfIsIso V hV).op).toLinearEquiv.toEquiv.symm.subsingleton
      exact Subsingleton.elim _ _⟩
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

/-- Over a separably closed field `k`, an epimorphism of étale sheaves of `Λ`-modules on `Spec k`
is surjective on global sections. -/
theorem surjective_app_sections_of_epi_of_isSepClosed
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (etalePoint k))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u + 1} Λ) φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
    (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology φ.hom
      (U := op (etalePoint k)) s)
  exact ⟨t, ht.trans (by erw [G.obj.map_id]; rfl)⟩

omit [IsSepClosed k] in
/-- `𝟙 : Spec k ⟶ Spec k` is the terminal object of the small étale site of `Spec k`. -/
noncomputable def isTerminalEtalePoint : IsTerminal (etalePoint k) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of k))

/-- The map `Λ_k ⟶ G` from the constant sheaf `Λ` on `Spec k` to an étale sheaf of
`Λ`-modules `G` corresponding to a global section `s` of `G`. -/
noncomputable def homOfGlobalSection
    {G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (s : G.obj.obj (op (etalePoint k))) :
    (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ) ⟶ G :=
  ((constantSheafAdj _ _ isTerminalEtalePoint).homEquiv
    _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s))

omit [IsSepClosed k] in
/-- Composing the map attached to a global section `s` with `ψ : G ⟶ G'` gives the map attached
to the global section `ψ(s)`. -/
theorem homOfGlobalSection_comp
    {G G' : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (s : G.obj.obj (op (etalePoint k))) (ψ : G ⟶ G') :
    homOfGlobalSection s ≫ ψ = homOfGlobalSection (ψ.hom.app _ s) := by
  rw [homOfGlobalSection, homOfGlobalSection, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext
  simp

omit [IsSepClosed k] in
/-- The map attached to a nonzero global section is nonzero. -/
theorem homOfGlobalSection_ne_zero
    {G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} {s : G.obj.obj (op (etalePoint k))} (hs : s ≠ 0) : homOfGlobalSection s ≠ 0 := by
  intro h
  apply hs
  have := congrArg (fun f : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ G ↦ ModuleCat.Hom.hom
    (((constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      isTerminalEtalePoint).homEquiv (ModuleCat.of Λ Λ) G) f) (1 : Λ)) h
  simp only [homOfGlobalSection, Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero] at this
  simpa using this

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme Pretriangulated ZeroObject

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [Ring Λ]

/-- If the `n`-th cohomology sheaf of an object `C` of the point category is nonzero, then
there is a nonzero morphism `Λ_s[-n] ⟶ C`. -/
theorem exists_ne_zero_of_not_isZero_homology
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (hC : ¬ IsZero ((DerivedCategory.homologyFunctor _ n).obj C)) :
    ∃ g : ((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))⟦-n⟧ ⟶ C,
      g ≠ 0 := by
  let e := DerivedCategory.Q.objObjPreimageIso C
  set K := DerivedCategory.Q.objPreimage C
  have hK : ¬ IsZero (K.homology n) := fun h ↦ hC (IsZero.of_iso h
    ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app K))
  obtain ⟨s, hs⟩ : ∃ s : (K.homology n).obj.obj (op (etalePoint k)), s ≠ 0 := by
    by_contra! h
    exact hK (isZero_of_subsingleton_sections_of_isSepClosed _ ⟨fun x y ↦ by rw [h x, h y]⟩)
  obtain ⟨t, rfl⟩ := surjective_app_sections_of_epi_of_isSepClosed (K.homologyπ n) s
  let f : (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (homOfGlobalSection t ≫ K.iCycles n) (by simp)
  have hf : (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫
      HomologicalComplex.homologyMap f n = homOfGlobalSection t ≫ K.homologyπ n := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    congr 1
    rw [← cancel_mono (K.iCycles n), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
      HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  have hQf : DerivedCategory.Q.map f ≠ 0 := by
    intro h0
    have := DerivedCategory.homologyFunctorFactors_hom_naturality f n
    rw [h0, Functor.map_zero, zero_comp] at this
    have hzero : HomologicalComplex.homologyMap f n = 0 :=
      (cancel_epi ((DerivedCategory.homologyFunctorFactors _ n).hom.app _)).1
        (this.symm.trans comp_zero.symm)
    apply homOfGlobalSection_ne_zero hs
    rw [← homOfGlobalSection_comp, ← hf, hzero, comp_zero]
  refine ⟨((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).hom.app _ ≫
    DerivedCategory.Q.map f ≫ e.hom, ?_⟩
  intro h0
  apply hQf
  rw [← cancel_mono e.hom, zero_comp]
  exact (cancel_epi (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).hom.app
    _)).1 (h0.trans comp_zero.symm)

/-- Blueprint `lem-sf-detection`: Detection of isomorphisms at the point.

Let `k` be a separably closed field and `s = Spec k`. A morphism `u : P ⟶ Q` of the point
category `D(s_ét, Λ)` is an isomorphism if and only if `Hom(Λ_s[r], u)` is bijective for every
`r : ℤ`, where `Λ_s` is the constant sheaf `Λ` placed in degree `0`.

The blueprint deduces this from the equivalence of the point category with complexes of
`Λ`-modules. Here the cone `C` of `u` is shown to be zero directly: `Hom(Λ_s[r], C) = 0` for all
`r` by the long exact sequence, and a nonzero cohomology sheaf `H^n(C)` would give a nonzero
morphism `Λ_s[-n] ⟶ C`, since an étale sheaf on `Spec k` is determined by its global sections
(`AlgebraicGeometry.Etale.exists_ne_zero_of_not_isZero_homology`). -/
theorem isIso_iff_bijective_comp_of_isSepClosed
    {P Q : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (u : P ⟶ Q) :
    IsIso u ↔ ∀ r : ℤ, Function.Bijective (fun g : ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)))⟦r⟧ ⟶ P ↦ g ≫ u) := by
  refine ⟨fun hu r ↦ (isIso_iff_yoneda_map_bijective u).1 hu _, fun h ↦ ?_⟩
  set T := (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ))
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle u
  -- composition with `u⟦1⟧'` is injective on morphisms out of `T⟦r⟧`
  have hinj : ∀ (r : ℤ) (x : T⟦r⟧ ⟶ P⟦(1 : ℤ)⟧), x ≫ u⟦(1 : ℤ)⟧' = 0 → x = 0 := by
    intro r x hx
    let E : T⟦r⟧ ≅ (T⟦r - 1⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd' _ (r - 1) 1 r (by omega)).app T
    obtain ⟨y, hy⟩ := (shiftFunctor _ (1 : ℤ)).map_surjective (E.inv ≫ x)
    have hyu : y ≫ u = 0 := by
      apply (shiftFunctor _ (1 : ℤ)).map_injective
      rw [Functor.map_comp, hy, Functor.map_zero, Category.assoc, hx, comp_zero]
    have hy0 : y = 0 := (h (r - 1)).1 (hyu.trans zero_comp.symm)
    rw [← cancel_epi E.inv, ← hy, hy0, Functor.map_zero, comp_zero]
  have hw : w ≫ u⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have huv : u ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hzero : ∀ (r : ℤ) (g : T⟦r⟧ ⟶ C), g = 0 := by
    intro r g
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ _ hT g
      (hinj r (g ≫ w) (by rw [Category.assoc, hw, comp_zero]))
    obtain ⟨g'', rfl⟩ := (h r).2 g'
    change g = (g'' ≫ u) ≫ v at hg'
    rw [hg', Category.assoc, huv, comp_zero]
  have hC : IsZero C := by
    have : IsIso (0 : C ⟶ 0) := (DerivedCategory.isIso_iff _ _).2 fun n ↦ by
      have hn : IsZero ((DerivedCategory.homologyFunctor _ n).obj C) := by
        by_contra hn
        obtain ⟨g, hg⟩ := exists_ne_zero_of_not_isZero_homology C n hn
        exact hg (hzero _ g)
      exact isIso_of_source_target_iso_zero _ hn.isoZero
        ((Functor.map_isZero _ (isZero_zero _)).isoZero)
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : C ⟶ 0))
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hC

end AlgebraicGeometry.Etale
