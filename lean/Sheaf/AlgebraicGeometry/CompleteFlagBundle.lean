/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The complete flag bundle by tautological kernels

Source: Stacks Project, Chow Homology, Tag 02UL, proof of
`lemma-splitting-principle` (blueprint: def-pur-complete-flag-bundle).

`completeFlagBundle` is the rank recursion. Its levels are actual sheaves with maps to
its pulled-back module. `completeFlagStep` is the uniquely determined inclusion between
successive levels, and `completeFlagQuotient` is its sheaf cokernel.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject BigOperators

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The universal property fixing a normalized quotient-line projectivization.
The line quotient is a sheaf epimorphism, and the comparison must carry the
prescribed universal quotient to that very quotient.
Source: Stacks, Tag 01OB (blueprint: def-pur-complete-flag-bundle). -/
def IsCompleteFlagProjectivization {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) : Prop :=
  ∀ (S : Scheme.{u}) (f : S ⟶ T) (M : S.Modules) [M.IsInvertible]
    (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M) [Epi ε],
    ∃! g : S ⟶ D.A.data.relProj, ∃ h : g ≫ D.A.data.relProjHom = f,
      ∃ θ : (Scheme.Modules.tensorPullback g).obj D.L ≅ M,
        (Scheme.Modules.tensorPullback g).map D.quotient ≫ θ.hom =
          ((Scheme.Modules.tensorPullbackSectionComp g D.A.data.relProjHom).app F).inv ≫
            (projectiveBundlePullbackCongr h).hom.app F ≫ ε

/-- The normalized symmetric-algebra projectivization has its quotient-line universal
property, which determines the scheme and quotient up to canonical isomorphism.
Source: Stacks, Tags 01OB and 01OE (blueprint: def-pur-complete-flag-bundle).
Proof: take the normalized projective-bundle geometry of
`lem-pur-projective-bundle-tautological-geometry`. Locally trivialize the given line
quotient and a frame of `F`. Where its j-th coefficient is a unit, the ratios of the
other coefficients to it define the unique map to `D₊(Xⱼ)`. The quotient being epi
makes these opens a cover. The ratio maps agree on overlaps and glue. They are
unchanged by a frame change, since the symmetric algebra uses the same change of
basis on its degree-one generators. The normalized twist generator maps to the
j-th coefficient, giving the line isomorphism and the displayed quotient square.
The ratios force uniqueness of the scheme map; surjectivity of the quotient
forces uniqueness of the line comparison. Thus only a universal-property proof
is postponed, with all projectivization data fixed up to canonical isomorphism. -/
theorem exists_completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ∃ D : ProjectiveBundleRealization T F, IsCompleteFlagProjectivization D := by
  sorry

/-- A representative of the universal, normalized projectivization of the actual
symmetric algebra. The existence theorem specifies its universal property, while
`ProjectiveBundleRealization` fixes the affine algebras, restrictions, twist and
quotient by their homogeneous-localization formulas. Its data are determined up
to the canonical isomorphism used in interpreting the construction.
Source: Stacks, Tags 01OB, 01NR, 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ProjectiveBundleRealization T F :=
  Classical.choose (exists_completeFlagProjectivization T n F)

attribute [local irreducible] completeFlagProjectivization CategoryTheory.Limits.limit
  CategoryTheory.Limits.colimit

/-- The tautological kernel is the categorical kernel in sheaves of modules, hence
is the subsheaf of sections annihilated by the prescribed quotient.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagKernel (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagProjectivization T n F).A.data.relProj.Modules :=
  kernel (completeFlagProjectivization T n F).quotient

private theorem kernel_basis {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type*} [Finite ι]
    (v : Module.Basis ι R M) (f : M →ₗ[R] N) (τ : N)
    (hτ : Function.Injective fun r : R ↦ r • τ)
    (j : ι) (a : ι → R) (hj : a j = 1) (hε : ∀ i, f (v i) = a i • τ) :
    ∃ b : Module.Basis {i : ι // i ≠ j} R f.ker,
      ∀ i, (b i).val = v i.val - a i.val • v j := by
  classical
  let := Fintype.ofFinite ι
  let w (i : {i : ι // i ≠ j}) : f.ker :=
    ⟨v i.val - a i.val • v j, by simp [map_sub, map_smul, hε, hj]⟩
  let c : f.ker →ₗ[R] ({i : ι // i ≠ j} → R) :=
    LinearMap.pi fun i ↦ (v.coord i.val).comp f.ker.subtype
  have hc (x : f.ker) (i : {i : ι // i ≠ j}) : c x i = v.repr x.val i.val := rfl
  have hw (i k : {i : ι // i ≠ j}) : c (w i) k = if i = k then 1 else 0 := by
    simp [hc, w, map_sub, map_smul, Module.Basis.repr_self, k.property,
      Subtype.ext_iff, Finsupp.single_apply]
  have hinj : Function.Injective c := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro x hx
      have hx' : c x = 0 := hx
      have hz (i : ι) (hi : i ≠ j) : v.repr x.val i = 0 := by
        exact congrFun hx' ⟨i, hi⟩
      have he : x.val = v.repr x.val j • v j := by
        conv_lhs => rw [← v.sum_repr x.val]
        exact Finset.sum_eq_single j (fun i _ hi ↦ by rw [hz i hi, zero_smul])
          (by simp)
      have hj0 : v.repr x.val j = 0 := hτ (by
        have h : f x.val = 0 := x.property
        rw [he, map_smul, hε, hj, one_smul] at h
        simpa using h)
      apply Subtype.ext
      change x.val = 0
      rw [he, hj0, zero_smul]
    · exact bot_le
  have hsurj : Function.Surjective c := by
    intro t
    refine ⟨∑ i, t i • w i, ?_⟩
    ext k
    simp [map_sum, map_smul, hw]
  let e := LinearEquiv.ofBijective c ⟨hinj, hsurj⟩
  refine ⟨Module.Basis.ofEquivFun e, ?_⟩
  intro i
  have he : (Module.Basis.ofEquivFun e) i = w i := by
    apply hinj
    change e ((Module.Basis.ofEquivFun e) i) = c (w i)
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
    ext k
    simp [hw, Pi.single_apply, eq_comm]
  rw [he]

/-- The explicit chart splitting and kernel basis. On `D₊(Xⱼ)` take `aᵢ=Xᵢ/Xⱼ`,
`v` the pulled-back frame and `τ=τⱼ`; the normalized quotient and its overlap
formulas are those of `ProjectiveBundleRealization` and `ProjectiveBundleFrameChart`.
Source: Stacks, Tags 01OB and 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: every section of the line is uniquely a multiple of `τ`. Send that multiple
to the same multiple of `vⱼ`. Since `aⱼ=1`, this is a section of the quotient.
For a kernel vector subtract the sum of its coefficients away from j times
`vᵢ-aᵢvⱼ`. The result is a multiple of `vⱼ` in the kernel, hence zero because
`τ` is a free generator. The coefficients away from j also prove independence.
Sections of the sheaf kernel are precisely the sectionwise kernel, since the
sections functor preserves limits. This identifies the displayed basis with
sections of the actual sheaf kernel, on every further open in the chart. -/
theorem completeFlagKernel_chart {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) (r : ℕ)
    (W : D.A.data.relProj.Opens)
    (v : Module.Basis (Fin r) Γ(D.A.data.relProj, W)
      Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W))
    (τ : Γ(D.L, W)) (hτ : Scheme.Modules.IsFreeGenerator τ)
    (j : Fin r) (a : Fin r → Γ(D.A.data.relProj, W)) (hj : a j = 1)
    (hε : ∀ i : Fin r, Scheme.Modules.Hom.app D.quotient W (v i) = a i • τ) :
    (∃ s : Γ(D.L, W) →ₗ[Γ(D.A.data.relProj, W)]
        Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W),
      s τ = v j ∧ ∀ x : Γ(D.L, W), Scheme.Modules.Hom.app D.quotient W (s x) = x) ∧
    ∃ b : Module.Basis {i : Fin r // i ≠ j} Γ(D.A.data.relProj, W)
        Γ(kernel D.quotient, W),
      ∀ i : {i : Fin r // i ≠ j},
        Scheme.Modules.Hom.app (kernel.ι D.quotient) W (b i) = v i.1 - a i.1 • v j := by
  classical
  constructor
  · let s : Γ(D.L, W) →ₗ[Γ(D.A.data.relProj, W)]
        Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W) :=
      { toFun := fun x ↦ hτ.coeff x • v j
        map_add' := by intro x y; simp [add_smul]
        map_smul' := by intro c x; simp [mul_smul] }
    refine ⟨s, ?_, ?_⟩
    · have hc : hτ.coeff τ = 1 := by simpa using hτ.coeff_smul_self 1
      simp [s, hc]
    · intro x
      simp [s, hε, hj]
  · let E := SheafOfModules.evaluation D.A.data.relProj.ringCatSheaf (Opposite.op W)
    let e := PreservesKernel.iso E D.quotient ≪≫ ModuleCat.kernelIsoKer (E.map D.quotient)
    have he : e.hom ≫ ModuleCat.ofHom (E.map D.quotient).hom.ker.subtype =
        E.map (kernel.ι D.quotient) := by
      simp [e, PreservesKernel.iso_hom]
    obtain ⟨b, hb⟩ := kernel_basis v (D.quotient.val.app (Opposite.op W)).hom
      τ hτ.smul_left_injective j a hj hε
    refine ⟨b.map e.symm.toLinearEquiv, ?_⟩
    intro i
    change (E.map (kernel.ι D.quotient)) (e.inv (b i)) = _
    rw [← he]
    change (e.hom (e.inv (b i))).val = _
    simp only [Iso.inv_hom_id_apply]
    exact hb i

/-- The tautological quotient is locally split, and its displayed local splittings
remain splittings after every pullback. This asserts no global splitting.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: refine the frame cover by the standard opens `D₊(Xⱼ)`. On each one send
the twist generator to the j-th frame vector; the quotient formula gives the
identity on the generator and hence on the line sheaf. Pull back these local
sections along `g`, and then restrict to a neighbourhood of the given point.
Functoriality preserves the section equation. The preimages of the chart cover
cover S, giving the asserted local splittings for every pullback. -/
theorem completeFlagKernel_pullback_locally_split (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (S : Scheme.{u}) (g : S ⟶ (completeFlagProjectivization T n F).A.data.relProj) :
    ∀ x : S, ∃ W : S.Opens, x ∈ W ∧
      ∃ s : (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj (completeFlagProjectivization T n F).L) ⟶
        (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj
            ((Scheme.Modules.tensorPullback
              (completeFlagProjectivization T n F).A.data.relProjHom).obj F)),
        s ≫ (Scheme.Modules.tensorPullback W.ι).map
          ((Scheme.Modules.tensorPullback g).map
            (completeFlagProjectivization T n F).quotient) = 𝟙 _ := by
  sorry

/-- The rank needed for the recursive call.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: in a frame on `D₊(Xⱼ)`, the quotient sends `vᵢ` to `(Xᵢ/Xⱼ)τⱼ`.
It has the section `τⱼ ↦ vⱼ`; its kernel has the free basis
`vᵢ - (Xᵢ/Xⱼ)vⱼ`, for `i ≠ j`. The standard opens over a frame cover cover
projective space; the frame opens cover the base. These bases therefore prove
finite local freeness of rank `n`. The normalized degree-one maps ensure that
these are the kernel of the same global quotient on overlaps and under frame changes. -/
theorem completeFlagKernel_rank (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagKernel T n F).IsFiniteLocallyFreeOfRank n := by
  sorry

/-- A scheme over `T` together with a family of actual subsheaf presentations.
Levels past the rank are repeated final levels; only levels `0,…,r` are used.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
structure CompleteFlagBundleData (T : Scheme.{u}) (F : T.Modules) where
  scheme : Scheme.{u}
  projection : scheme ⟶ T
  level : ℕ → scheme.Modules
  inclusion : ∀ i : ℕ, level i ⟶ (Scheme.Modules.tensorPullback projection).obj F

/-- The identity bundle with its zero and full levels, used at ranks zero and one.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagIdentity (T : Scheme.{u}) (F : T.Modules) :
    CompleteFlagBundleData T F where
  scheme := T
  projection := 𝟙 T
  level i := if i = 0 then 0 else (Scheme.Modules.tensorPullback (𝟙 T)).obj F
  inclusion i := if h : i = 0 then
    eqToHom (if_pos h) ≫ 0
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- Extend a recursive kernel filtration by its ambient pulled-back module.
The embeddings use the actual kernel inclusion and the section-normalized comparison
`h* q* F ≅ (h ≫ q)* F`. No global splitting is chosen.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagExtend {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r : ℕ) :
    CompleteFlagBundleData T F where
  scheme := G.scheme
  projection := G.projection ≫ D.A.data.relProjHom
  level i := if i < r then G.level i else
    (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F
  inclusion i := if h : i < r then
    eqToHom (if_pos h) ≫ G.inclusion i ≫
      (Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- The complete flag bundle, recursively projectivizing the tautological kernel.
At ranks zero and one its projection is the identity. At rank `n+2` it is the
composite of the recursively constructed rank-`n+1` flag projection with the
projectivization projection; its earlier levels are the recursive kernel levels.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagBundle : (r : ℕ) → (T : Scheme.{u}) → (F : T.Modules) →
    [F.IsFiniteLocallyFreeOfRank r] → CompleteFlagBundleData T F
  | 0, T, F, _ => completeFlagIdentity T F
  | 1, T, F, _ => completeFlagIdentity T F
  | n + 2, T, F, _ =>
    let D := completeFlagProjectivization T (n + 1) F
    letI := completeFlagKernel_rank T (n + 1) F
    completeFlagExtend D
      (completeFlagBundle (n + 1) D.A.data.relProj (completeFlagKernel T (n + 1) F))
      (n + 2)
termination_by structural r => r

/-- The recursive kernel flag, exposing the map `h` used at rank `n+2`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagPredecessor (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    CompleteFlagBundleData (completeFlagProjectivization T (n + 1) F).A.data.relProj
      (completeFlagKernel T (n + 1) F) :=
  letI := completeFlagKernel_rank T (n + 1) F
  completeFlagBundle (n + 1) _ (completeFlagKernel T (n + 1) F)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible]
  projectiveBundleTensorPullbackIso Scheme.Modules.tensorPullbackSectionComp
  Scheme.Modules.tensorPullbackSectionId

private theorem split_epi_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) [IsSplitEpi (F.map f)] :
    IsSplitEpi (G.map f) := by
  apply IsSplitEpi.mk'
  refine ⟨e.inv.app B ≫ section_ (F.map f) ≫ e.hom.app A, ?_⟩
  rw [Category.assoc, Category.assoc, ← e.hom.naturality, ← Category.assoc (section_ (F.map f)),
    IsSplitEpi.id, Category.id_comp, e.inv_hom_id_app]

private theorem kernel_split {C : Type*} [Category C] [Preadditive C]
    {A B : C} (f : A ⟶ B) [HasKernel f] [IsSplitEpi f] :
    IsSplitMono (kernel.ι f) := by
  let r := kernel.lift f (𝟙 A - f ≫ section_ f) (by simp)
  apply IsSplitMono.mk'
  refine ⟨r, ?_⟩
  apply (cancel_mono (kernel.ι f)).mp
  simp [r, Preadditive.comp_sub]

private theorem map_kernel_split {C D : Type*} [Category C] [Preadditive C]
    [Category D] [Preadditive D] (H : C ⥤ D) [H.Additive]
    {A B : C} (f : A ⟶ B) [HasKernel f] [HasKernel (H.map f)]
    [PreservesLimit (parallelPair f 0) H] [IsSplitEpi (H.map f)] :
    IsSplitMono (H.map (kernel.ι f)) := by
  have := kernel_split (H.map f)
  have : IsSplitMono ((PreservesKernel.iso H f).hom ≫ kernel.ι (H.map f)) :=
    inferInstance
  simpa using this

private theorem restrict_limits {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let R := Scheme.Modules.restrictFunctor f
  let Z := Scheme.Modules.toPresheaf X
  let Z' := Scheme.Modules.toPresheaf Y
  let eR : R ⋙ Z ≅ Z' ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op :=
    Iso.refl _
  have : PreservesFiniteLimits Z' := by dsimp only [Z']; infer_instance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab).obj f.opensFunctor.op) := by infer_instance
  have : PreservesFiniteLimits (R ⋙ Z) := preservesFiniteLimits_of_natIso eR.symm
  exact preservesFiniteLimits_of_reflects_of_preserves R Z

private theorem restrict_kernel_split {X : Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) (U : X.Opens)
    [IsSplitEpi ((Scheme.Modules.tensorPullback U.ι).map f)] :
    IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map (kernel.ι f)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let a : Scheme.Modules.tensorPullback U.ι ≅ R :=
    projectiveBundleTensorPullbackIso U.ι ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  have : IsSplitEpi (R.map f) := split_epi_iso a f
  have : PreservesFiniteLimits R := restrict_limits U.ι
  have : R.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  exact map_kernel_split R f

private theorem tautological_locally_split_kernel (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ∀ x : (completeFlagProjectivization T n F).A.data.relProj,
      ∃ U : (completeFlagProjectivization T n F).A.data.relProj.Opens, x ∈ U ∧
        IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map
          (kernel.ι (completeFlagProjectivization T n F).quotient)) := by
  intro x
  let D := completeFlagProjectivization T n F
  obtain ⟨U, hx, s, hs⟩ := completeFlagKernel_pullback_locally_split T n F
    D.A.data.relProj (𝟙 _) x
  let H := Scheme.Modules.tensorPullback U.ι
  let e := Functor.isoWhiskerRight (Scheme.Modules.tensorPullbackSectionId D.A.data.relProj) H
  have : IsSplitEpi ((Scheme.Modules.tensorPullback (𝟙 D.A.data.relProj) ⋙ H).map
      D.quotient) := IsSplitEpi.mk' ⟨s, hs⟩
  have : IsSplitEpi (H.map D.quotient) := split_epi_iso e D.quotient
  exact ⟨U, hx, restrict_kernel_split D.quotient U⟩

private theorem pullback_mono_of_local_retractions {X Y : Scheme.{u}}
    {A B : X.Modules} (f : A ⟶ B)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map f)) (g : Y ⟶ X) :
    Mono ((Scheme.Modules.tensorPullback g).map f) := by
  classical
  choose U hx hs using h
  let V (y : Y) := g ⁻¹ᵁ U (g y)
  have hm : Mono ((Scheme.Modules.pullback g).map f) := by
    apply Scheme.Modules.mono_of_restrict _ V
    · exact eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx (g y)⟩
    · intro y
      let R := Scheme.Modules.restrictFunctor (U (g y)).ι
      let G := Scheme.Modules.pullback (g ∣_ U (g y))
      let H := Scheme.Modules.restrictFunctor (V y).ι
      let e : Scheme.Modules.pullback g ⋙ H ≅ R ⋙ G :=
        Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (V y).ι) ≪≫
          Scheme.Modules.pullbackComp (V y).ι g ≪≫
          Scheme.Modules.pullbackCongr (morphismRestrict_ι g (U (g y))).symm ≪≫
          (Scheme.Modules.pullbackComp (g ∣_ U (g y)) (U (g y)).ι).symm ≪≫
          Functor.isoWhiskerRight
            (Scheme.Modules.restrictFunctorIsoPullback (U (g y)).ι).symm G
      have : IsSplitMono (R.map f) := hs (g y)
      have hj : G.map (R.map f) ≫
          G.map (retraction (R.map f)) = 𝟙 _ := by
        rw [← G.map_comp, IsSplitMono.id, G.map_id]
      have : IsSplitMono (H.map ((Scheme.Modules.pullback g).map
          f)) := IsSplitMono.mk'
        { retraction := e.hom.app _ ≫ G.map (retraction (R.map f)) ≫
            e.inv.app _
          id := by
            change (Scheme.Modules.pullback g ⋙ H).map f ≫ _ = _
            rw [← Category.assoc, e.hom.naturality, Functor.comp_map, Category.assoc,
              ← Category.assoc (G.map (R.map f)), hj, Category.id_comp]
            exact e.hom_inv_id_app _ }
      infer_instance
  let e := projectiveBundleTensorPullbackIso g
  have he : (Scheme.Modules.tensorPullback g).map f =
      e.hom.app _ ≫ (Scheme.Modules.pullback g).map f ≫ e.inv.app _ := by
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app, Category.comp_id]
  rw [he]
  infer_instance

private theorem tautological_kernel_pullback_mono (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (Y : Scheme.{u}) (g : Y ⟶ (completeFlagProjectivization T n F).A.data.relProj) :
    Mono ((Scheme.Modules.tensorPullback g).map
      (kernel.ι (completeFlagProjectivization T n F).quotient)) := by
  exact pullback_mono_of_local_retractions _ (tautological_locally_split_kernel T n F) g

private theorem identity_mono {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (A : C) (i : ℕ) :
    Mono (if h : i = 0 then (eqToHom (if_pos h) :
      (if i = 0 then 0 else A) ⟶ 0) ≫ (0 : 0 ⟶ A)
      else eqToHom (if_neg h) ≫ 𝟙 A) := by
  split <;> infer_instance

private theorem extend_mono {C : Type*} [Category C] {K A : C}
    (L : ℕ → C) (j : ∀ i, L i ⟶ K) (k : K ⟶ A) [∀ i, Mono (j i)] [Mono k]
    (r i : ℕ) :
    Mono (if h : i < r then (eqToHom (if_pos h) :
      (if i < r then L i else A) ⟶ L i) ≫ j i ≫ k
      else eqToHom (if_neg h) ≫ 𝟙 A) := by
  split <;> infer_instance

private theorem identity_mono_data (T : Scheme.{u}) (F : T.Modules) (i : ℕ) :
    Mono ((completeFlagIdentity T F).inclusion i) :=
  identity_mono ((Scheme.Modules.tensorPullback (𝟙 T)).obj F) i

private theorem extend_mono_data {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient))
    [∀ i, Mono (G.inclusion i)]
    [Mono ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient))]
    (r i : ℕ) : Mono ((completeFlagExtend D G r).inclusion i) :=
  extend_mono G.level G.inclusion
    ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv) r i

attribute [local irreducible] completeFlagBundle completeFlagIdentity completeFlagExtend

/-- Each presented level is a subsheaf.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: for the identity cases, the zero and identity maps are monomorphisms.
In the induction step the recursive maps are monic by induction. The chart
splitting `τⱼ ↦ vⱼ` makes the kernel inclusion split on the standard open cover;
a split inclusion remains split after any pullback. Composing this pulled-back
inclusion with the recursive inclusion and the pullback comparison remains monic. -/
theorem completeFlagBundle_mono (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    Mono ((completeFlagBundle r T F).inclusion i) := by
  induction r using Nat.strong_induction_on generalizing T F i with
  | h r ih =>
    cases r with
    | zero =>
      rw [completeFlagBundle]
      exact identity_mono_data T F i
    | succ r =>
      cases r with
      | zero =>
        rw [completeFlagBundle]
        exact identity_mono_data T F i
      | succ n =>
        rw [completeFlagBundle]
        let D := completeFlagProjectivization T (n + 1) F
        let := completeFlagKernel_rank T (n + 1) F
        let G := completeFlagBundle (n + 1) D.A.data.relProj
          (completeFlagKernel T (n + 1) F)
        have hm : ∀ k, Mono (G.inclusion k) := fun k ↦
          ih (n + 1) (by omega) D.A.data.relProj (completeFlagKernel T (n + 1) F) k
        have hk : Mono ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient)) :=
          tautological_kernel_pullback_mono T (n + 1) F G.scheme G.projection
        exact @extend_mono_data T F D G hm hk (n + 2) i

private theorem flag_identity_steps {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (A : C) (i : ℕ) :
    ∃ f : (if i = 0 then 0 else A) ⟶ (if i + 1 = 0 then 0 else A),
      f ≫ (if h : i + 1 = 0 then eqToHom (if_pos h) ≫ 0
        else eqToHom (if_neg h) ≫ 𝟙 A) =
      (if h : i = 0 then eqToHom (if_pos h) ≫ 0
        else eqToHom (if_neg h) ≫ 𝟙 A) := by
  have hi : i + 1 ≠ 0 := by omega
  refine ⟨(if h : i = 0 then eqToHom (if_pos h) ≫ 0
    else eqToHom (if_neg h) ≫ 𝟙 A) ≫ eqToHom (if_neg hi).symm, ?_⟩
  simp only [dif_neg hi, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem flag_extend_steps {C : Type*} [Category C] {K A : C}
    (L : ℕ → C) (j : ∀ i, L i ⟶ K) (k : K ⟶ A) (r i : ℕ)
    (h : ∃ f : L i ⟶ L (i + 1), f ≫ j (i + 1) = j i) :
    ∃ f : (if i < r then L i else A) ⟶ (if i + 1 < r then L (i + 1) else A),
      f ≫ (if h : i + 1 < r then eqToHom (if_pos h) ≫ j (i + 1) ≫ k
        else eqToHom (if_neg h) ≫ 𝟙 A) =
      (if h : i < r then eqToHom (if_pos h) ≫ j i ≫ k
        else eqToHom (if_neg h) ≫ 𝟙 A) := by
  by_cases hi : i + 1 < r
  · have hi' : i < r := by omega
    obtain ⟨f, hf⟩ := h
    refine ⟨eqToHom (if_pos hi') ≫ f ≫ eqToHom (if_pos hi).symm, ?_⟩
    simp only [dif_pos hi, dif_pos hi', Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Category.assoc f, hf]
  · by_cases hi' : i < r
    · refine ⟨eqToHom (if_pos hi') ≫ j i ≫ k ≫ eqToHom (if_neg hi).symm, ?_⟩
      simp only [dif_neg hi, dif_pos hi', Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
    · refine ⟨eqToHom (if_neg hi') ≫ eqToHom (if_neg hi).symm, ?_⟩
      simp only [dif_neg hi, dif_neg hi', eqToHom_trans, Category.comp_id]

attribute [local semireducible] completeFlagIdentity completeFlagExtend

private theorem identity_steps_data (T : Scheme.{u}) (F : T.Modules) (i : ℕ) :
    ∃ f : (completeFlagIdentity T F).level i ⟶ (completeFlagIdentity T F).level (i + 1),
      f ≫ (completeFlagIdentity T F).inclusion (i + 1) =
        (completeFlagIdentity T F).inclusion i :=
  flag_identity_steps ((Scheme.Modules.tensorPullback (𝟙 T)).obj F) i

private theorem extend_steps_data {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r i : ℕ)
    (h : ∃ f : G.level i ⟶ G.level (i + 1), f ≫ G.inclusion (i + 1) = G.inclusion i) :
    ∃ f : (completeFlagExtend D G r).level i ⟶ (completeFlagExtend D G r).level (i + 1),
      f ≫ (completeFlagExtend D G r).inclusion (i + 1) =
        (completeFlagExtend D G r).inclusion i :=
  flag_extend_steps G.level G.inclusion
    ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv)
    r i h

attribute [local irreducible] projectiveBundlePullbackAdjunction
  completeFlagIdentity completeFlagExtend
/-- The levels form an increasing filtration; the factor map is uniquely determined.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: at ranks zero and one the factors are zero or identity maps. At a higher
rank use the recursive factor while both levels are kernel levels. At the last
step use the pulled-back kernel inclusion, composed with the last recursive
level map. Thereafter use identities. The equations follow by composition with
the ambient inclusion. Uniqueness follows from `completeFlagBundle_mono`. -/
theorem completeFlagBundle_step_unique (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    ∃! f : (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1),
      f ≫ (completeFlagBundle r T F).inclusion (i + 1) =
        (completeFlagBundle r T F).inclusion i := by
  classical
  have hex : ∃ f : (completeFlagBundle r T F).level i ⟶
      (completeFlagBundle r T F).level (i + 1),
      f ≫ (completeFlagBundle r T F).inclusion (i + 1) =
        (completeFlagBundle r T F).inclusion i := by
    induction r using Nat.strong_induction_on generalizing T F with
    | h r ih =>
      cases r with
      | zero =>
        rw [completeFlagBundle]
        exact identity_steps_data T F i
      | succ r =>
        cases r with
        | zero =>
          rw [completeFlagBundle]
          exact identity_steps_data T F i
        | succ n =>
          rw [completeFlagBundle]
          let D := completeFlagProjectivization T (n + 1) F
          let := completeFlagKernel_rank T (n + 1) F
          let G := completeFlagBundle (n + 1) D.A.data.relProj
            (completeFlagKernel T (n + 1) F)
          exact extend_steps_data D G (n + 2) i
            (ih (n + 1) (by omega) D.A.data.relProj (completeFlagKernel T (n + 1) F))
  obtain ⟨f, hf⟩ := hex
  let := completeFlagBundle_mono r T F (i + 1)
  exact ⟨f, hf, fun g hg ↦ (cancel_mono
    ((completeFlagBundle r T F).inclusion (i + 1))).mp (hg.trans hf.symm)⟩

attribute [local semireducible] completeFlagBundle completeFlagIdentity completeFlagExtend

/-- The uniquely characterized inclusion `Fᵢ ⟶ Fᵢ₊₁`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagStep (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1) :=
  Classical.choose (completeFlagBundle_step_unique r T F i)

attribute [local irreducible] completeFlagStep

/-- The successive quotient `Qᵢ₊₁ = Fᵢ₊₁/Fᵢ`, taken in sheaves of modules.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagQuotient (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) : (completeFlagBundle r T F).scheme.Modules :=
  cokernel (completeFlagStep r T F i)

set_option backward.isDefEq.respectTransparency false

/-- The last quotient is the pullback of the tautological line by the recursive map,
with quotient map the pulled-back tautological quotient `h*ε` under `p*F ≅ h*q*F`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: the chart section of the tautological quotient splits its kernel sequence.
After pullback by `h` this is still a split exact sequence. Its kernel is the
last recursive level, by induction. These local cokernel identifications carry
the quotient map to `h*ε`, so agree on overlaps by the cokernel universal property.
They glue to the stated isomorphism, without a global splitting. -/
theorem completeFlagBundle_last_quotient (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    ∃ θ : completeFlagQuotient (n + 2) T F (n + 1) ≅
        (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).obj
          (completeFlagProjectivization T (n + 1) F).L,
      cokernel.π (completeFlagStep (n + 2) T F (n + 1)) ≫ θ.hom =
        (completeFlagBundle (n + 2) T F).inclusion (n + 2) ≫
          ((Scheme.Modules.tensorPullbackSectionComp (completeFlagPredecessor T n F).projection
            (completeFlagProjectivization T (n + 1) F).A.data.relProjHom).app F).hom ≫
          (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).map
            (completeFlagProjectivization T (n + 1) F).quotient := by
  sorry

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] completeFlagBundle completeFlagQuotient
  completeFlagPredecessor completeFlagKernel completeFlagExtend completeFlagIdentity

/-- Endpoints, line quotients and the vector subbundle property of the universal filtration.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: induct on the rank. Rank zero means `F` is locally zero, hence zero by
sheaf separatedness. At rank one the sole quotient is the pullback of `F` by the
identity, and is invertible. At rank `n+2`, on a pulled-back standard chart the
splitting of the tautological quotient gives `h*q*F = h*K ⊕ h*L`. Refine by an
adapted frame for the recursive filtration. This gives an adapted frame for the
new one: its earlier quotients are the recursive line quotients, its last is
`h*L`, and every ambient quotient by a level is locally free. The initial level
is zero by induction and the final inclusion is the identity by construction.
Only these local splittings, and no global splitting, are used. -/
theorem completeFlagBundle_properties (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    IsZero ((completeFlagBundle r T F).level 0) ∧
    IsIso ((completeFlagBundle r T F).inclusion r) ∧
    (∀ i : ℕ, i < r → (completeFlagQuotient r T F i).IsInvertible) ∧
    (∀ i : ℕ, i ≤ r →
      (cokernel ((completeFlagBundle r T F).inclusion i)).IsLocallyFree) := by
  sorry

end AlgebraicGeometry
