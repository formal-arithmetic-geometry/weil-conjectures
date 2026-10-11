/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement
public import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.SixFunctors.Finite.Descent
public import WeilConjectures.Topology.SpectralSpace.ShrinkCover

/-!
# Sections of étale sheaves over a proper scheme over a henselian pair

Let `(A, I)` be a henselian pair, `p : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre
over `Spec A/I`. For every abelian étale sheaf `G` on `Y`, the restriction of global sections
`Γ(Y, G) ⟶ Γ(Y₀, i^* G)` is bijective.

* *Injectivity.* A section whose restriction to `Y₀` vanishes vanishes on an open neighbourhood
  of `Y₀` (`AlgebraicGeometry.Etale.range_subset_vanishingLocus_of_pullSection_eq_zero`); as
  every nonempty closed subset of `Y` meets `Y₀`, `p` being closed, it vanishes.
* *Surjectivity.* A section `t` over `Y₀` is étale locally the restriction of sections `g_k` of
  `G` over finitely many étale `U_k ⟶ Y` covering `Y₀`. The finite refinement of the surjective
  étale morphism `∐ U_k ⊔ (Y ∖ Y₀) ⟶ Y` (Stacks 09Z0) gives a finite surjective `r : Y' ⟶ Y`
  on which the `g_k` pull back to sections on Zariski opens of `Y'`, which agree near the closed
  fibre `Y'₀`. The spectral shrinking `SpectralSpace.exists_shrink_of_isConnected_inter`
  (Stacks 09ZG, with the connectedness of the closed fibres of the proper `Y' ⟶ Spec A`,
  Stacks 0A0B) glues them to a section `σ'` of `r^* G` restricting to `r₀^* t` on `Y'₀`. Its
  two pullbacks to `Y' ×_Y Y'` have the same restriction to the closed fibre, hence agree by
  injectivity, and `σ'` descends along the finite surjective `r` (Stacks 09Z3) to a section of
  `G` restricting to `t`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_pullSection_of_henselianRing`: the comparison.

## References

- Stacks Project, Lemma 59.91.2, <https://stacks.math.columbia.edu/tag/0A0C>
- Stacks Project, Lemma 59.82.2, <https://stacks.math.columbia.edu/tag/09ZF>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section LocalRepresentatives

variable {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y) [IsClosedImmersion i]
  (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The map from the base change `U ×_Y Y₀` of an étale `Y`-scheme to the terminal étale
`Y₀`-scheme. -/
noncomputable def toTerminalOfPullback (U : Y.Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ i).obj U ⟶ Scheme.Etale.mk (𝟙 Y₀) :=
  MorphismProperty.Over.homMk (pullback.snd U.hom i) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms into the terminal étale `X`-scheme `X` are unique. -/
lemma _root_.AlgebraicGeometry.Scheme.Etale.hom_ext_mk_id {X : Scheme.{u}} {V : X.Etale}
    (a b : V ⟶ Scheme.Etale.mk (𝟙 X)) : a = b :=
  MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans ((MorphismProperty.Over.w a).trans
    ((MorphismProperty.Over.w b).symm.trans (Category.comp_id _))))

set_option backward.isDefEq.respectTransparency false in
/-- **Local representatives.** Let `i : Y₀ ⟶ Y` be a closed immersion and `t` a global section
of `i^* G`. Every point `y₀` of `Y₀` lies in the image of `U ×_Y Y₀` for some étale `U ⟶ Y`
with a section `g` of `G` over `U` whose restriction to `U ×_Y Y₀` is the restriction of `t`. -/
lemma exists_pullSection_eq_map (t : ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y₀)))) (y₀ : Y₀) :
    ∃ (U : Y.Etale) (g : G.obj.obj (op U)),
      y₀ ∈ Set.range (pullback.snd U.hom i) ∧
      pullSection i G (V := (MorphismProperty.Over.pullback @Etale ⊤ i).obj U)
          (pullback.fst U.hom i) pullback.condition g =
        ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (toTerminalOfPullback i U).op t := by
  let F := (i)^*[AddCommGrpCat.{u + 1}].obj G
  obtain ⟨V', a, U, φ, hφ, g, ⟨v, hv⟩, heq⟩ := exists_pullSection_eq i G t y₀
  let U₀ := (MorphismProperty.Over.pullback @Etale ⊤ i).obj U
  let D : F.obj.obj (op U₀) := pullSection i G (V := U₀) (pullback.fst U.hom i)
    pullback.condition g - F.obj.map (toTerminalOfPullback i U).op t
  let b : V' ⟶ U₀ := homToPullback i φ hφ
  have hb : F.obj.map b.op D = 0 := by
    rw [map_sub, map_pullSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Scheme.Etale.hom_ext_mk_id (b ≫ toTerminalOfPullback i U) a, heq, sub_eq_zero]
    exact pullSection_congr _ _ _ (by simp [b]) _
  have hbv : b.left v ∈ vanishingLocus F D := mem_vanishingLocus_of_map_eq_zero b hb v
  -- The vanishing locus of `D` is cut out by an open `O` of `U`.
  have hemb : Topology.IsEmbedding (pullback.fst U.hom i) :=
    (pullback.fst U.hom i).isClosedEmbedding.isEmbedding
  obtain ⟨O, hO, hOD⟩ := hemb.isOpen_iff.1 (isOpen_vanishingLocus D)
  let O' : U.left.Opens := ⟨O, hO⟩
  let U' : Y.Etale := Scheme.Etale.mk (O'.ι ≫ U.hom)
  let e : U' ⟶ U := MorphismProperty.Over.homMk O'.ι rfl
  refine ⟨U', G.obj.map e.op g, ?_, ?_⟩
  · -- the point `y₀` lies over `O`
    have hO₁ : pullback.fst U.hom i (b.left v) ∈ O := by
      rw [← Set.mem_preimage, hOD]
      exact hbv
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := U'.hom) (g := i)
      (⟨_, hO₁⟩ : O') y₀ (by
        change U.hom (pullback.fst U.hom i (b.left v)) = i y₀
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        congr 1
        rw [← hv]
        have := congrArg (fun c ↦ c.left)
          (Scheme.Etale.hom_ext_mk_id (b ≫ toTerminalOfPullback i U) a)
        rw [← this]
        rfl)
    exact ⟨z, hz⟩
  · -- the difference vanishes everywhere on `U' ×_Y Y₀`
    let c : (MorphismProperty.Over.pullback @Etale ⊤ i).obj U' ⟶ U₀ :=
      (MorphismProperty.Over.pullback @Etale ⊤ i).map e
    have hD : F.obj.map c.op D = 0 := by
      refine eq_zero_of_forall_mem_vanishingLocus fun z ↦ ?_
      rw [vanishingLocus_map, Set.mem_preimage, ← hOD, Set.mem_preimage]
      have hc : c.left ≫ pullback.fst U.hom i = pullback.fst U'.hom i ≫ O'.ι := by
        simp [c, e]
      change (c.left ≫ pullback.fst U.hom i) z ∈ O
      rw [hc, Scheme.Hom.comp_apply]
      exact (pullback.fst U'.hom i z).2
    rw [map_sub, map_pullSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Scheme.Etale.hom_ext_mk_id (c ≫ toTerminalOfPullback i U) (toTerminalOfPullback i U'),
      sub_eq_zero] at hD
    rw [← pullSection_comp]
    refine Eq.trans ?_ hD
    exact pullSection_congr _ _ _ (by simp [c, e]) _

end LocalRepresentatives

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms into the étale `X`-scheme given by a monomorphism are unique. -/
lemma _root_.AlgebraicGeometry.Scheme.Etale.hom_ext_mk_of_mono {X Z : Scheme.{u}} (j : Z ⟶ X)
    [Etale j] [Mono j] {V : X.Etale} (a b : V ⟶ Scheme.Etale.mk j) : a = b :=
  MorphismProperty.Over.Hom.ext ((cancel_mono j).1
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))

section GermEq

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The locus where two sections `s₁`, `s₂` of `F` over étale `X`-schemes `V₁`, `V₂` have the
same germ: the points of `X` in the image of some étale `W` mapping to both `V₁` and `V₂` on
which the restrictions of `s₁` and `s₂` agree. -/
def germEqLocus {V₁ V₂ : X.Etale} (s₁ : F.obj.obj (op V₁)) (s₂ : F.obj.obj (op V₂)) : Set X :=
  {x | ∃ (W : X.Etale) (a₁ : W ⟶ V₁) (a₂ : W ⟶ V₂) (w : W.left), W.hom w = x ∧
    F.obj.map a₁.op s₁ = F.obj.map a₂.op s₂}

variable {F}

lemma isOpen_germEqLocus {V₁ V₂ : X.Etale} (s₁ : F.obj.obj (op V₁)) (s₂ : F.obj.obj (op V₂)) :
    IsOpen (germEqLocus F s₁ s₂) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, a₁, a₂, w, rfl, h⟩
  exact ⟨Set.range W.hom, fun _ ⟨w', hw'⟩ ↦ ⟨W, a₁, a₂, w', hw', h⟩,
    W.hom.isOpenMap.isOpen_range, ⟨w, rfl⟩⟩

lemma range_subset_germEqLocus_self {V : X.Etale} (s : F.obj.obj (op V)) :
    Set.range V.hom ⊆ germEqLocus F s s :=
  fun _ ⟨w, hw⟩ ↦ ⟨V, 𝟙 V, 𝟙 V, w, hw, rfl⟩

lemma germEqLocus_symm {V₁ V₂ : X.Etale} (s₁ : F.obj.obj (op V₁)) (s₂ : F.obj.obj (op V₂)) :
    germEqLocus F s₁ s₂ ⊆ germEqLocus F s₂ s₁ :=
  fun _ ⟨W, a₁, a₂, w, hw, h⟩ ↦ ⟨W, a₂, a₁, w, hw, h.symm⟩

set_option backward.isDefEq.respectTransparency false in
lemma germEqLocus_trans {V₁ V₂ V₃ : X.Etale} [IsOpenImmersion V₂.hom] (s₁ : F.obj.obj (op V₁))
    (s₂ : F.obj.obj (op V₂)) (s₃ : F.obj.obj (op V₃)) :
    germEqLocus F s₁ s₂ ∩ germEqLocus F s₂ s₃ ⊆ germEqLocus F s₁ s₃ := by
  rintro x ⟨⟨W, a₁, a₂, w, rfl, h⟩, ⟨W', b₂, b₃, w', hw', h'⟩⟩
  have hww : a₂.left w = b₂.left w' := by
    apply V₂.hom.isOpenEmbedding.injective
    change (a₂.left ≫ V₂.hom) w = (b₂.left ≫ V₂.hom) w'
    rw [MorphismProperty.Over.w a₂, MorphismProperty.Over.w b₂]
    exact hw'.symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w w' hww
  refine ⟨overlap a₂ b₂, overlapFst a₂ b₂ ≫ a₁, overlapSnd a₂ b₂ ≫ b₃, z, ?_, ?_⟩
  · change (pullback.fst a₂.left b₂.left ≫ W.hom) z = _
    rw [Scheme.Hom.comp_apply, hz]
    rfl
  · have e : overlapFst a₂ b₂ ≫ a₂ = overlapSnd a₂ b₂ ≫ b₂ :=
      MorphismProperty.Over.Hom.ext (by simp [pullback.condition])
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, e, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      h', ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

end GermEq

section Sigma

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {ι : Type u}
  (E : ι → X.Etale)

instance : Etale (Sigma.desc fun k ↦ (E k).hom) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The disjoint union of a family of étale `X`-schemes, as an étale `X`-scheme. -/
noncomputable def sigmaEtale : X.Etale :=
  Scheme.Etale.mk (Sigma.desc fun k ↦ (E k).hom)

/-- The inclusion of a member into the disjoint union of a family of étale `X`-schemes. -/
noncomputable def sigmaEtaleι (k : ι) : E k ⟶ sigmaEtale E :=
  MorphismProperty.Over.homMk (Sigma.ι (fun k ↦ (E k).left) k) (Sigma.ι_desc _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Sections of an étale sheaf over the members of a family glue to a section over their
disjoint union. -/
lemma exists_map_sigmaEtaleι_eq (g : ∀ k, F.obj.obj (op (E k))) :
    ∃ s : F.obj.obj (op (sigmaEtale E)), ∀ k, F.obj.map (sigmaEtaleι E k).op s = g k := by
  refine exists_map_eq_of_compatible F (sigmaEtaleι E) (fun x ↦ ?_) g (fun k l ↦ ?_)
  · obtain ⟨⟨k, y⟩, rfl⟩ := (sigmaMk fun k ↦ (E k).left).surjective x
    exact ⟨k, y, by rw [sigmaMk_mk]; rfl⟩
  · by_cases hkl : k = l
    · subst hkl
      have : overlapFst (sigmaEtaleι E k) (sigmaEtaleι E k) =
          overlapSnd (sigmaEtaleι E k) (sigmaEtaleι E k) :=
        MorphismProperty.Over.Hom.ext ((cancel_mono (Sigma.ι (fun k ↦ (E k).left) k)).1
          pullback.condition)
      rw [this]
    · have : IsEmpty (overlap (sigmaEtaleι E k) (sigmaEtaleι E l)).left :=
        isEmpty_pullback_sigmaι_of_ne (fun k ↦ (E k).left) hkl
      exact eq_of_forall_exists_map_eq F _ _ fun x ↦ isEmptyElim x

end Sigma

section ClosedFibre

variable {Y Y₀ Y' Y'₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (r : Y' ⟶ Y)
  (i' : Y'₀ ⟶ Y') (r₀ : Y'₀ ⟶ Y₀) (hsq : i' ≫ r = r₀ ≫ i)
  (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of pulled back representatives to the closed fibre.** Let `g` be a section of
`G` over an étale `U ⟶ Y` whose restriction to `U ×_Y Y₀` is the restriction of a global section
`t` of `i^* G`. For a morphism `r : Y' ⟶ Y` with closed fibre `i' : Y'₀ ⟶ Y'` over `Y₀`, the
pullback `ψ^* g` of `g` along `ψ : V ⟶ U` (over `r`) restricts on the closed fibre to the
pullback of `t` along `Y'₀ ⟶ Y₀`. -/
lemma restrictAlong_pullSection_eq_restrictAlong {U : Y.Etale} (g : G.obj.obj (op U))
    (t : ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y₀))))
    (hg : pullSection i G (V := (MorphismProperty.Over.pullback @Etale ⊤ i).obj U)
        (pullback.fst U.hom i) pullback.condition g =
      ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (toTerminalOfPullback i U).op t)
    {V : Y'.Etale} (ψ : V.left ⟶ U.left) (hψ : ψ ≫ U.hom = V.hom ≫ r) {V' : Y'₀.Etale}
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ i') :
    restrictAlong r G i' (i' ≫ r) rfl m hm (pullSection r G ψ hψ g) =
      restrictAlong i G r₀ (i' ≫ r) hsq (V := Scheme.Etale.mk (𝟙 Y₀)) (V' := V')
        (V'.hom ≫ r₀) (Category.comp_id _) t := by
  rw [restrictAlong_pullSection]
  let ℓ : V'.left ⟶ pullback U.hom i := pullback.lift (m ≫ ψ) (V'.hom ≫ r₀) (by
    rw [Category.assoc, hψ, ← Category.assoc, hm, Category.assoc, hsq, Category.assoc])
  have hℓ : ℓ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ i).obj U).hom = V'.hom ≫ r₀ :=
    pullback.lift_snd _ _ _
  rw [restrictAlong_congr i G r₀ (i' ≫ r) hsq (Category.comp_id _)
      (show V'.hom ≫ r₀ = ℓ ≫ (toTerminalOfPullback i U).left from (pullback.lift_snd _ _ _).symm),
    ← restrictAlong_map i G r₀ (i' ≫ r) hsq (toTerminalOfPullback i U) ℓ hℓ, ← hg,
    restrictAlong_pullSection]
  exact pullSection_congr _ _ _ (pullback.lift_fst _ _ _).symm _

end ClosedFibre

section Glue

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The open immersion of an open subscheme, as a morphism to the terminal étale `X`-scheme. -/
noncomputable def opensToTerminal (N : X.Opens) :
    Scheme.Etale.mk N.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk N.ι (Category.comp_id _)

/-- The inclusion of open subschemes `N ≤ N'`, as a morphism of étale `X`-schemes. -/
noncomputable def opensHomOfLE {N N' : X.Opens} (h : N ≤ N') :
    Scheme.Etale.mk N.ι ⟶ Scheme.Etale.mk N'.ι :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h)

set_option backward.isDefEq.respectTransparency false in
/-- **Gluing sections near a closed subset of a spectral scheme.** Let `X` be a quasi-compact
quasi-separated scheme and `T₀ ⊆ X` a closed subset meeting every irreducible closed subset in
a nonempty connected set. Let `σ_m` be sections of `F` over finitely many quasi-compact opens
`N_m` covering `T₀`, any two of which have the same germs along `T₀`. Then there are a global
section `σ'` and opens `W_m ⊆ N_m` containing `N_m ∩ T₀` on which `σ'` restricts to `σ_m`. -/
lemma exists_glue_of_isConnected_inter [CompactSpace X] [QuasiSeparatedSpace X] {T₀ : Set X}
    (hT₀ : IsClosed T₀) (hC : ∀ C : Set X, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    {M : Type*} [Finite M] (N : M → X.Opens) (hNc : ∀ m, IsCompact (N m : Set X))
    (hcov : T₀ ⊆ ⋃ m, (N m : Set X)) (σ : ∀ m, F.obj.obj (op (Scheme.Etale.mk (N m).ι)))
    (hagree : ∀ m n, (N m : Set X) ∩ N n ∩ T₀ ⊆ germEqLocus F (σ m) (σ n)) :
    ∃ (σ' : F.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) (W : M → X.Opens) (hW : ∀ m, W m ≤ N m),
      (∀ m, (N m : Set X) ∩ T₀ ⊆ W m) ∧
      ∀ m, F.obj.map (opensToTerminal (W m)).op σ' = F.obj.map (opensHomOfLE (hW m)).op (σ m) := by
  have : SpectralSpace X := {}
  have : ∀ n, IsOpenImmersion (Scheme.Etale.mk (N n).ι).hom :=
    fun n ↦ inferInstanceAs (IsOpenImmersion (N n).ι)
  obtain ⟨W, hWo, hWN, hWcov, hWagree, hNW⟩ := SpectralSpace.exists_shrink_of_isConnected_inter
    hT₀ hC (fun m ↦ (N m : Set X)) (fun m ↦ (N m).2) hNc hcov
    (fun m n ↦ germEqLocus F (σ m) (σ n)) (fun m n ↦ isOpen_germEqLocus _ _)
    (fun m x hx ↦ ⟨Scheme.Etale.mk (N m).ι, 𝟙 _, 𝟙 _, ⟨x, hx⟩, rfl, rfl⟩)
    (fun m n ↦ germEqLocus_symm _ _) (fun m n k ↦ germEqLocus_trans _ _ _) hagree
  let W' : M → X.Opens := fun m ↦ ⟨W m, hWo m⟩
  have hW' : ∀ m, W' m ≤ N m := hWN
  let σ'' : ∀ m, F.obj.obj (op (Scheme.Etale.mk (W' m).ι)) :=
    fun m ↦ F.obj.map (opensHomOfLE (hW' m)).op (σ m)
  obtain ⟨σ', hσ'⟩ := exists_map_eq_of_compatible F (fun m ↦ opensToTerminal (W' m))
    (fun x ↦ by
      obtain ⟨m, hm⟩ := hWcov x
      exact ⟨m, ⟨x, hm⟩, rfl⟩) σ'' (fun m n ↦ by
      refine eq_of_forall_exists_map_eq F _ _ fun x ↦ ?_
      let O := overlap (opensToTerminal (W' m)) (opensToTerminal (W' n))
      have hy : O.hom x ∈ W m ∩ W n := by
        refine ⟨?_, ?_⟩
        · change (pullback.fst (W' m).ι (W' n).ι ≫ (W' m).ι) x ∈ W' m
          rw [Scheme.Hom.comp_apply]
          exact (pullback.fst (W' m).ι (W' n).ι x).2
        · change (pullback.fst (W' m).ι (W' n).ι ≫ (W' m).ι) x ∈ W' n
          rw [pullback.condition, Scheme.Hom.comp_apply]
          exact (pullback.snd (W' m).ι (W' n).ι x).2
      obtain ⟨Wt, b₁, b₂, w, hw, hb⟩ := hWagree m n hy
      let qO : O ⟶ Scheme.Etale.mk (𝟙 X) := MorphismProperty.Over.homMk O.hom (Category.comp_id _)
      let qW : Wt ⟶ Scheme.Etale.mk (𝟙 X) :=
        MorphismProperty.Over.homMk Wt.hom (Category.comp_id _)
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := qO.left)
        (g := qW.left) x w hw.symm
      refine ⟨overlap qO qW, overlapFst qO qW, ⟨z, hz₁⟩, ?_⟩
      simp only [σ'', ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rw [Scheme.Etale.hom_ext_mk_of_mono (N m).ι
          (overlapFst qO qW ≫ overlapFst _ _ ≫ opensHomOfLE (hW' m)) (overlapSnd qO qW ≫ b₁),
        Scheme.Etale.hom_ext_mk_of_mono (N n).ι
          (overlapFst qO qW ≫ overlapSnd _ _ ≫ opensHomOfLE (hW' n)) (overlapSnd qO qW ≫ b₂),
        op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hb, op_comp, Functor.map_comp,
        ConcreteCategory.comp_apply])
  exact ⟨σ', W', hW', hNW, hσ'⟩

end Glue

section HenselianPair

variable {A : Type u} [CommRing A] (I : Ideal A)

lemma range_specMap_quotientMk :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  have := range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at this
  exact this

variable {Y Y₀ : Scheme.{u}} (p : Y ⟶ Spec (.of A)) (i : Y₀ ⟶ Y)
  (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
  (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

include h in
/-- The closed fibre over `V(I)` of a scheme over `Spec A` is the preimage of `V(I)`. -/
lemma range_eq_preimage_zeroLocus_of_isPullback :
    Set.range i = p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst,
    range_specMap_quotientMk]

include h in
/-- The closed fibre over `V(I)` is a closed immersion. -/
lemma isClosedImmersion_of_isPullback : IsClosedImmersion i :=
  MorphismProperty.of_isPullback h.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
      Ideal.Quotient.mk_surjective)

end HenselianPair

/-- Two sections of an étale sheaf over an étale scheme with no points agree. -/
lemma eq_of_isEmpty {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : X.Etale} [IsEmpty V.left] (s₁ s₂ : F.obj.obj (op V)) : s₁ = s₂ :=
  eq_of_forall_exists_map_eq F _ _ fun x ↦ isEmptyElim x

section SigmaClosedFibre

variable {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
  (t : ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y₀))))

set_option backward.isDefEq.respectTransparency false in
/-- If sections `g_k` over étale `E_k ⟶ Y` restrict to `t` on the `E_k ×_Y Y₀`, then so does the
section they induce on the disjoint union of the `E_k`. -/
lemma pullSection_sigmaEtale_eq {ι : Type u} (E : ι → Y.Etale) (gE : ∀ k, G.obj.obj (op (E k)))
    (hE : ∀ k, pullSection i G (V := (MorphismProperty.Over.pullback @Etale ⊤ i).obj (E k))
        (pullback.fst (E k).hom i) pullback.condition (gE k) =
      ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (toTerminalOfPullback i (E k)).op t)
    (gt : G.obj.obj (op (sigmaEtale E))) (hgt : ∀ k, G.obj.map (sigmaEtaleι E k).op gt = gE k) :
    pullSection i G (V := (MorphismProperty.Over.pullback @Etale ⊤ i).obj (sigmaEtale E))
        (pullback.fst (sigmaEtale E).hom i) pullback.condition gt =
      ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.map
        (toTerminalOfPullback i (sigmaEtale E)).op t := by
  refine eq_of_forall_exists_map_eq _ _ _ fun z ↦ ?_
  obtain ⟨⟨k, y⟩, hky⟩ := (sigmaMk fun k ↦ (E k).left).surjective
    (pullback.fst (sigmaEtale E).hom i z)
  let c := (MorphismProperty.Over.pullback @Etale ⊤ i).map (sigmaEtaleι E k)
  have hc : c.left = pullback.map (E k).hom i (sigmaEtale E).hom i (sigmaEtaleι E k).left (𝟙 _)
      (𝟙 _) (by simp [sigmaEtaleι, sigmaEtale]) (by simp) := by
    apply pullback.hom_ext <;> simp [c]
  have hz : z ∈ Set.range c.left := by
    have hr := Scheme.Pullback.range_map (E k).hom i (sigmaEtale E).hom i
      (sigmaEtaleι E k).left (𝟙 _) (𝟙 _) (by simp [sigmaEtaleι, sigmaEtale]) (by simp)
    have hmem : z ∈
        pullback.fst (sigmaEtale E).hom i ⁻¹' Set.range (sigmaEtaleι E k).left ∩
          pullback.snd (sigmaEtale E).hom i ⁻¹' Set.range (𝟙 Y₀) := by
      refine ⟨⟨y, ?_⟩, ⟨pullback.snd (sigmaEtale E).hom i z, rfl⟩⟩
      rw [← hky, sigmaMk_mk]
      rfl
    rw [hc]
    exact hr.symm ▸ hmem
  refine ⟨_, c, hz, ?_⟩
  rw [map_pullSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Scheme.Etale.hom_ext_mk_id (c ≫ toTerminalOfPullback i (sigmaEtale E))
      (toTerminalOfPullback i (E k)), ← hE k, ← hgt k, ← pullSection_comp]
  exact pullSection_congr _ _ _ (by simp [c, sigmaEtaleι]) _

end SigmaClosedFibre

section Main

variable {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}}
  (p : Y ⟶ Spec (.of A)) [IsProper p] (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
  (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
include h in
/-- **Injectivity of restriction to the closed fibre over a henselian pair.** -/
lemma injective_pullSection_of_henselianRing :
    Function.Injective (pullSection i G (V := Scheme.Etale.mk (𝟙 Y₀))
      (U := Scheme.Etale.mk (𝟙 Y)) i ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  intro g₁ g₂ heq
  rw [← sub_eq_zero]
  refine eq_zero_of_pullSection_eq_zero (V := Scheme.Etale.mk (𝟙 Y₀)) (U := Scheme.Etale.mk (𝟙 Y))
    i G i ((Category.comp_id _).trans (Category.id_comp _).symm) (fun C hC hne ↦ ?_) (g₁ - g₂)
    (by rw [pullSection_sub, heq, sub_self])
  have hr := range_eq_preimage_zeroLocus_of_isPullback I p i p₀ h
  have := p.nonempty_inter_preimage_zeroLocus I HenselianRing.jac (C := C) hC hne
  rw [← hr] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
include h in
/-- **Surjectivity of restriction to the closed fibre over a henselian pair**, first step: the
local representatives of a section `t` over `Y₀` assemble to a section `g` over a surjective
étale `U ⟶ Y` whose restriction to `U ×_Y Y₀` is the restriction of `t`. -/
lemma exists_surjective_etale_pullSection_eq
    (t : ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y₀)))) :
    ∃ (U : Y.Etale) (_ : Surjective U.hom) (g : G.obj.obj (op U)),
      pullSection i G (V := (MorphismProperty.Over.pullback @Etale ⊤ i).obj U)
          (pullback.fst U.hom i) pullback.condition g =
        ((i)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (toTerminalOfPullback i U).op t := by
  have : IsClosedImmersion i := isClosedImmersion_of_isPullback I p i p₀ h
  choose U g hy hg using exists_pullSection_eq_map i G t
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace Y₀ := i.isClosedEmbedding.compactSpace
  obtain ⟨K, hK⟩ := isCompact_univ.elim_finite_subcover
    (fun y₀ : Y₀ ↦ Set.range (pullback.snd (U y₀).hom i))
    (fun y₀ ↦ (pullback.snd (U y₀).hom i).isOpenMap.isOpen_range)
    (fun y₀ _ ↦ Set.mem_iUnion.2 ⟨y₀, hy y₀⟩)
  let Yc : Y.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let E : Option K → Y.Etale := fun o ↦ Option.elim o (Scheme.Etale.mk Yc.ι) (fun k ↦ U k.1)
  let gE : ∀ o, G.obj.obj (op (E o)) := fun o ↦ match o with
    | none => 0
    | some k => g k.1
  obtain ⟨gt, hgt⟩ := exists_map_sigmaEtaleι_eq G E gE
  have hι : ∀ o, Sigma.ι (fun o ↦ (E o).left) o ≫ (sigmaEtale E).hom = (E o).hom :=
    fun o ↦ Sigma.ι_desc _ _
  refine ⟨sigmaEtale E, ⟨fun y ↦ ?_⟩, gt, pullSection_sigmaEtale_eq i G t E gE (fun o ↦ ?_) gt hgt⟩
  · by_cases hyi : y ∈ Set.range i
    · obtain ⟨y₀, rfl⟩ := hyi
      obtain ⟨k, hk, z, hz⟩ := Set.mem_iUnion₂.1 (hK (Set.mem_univ y₀))
      refine ⟨Sigma.ι (fun o ↦ (E o).left) (some ⟨k, hk⟩) (pullback.fst (U k).hom i z), ?_⟩
      change (Sigma.ι (fun o ↦ (E o).left) (some ⟨k, hk⟩) ≫ (sigmaEtale E).hom) _ = _
      rw [hι]
      change ((pullback.fst (U k).hom i ≫ (U k).hom) z) = _
      rw [pullback.condition, Scheme.Hom.comp_apply, hz]
      rfl
    · refine ⟨Sigma.ι (fun o ↦ (E o).left) none ⟨y, hyi⟩, ?_⟩
      change (Sigma.ι (fun o ↦ (E o).left) none ≫ (sigmaEtale E).hom) _ = _
      rw [hι]
      rfl
  · cases o with
    | none =>
      have : IsEmpty ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (E none)).left :=
        ⟨fun w ↦ by
        have h₁ : ((E none).hom ((pullback.fst (E none).hom i) w)) ∈ (Set.range i)ᶜ :=
          ((pullback.fst (E none).hom i) w).2
        apply h₁
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩⟩
      exact eq_of_isEmpty _ _ _
    | some k => exact hg k.1

end Main

end AlgebraicGeometry.Etale
