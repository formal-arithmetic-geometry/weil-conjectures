module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotientPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Admissible free finite-group quotients

Source: Stacks Project, spaces-properties.tex, Tags 07S6, 07S7 and 0BBM(4)
(blueprint: lem-sfb-admissible-free-finite-quotient).

The action relation is the coproduct of copies of M. A map into this coproduct
amounts to a locally constant group label on the test scheme and a map to M;
its two projections are the action and the forgetful map. Thus their presheaf
coequalizer is exactly the quotient by G_T(T), including disconnected tests.
Sheafification is specified by the universal property of sheafificationAdjunction.
The base-changed relation maps are fixed by both scheme pullback projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The source map of the constant finite-group action relation is the fold.
It is the projection G_{Spec Z} times M to M under the coproduct identification.
Source: Stacks, Tag 07S6, constant-group specialization of the relation
(blueprint: lem-sfb-admissible-free-finite-quotient). -/
def finiteActionRelationSource (M : Scheme.{u}) (G : Type v) [Group G] [Finite G] :
    (∐ fun _ : G ↦ M) ⟶ M :=
  Sigma.desc (fun _ : G ↦ 𝟙 M)

/-- The target map of the constant finite-group action relation is (g,m) to gm.
Source: Stacks, Tags 07S6 and 07S7, action equivalence relation
(blueprint: lem-sfb-admissible-free-finite-quotient). -/
def finiteActionRelationTarget {M : Scheme.{u}} {G : Type v} [Group G] [Finite G]
    (a : G →* Aut M) : (∐ fun _ : G ↦ M) ⟶ M :=
  Sigma.desc (fun g : G ↦ (a g).hom)

private theorem invariant_affine_neighborhood {M : Scheme.{u}} [M.IsSeparated]
    {G : Type v} [Group G] [Finite G] (a : G →* Aut M) (x : M)
    (hx : ∃ U : M.affineOpens, ∀ g : G, (a g).hom x ∈ U.1) :
    ∃ U : M.affineOpens, x ∈ U.1 ∧ ∀ g : G, (a g).hom ⁻¹ᵁ U.1 = U.1 := by
  obtain ⟨U, hU⟩ := hx
  let W : M.Opens := ⨅ g : G, (a g).hom ⁻¹ᵁ U.1
  have hW (y : M) : y ∈ W ↔ ∀ g : G, (a g).hom y ∈ U.1 := by
    simp only [W, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    rfl
  have haff : IsAffineOpen W :=
    IsAffineOpen.iInf (fun g : G ↦ U.2.preimage_of_isIso (a g).hom)
  refine ⟨⟨W, haff⟩, (hW x).2 hU, fun g ↦ ?_⟩
  have hmul (h k : G) (y : M) : (a h).hom ((a k).hom y) = (a (h * k)).hom y := by
    rw [map_mul]
    rfl
  apply le_antisymm
  · intro y hy
    change (a g).hom y ∈ W at hy
    apply (hW y).2
    intro k
    have hk := (hW _).1 hy (k * g⁻¹)
    simpa only [hmul, inv_mul_cancel_right] using hk
  · intro y hy
    change (a g).hom y ∈ W
    apply (hW _).2
    intro k
    rw [hmul]
    exact (hW y).1 hy (k * g)

private theorem uy_comp {X Y : Scheme.{u}} {F : Scheme.{u}ᵒᵖ ⥤ Type (max (u + 1) w)}
    (f : X ⟶ Y) (b : uliftYoneda.{max (u + 1) w}.obj Y ⟶ F) :
    uliftYonedaEquiv (uliftYoneda.map f ≫ b) = F.map f.op (uliftYonedaEquiv b) :=
  (uliftYonedaEquiv_naturality b f.op).symm

private theorem sheaf_descent {U R Q : Scheme.{u}} (s t : R ⟶ U) (q : U ⟶ Q)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    (hp : IsPullback s t q q)
    (F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)))
    (b : uliftYoneda.{max (u + 1) w}.obj U ⟶ F.obj)
    (hb : uliftYoneda.map s ≫ b = uliftYoneda.map t ≫ b) :
    ∃! c : uliftYoneda.{max (u + 1) w}.obj Q ⟶ F.obj,
      uliftYoneda.map q ≫ c = b := by
  have hF : Presieve.IsSheafFor F.obj (Presieve.singleton q) :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type _ _).1 F.property _
        (Precoverage.generate_mem_toGrothendieck q.singleton_mem_fppfPrecoverage))
  obtain ⟨c, hc, hu⟩ := (Presieve.isSheafFor_singleton (P := F.obj)).1 hF
    (uliftYonedaEquiv b) (by
      intro Z p₁ p₂ he
      let r := hp.lift p₁ p₂ he
      have h₁ : r ≫ s = p₁ := hp.lift_fst _ _ _
      have h₂ : r ≫ t = p₂ := hp.lift_snd _ _ _
      have hb' := congrArg uliftYonedaEquiv hb
      rw [uy_comp, uy_comp] at hb'
      rw [← h₁, ← h₂]
      simpa only [op_comp, Functor.map_comp, types_comp_apply] using
        congrArg (fun x ↦ F.obj.map r.op x) hb')
  refine ⟨uliftYonedaEquiv.symm c, ?_, ?_⟩
  · apply uliftYonedaEquiv.injective
    change F.obj.map q.op c = uliftYonedaEquiv b
    exact hc
  · intro d hd
    apply uliftYonedaEquiv.injective
    have hd' := congrArg uliftYonedaEquiv hd
    rw [uy_comp] at hd'
    simpa only [Equiv.apply_symm_apply] using hu (uliftYonedaEquiv d) hd'

private theorem sheaf_quotient {U R Q : Scheme.{u}} (s t : R ⟶ U) (q : U ⟶ Q)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    (hp : IsPullback s t q q) :
    ∃ η : coequalizer (uliftYoneda.{max (u + 1) w}.map s) (uliftYoneda.map t) ⟶
        uliftYoneda.{max (u + 1) w}.obj Q,
      coequalizer.π (uliftYoneda.map s) (uliftYoneda.map t) ≫ η = uliftYoneda.map q ∧
      ∀ F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)),
        Function.Bijective (fun k : uliftYoneda.{max (u + 1) w}.obj Q ⟶ F.obj ↦ η ≫ k) := by
  let η : coequalizer (uliftYoneda.{max (u + 1) w}.map s)
      (uliftYoneda.{max (u + 1) w}.map t) ⟶
        uliftYoneda.{max (u + 1) w}.obj Q :=
    coequalizer.desc (uliftYoneda.map q) (by
      rw [← Functor.map_comp, ← Functor.map_comp, hp.w])
  have hη : coequalizer.π (uliftYoneda.map s) (uliftYoneda.map t) ≫ η =
      uliftYoneda.{max (u + 1) w}.map q := coequalizer.π_desc _ _
  refine ⟨η, hη, fun F ↦ ⟨?_, ?_⟩⟩
  · intro c d he
    change η ≫ c = η ≫ d at he
    have hcd : uliftYoneda.map q ≫ c = uliftYoneda.map q ≫ d := by
      rw [← hη, Category.assoc, Category.assoc, he]
    obtain ⟨e, he, hu⟩ := sheaf_descent s t q hp F (uliftYoneda.map q ≫ d)
      (by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k ↦ uliftYoneda.{max (u + 1) w}.map k ≫ d) hp.w)
    exact (hu c hcd).trans (hu d rfl).symm
  · intro b
    obtain ⟨c, hc, -⟩ := sheaf_descent s t q hp F
      (coequalizer.π (uliftYoneda.map s) (uliftYoneda.map t) ≫ b)
      (by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ b)
          (coequalizer.condition (uliftYoneda.{max (u + 1) w}.map s)
            (uliftYoneda.{max (u + 1) w}.map t)))
    refine ⟨c, ?_⟩
    apply coequalizer.hom_ext
    rw [← Category.assoc, hη, hc]

private theorem sheaf_action_invariant {M : Scheme.{u}} {G : Type v} [Group G] [Finite G]
    (a : G →* Aut M) (F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)))
    (b : uliftYoneda.{max (u + 1) w}.obj M ⟶ F.obj)
    (hb : ∀ g : G, uliftYoneda.map (a g).hom ≫ b = b) :
    uliftYoneda.map (finiteActionRelationTarget a) ≫ b =
      uliftYoneda.map (finiteActionRelationSource M G) ≫ b := by
  apply uliftYonedaEquiv.injective
  let 𝒰 := sigmaOpenCover (fun _ : G ↦ M)
  have hcover : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fppfTopology (∐ fun _ : G ↦ M) :=
    Precoverage.generate_mem_toGrothendieck
      (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ 𝒰.mem₀)
  have hsF := (Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property _ hcover)
  apply hsF.isSeparatedFor.ext
  intro Z p hp
  cases hp with
  | mk g =>
    change F.obj.map (Sigma.ι (fun _ : G ↦ M) g).op _ =
      F.obj.map (Sigma.ι (fun _ : G ↦ M) g).op _
    rw [← uy_comp, ← uy_comp]
    apply congrArg uliftYonedaEquiv
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    change uliftYoneda.map (Sigma.ι (fun _ : G ↦ M) g ≫
        Sigma.desc (fun h : G ↦ (a h).hom)) ≫ b =
      uliftYoneda.map (Sigma.ι (fun _ : G ↦ M) g ≫
        Sigma.desc (fun _ : G ↦ 𝟙 M)) ≫ b
    rw [Sigma.ι_desc, Sigma.ι_desc]
    exact (hb g).trans (by
      change b = uliftYoneda.{max (u + 1) w}.map (𝟙 M) ≫ b
      rw [CategoryTheory.Functor.map_id, Category.id_comp])

private theorem field_point_factors_sigma {M : Scheme.{u}} {G : Type v} [Finite G]
    (Ω : Type u) [Field Ω] (r : Spec (.of Ω) ⟶ ∐ fun _ : G ↦ M) :
    ∃ (g : G) (x : Spec (.of Ω) ⟶ M), r = x ≫ Sigma.ι (fun _ : G ↦ M) g := by
  let 𝒰 := sigmaOpenCover (fun _ : G ↦ M)
  let g := 𝒰.idx (r (IsLocalRing.closedPoint Ω))
  obtain ⟨z, hz⟩ := 𝒰.covers (r (IsLocalRing.closedPoint Ω))
  have hr : Set.range r ⊆ Set.range (Sigma.ι (fun _ : G ↦ M) g) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨z, hz.trans (congrArg r (Subsingleton.elim _ _))⟩
  exact ⟨g, IsOpenImmersion.lift (Sigma.ι (fun _ : G ↦ M) g) r hr,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩

private theorem baseChange_relation {U R Q T : Scheme.{u}} (s t : R ⟶ U) (q : U ⟶ Q)
    (hp : IsPullback t s q q) (f : T ⟶ Q) :
    ∃ sT tT : pullback (s ≫ q) f ⟶ pullback q f,
      sT ≫ pullback.fst q f = pullback.fst (s ≫ q) f ≫ s ∧
      sT ≫ pullback.snd q f = pullback.snd (s ≫ q) f ∧
      tT ≫ pullback.fst q f = pullback.fst (s ≫ q) f ≫ t ∧
      tT ≫ pullback.snd q f = pullback.snd (s ≫ q) f ∧
      IsPullback tT sT (pullback.snd q f) (pullback.snd q f) := by
  let sT : pullback (s ≫ q) f ⟶ pullback q f := pullback.lift
    (pullback.fst (s ≫ q) f ≫ s) (pullback.snd (s ≫ q) f)
    (by simp only [Category.assoc, pullback.condition])
  let tT : pullback (s ≫ q) f ⟶ pullback q f := pullback.lift
    (pullback.fst (s ≫ q) f ≫ t) (pullback.snd (s ≫ q) f)
    (by rw [Category.assoc, hp.w, pullback.condition])
  refine ⟨sT, tT, by simp [sT], by simp [sT], by simp [tT], by simp [tT], ?_⟩
  apply IsPullback.mk' (by simp [sT, tT])
  · intro W l l' h₁ h₂
    apply pullback.hom_ext
    · apply hp.hom_ext
      · simpa [tT] using congrArg (fun k ↦ k ≫ pullback.fst q f) h₁
      · simpa [sT] using congrArg (fun k ↦ k ≫ pullback.fst q f) h₂
    · simpa [sT] using congrArg (fun k ↦ k ≫ pullback.snd q f) h₂
  · intro W a b he
    let r := hp.lift (a ≫ pullback.fst q f) (b ≫ pullback.fst q f) (by
      simp only [Category.assoc, pullback.condition]
      exact congrArg (fun k ↦ k ≫ f) he)
    have hr : r ≫ s ≫ q = (b ≫ pullback.snd q f) ≫ f := by
      simp [r, pullback.condition]
    refine ⟨pullback.lift r (b ≫ pullback.snd q f) hr, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [tT, r]
      · simpa [tT] using he.symm
    · apply pullback.hom_ext <;> simp [sT, r]

/-- An admissible free finite-group action has a separated scheme fppf quotient,
with its specified torsor relation, arbitrary base-change quotient property,
universal invariant-map property, geometric orbit fibres and quasi-compactness.
All schemes have their unique structure over Spec Z. The coequalizers below are
the sectionwise orbit presheaves; their universal arrows specify sheafification.

Source: Stacks Project, spaces-properties.tex, Tags 07S6, 07S7 and 0BBM(4)
(blueprint: lem-sfb-admissible-free-finite-quotient).

Proof (the node's ten steps):
1. The fold of finitely many copies of any scheme is finite etale: on Spec A it
   is Spec of the finite free product algebra, with coordinate idempotent basis.
   Each summand is open and the fold there is the identity, so source-local
   etaleness (lem-sfb-scheme-etale-source-target-properties) applies. This also
   handles the empty scheme and zero ring (lem-weil-pbc-scheme-coproduct-family).
2. Form the action groupoid (def-a1-groupoid-scheme) on the coproduct. Its source
   is the fold and its target is the fold after (g,m) to (g,gm), an automorphism.
   The action laws give identities, inverses and composition. Freeness is the
   monomorphic relation on all test schemes, even disconnected ones.
3. Apply lem-trf-etale-relation-quotient to obtain the algebraic-space quotient
   sheaf, etale local lifts, kernel-pair identity and sheaf universal property.
4. By lem-sfb-locally-free-groupoid-invariant-affine each point orbit has an
   invariant affine neighborhood. On it the relation is the coproduct of its
   translates. Apply lem-a1-finite-flat-affine-relation-quotient (03BM) to obtain
   its affine invariant-spectrum quotient and finite locally free projection.
5. By lem-trf-etale-relation-finding-opens these quotient charts are open in the
   quotient sheaf. The local lifts of step 3 and the covering of M show that
   they cover every test scheme. Apply lem-pc-schemes-criterion to glue Q.
   For empty M the empty open-cover criterion gives the empty scheme.
6. The presentation makes q etale surjective and identifies the prescribed
   action relation with its kernel pair. It is an fppf, hence fpqc cover.
   Its self-base-change is the finite fold; lem-weil-pbc-fpqc-descend-finite
   descends finiteness to q, without assuming the desired conclusion.
7. Finite implies proper (lem-weil-pbc-finite-proper), hence universally closed.
   Apply lem-weil-pbc-surjective-universally-closed-separated to M over Spec Z
   to deduce the separatedness of Q, i.e. its closed absolute diagonal.
8. Base change preserves finite, etale and surjective morphisms and the actual
   action kernel-pair square. The relation maps are precisely the two maps
   characterized below. Apply lem-a1-fppf-kernel-pair-quotient-descent to give
   the base-changed orbit sheaf represented by T. An invariant map to any fppf
   sheaf descends first to the orbit presheaf, then uniquely through its
   sheafification (def-weil-pbc-sheafification), also after base change.
9. Over an algebraically closed field, each nonempty finite fibre has a point
   by lem-sc-finite-nonempty-point. Thus q is onto on field-valued points.
   The kernel-pair identity identifies equal images with a group label taking
   one lift to the other. Spec of a field is connected, so the label is a
   single element of G, giving exactly the stated geometric orbit fibres.
10. Pull back an open cover of Q to M. If M is quasi-compact, finitely many
    inverse images cover M, hence the corresponding opens cover Q by
    surjectivity. No step assumes Noetherianity, finite type, or division by |G|.
-/
theorem exists_admissible_free_finite_quotient
    (M : Scheme.{u}) [M.IsSeparated] (G : Type v) [Group G] [Finite G]
    (a : G →* Aut M)
    [Mono (prod.lift (finiteActionRelationTarget a) (finiteActionRelationSource M G))]
    (horbit : ∀ x : M, ∃ U : M.affineOpens, ∀ g : G, (a g).hom x ∈ U.1) :
    ∃ (Q : Scheme.{u}) (q : M ⟶ Q),
      Q.IsSeparated ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧
      IsPullback (finiteActionRelationTarget a) (finiteActionRelationSource M G) q q ∧
      (∃ η : coequalizer (uliftYoneda.{max (u + 1) w}.map (finiteActionRelationTarget a))
          (uliftYoneda.{max (u + 1) w}.map (finiteActionRelationSource M G)) ⟶
            uliftYoneda.{max (u + 1) w}.obj Q,
        coequalizer.π (uliftYoneda.{max (u + 1) w}.map (finiteActionRelationTarget a))
            (uliftYoneda.{max (u + 1) w}.map (finiteActionRelationSource M G)) ≫ η =
          uliftYoneda.{max (u + 1) w}.map q ∧
        ∀ F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)),
          Function.Bijective (fun k : uliftYoneda.{max (u + 1) w}.obj Q ⟶ F.obj ↦ η ≫ k)) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ Q),
        ∃ sT tT : pullback (finiteActionRelationSource M G ≫ q) f ⟶ pullback q f,
          sT ≫ pullback.fst q f =
            pullback.fst (finiteActionRelationSource M G ≫ q) f ≫
              finiteActionRelationSource M G ∧
          sT ≫ pullback.snd q f = pullback.snd (finiteActionRelationSource M G ≫ q) f ∧
          tT ≫ pullback.fst q f =
            pullback.fst (finiteActionRelationSource M G ≫ q) f ≫
              finiteActionRelationTarget a ∧
          tT ≫ pullback.snd q f = pullback.snd (finiteActionRelationSource M G ≫ q) f ∧
          ∃ ηT : coequalizer (uliftYoneda.{max (u + 1) w}.map tT)
              (uliftYoneda.{max (u + 1) w}.map sT) ⟶ uliftYoneda.{max (u + 1) w}.obj T,
            coequalizer.π (uliftYoneda.{max (u + 1) w}.map tT)
                (uliftYoneda.{max (u + 1) w}.map sT) ≫ ηT =
              uliftYoneda.{max (u + 1) w}.map (pullback.snd q f) ∧
            ∀ F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)),
              Function.Bijective
                (fun k : uliftYoneda.{max (u + 1) w}.obj T ⟶ F.obj ↦ ηT ≫ k)) ∧
      (∀ (F : Sheaf Scheme.fppfTopology (Type (max (u + 1) w)))
          (b : uliftYoneda.{max (u + 1) w}.obj M ⟶ F.obj),
        (∀ g : G, uliftYoneda.{max (u + 1) w}.map (a g).hom ≫ b = b) →
        ∃! c : uliftYoneda.{max (u + 1) w}.obj Q ⟶ F.obj,
          uliftYoneda.{max (u + 1) w}.map q ≫ c = b) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective (fun x : Spec (.of Ω) ⟶ M ↦ x ≫ q) ∧
        ∀ x y : Spec (.of Ω) ⟶ M,
          x ≫ q = y ≫ q ↔ ∃ g : G, x ≫ (a g).hom = y) ∧
      (CompactSpace M → CompactSpace Q) := by
  have hmono : Mono (prod.lift (Sigma.desc (fun g : G ↦ (a g).hom))
      (Sigma.desc (fun _ : G ↦ 𝟙 M))) :=
    inferInstanceAs (Mono
      (prod.lift (finiteActionRelationTarget a) (finiteActionRelationSource M G)))
  obtain ⟨Q, q, hqe, hqs, hp⟩ :=
    exists_admissible_free_finite_quotient_presentation M G a
      (fun x ↦ invariant_affine_neighborhood a x (horbit x))
  change IsPullback (finiteActionRelationTarget a) (finiteActionRelationSource M G) q q at hp
  have : Etale q := hqe
  have : Surjective q := hqs
  have hfold : IsFinite (finiteActionRelationSource M G) := by
    unfold finiteActionRelationSource
    infer_instance
  have hself : IsFinite (pullback.snd q q) := by
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ M) (fun _ ↦ q) ∈
      Scheme.fpqcPrecoverage Q := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.fppfPrecoverage_le_fpqcPrecoverage _ q.singleton_mem_fppfPrecoverage
  have : IsFinite q := isFinite_of_fpqc_cover q (fun _ : Unit ↦ M) (fun _ ↦ q)
    hcov (fun _ ↦ hself)
  have hsep : Q.IsSeparated := ⟨isSeparated_of_surjective_universallyClosed
    (terminal.from M) (terminal.from Q) q (terminal.comp_from q)⟩
  refine ⟨Q, q, hsep, inferInstance, hqe, hqs, hp,
    sheaf_quotient _ _ q hp, ?_, ?_, ?_, ?_⟩
  · intro T f
    obtain ⟨sT, tT, hs₁, hs₂, ht₁, ht₂, hT⟩ :=
      baseChange_relation (finiteActionRelationSource M G) (finiteActionRelationTarget a) q hp f
    exact ⟨sT, tT, hs₁, hs₂, ht₁, ht₂, sheaf_quotient tT sT _ hT⟩
  · intro F b hb
    exact sheaf_descent _ _ q hp F b (sheaf_action_invariant a F b hb)
  · intro Ω _ _
    refine ⟨fun y ↦ exists_comp_eq_of_isFinite_of_surjective q y, ?_⟩
    intro x y
    constructor
    · intro hxy
      obtain ⟨r, hr₁, hr₂⟩ := hp.exists_lift y x hxy.symm
      obtain ⟨g, z, rfl⟩ := field_point_factors_sigma Ω r
      have hz : z = x := by
        simpa [finiteActionRelationSource] using hr₂
      refine ⟨g, ?_⟩
      simpa [finiteActionRelationTarget, hz] using hr₁
    · rintro ⟨g, rfl⟩
      have he := congrArg (fun k ↦ Sigma.ι (fun _ : G ↦ M) g ≫ k) hp.w
      have hg : (a g).hom ≫ q = q := by
        simpa [finiteActionRelationTarget, finiteActionRelationSource] using he
      simp only [Category.assoc, hg]
  · intro hM
    have : CompactSpace M := hM
    exact q.surjective.compactSpace q.continuous

end AlgebraicGeometry
