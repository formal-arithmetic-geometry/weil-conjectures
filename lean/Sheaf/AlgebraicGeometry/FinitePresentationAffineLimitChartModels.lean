module

public import Sheaf.AlgebraicGeometry.FiniteAffineRefinementCollection
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Algebra.Homology.FinitePresentationPreorderColimitModel
import Sheaf.AlgebraicGeometry.FiniteAffineRefinementExistence
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineSectionsRealization
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation

/-!
# Independent finite-presentation models on affine limit charts

Source: Stacks Project, Limits, Tag 01ZR, first proof (affine reduction and Zariski gluing)
(blueprint: lem-trf-fp-affine-limit-chart-models).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- The restricted projection, with source the chosen limit chart rather than a renamed copy.
Source: Stacks, Tags 01ZR and 01YX (blueprint: lem-trf-fp-affine-limit-chart-models). -/
noncomputable def fpLimitChartProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (h : f ⁻¹ᵁ V = U) : U.toScheme ⟶ V.toScheme :=
  f.resLE V U h.ge

/-- An independent sheaf model, together with its canonical affine sections isomorphism.
The displayed pure-tensor formula specifies the comparison: first the actual section
`1 ⊗ s` of the tensor pullback, then multiplication by `b`, then the sections of `e`.
Thus the map is fixed by `e`, rather than an unrelated scalar-extension isomorphism.
Source: Stacks, Tags 01ZR and 01I9
(blueprint: lem-trf-fp-affine-limit-chart-models). -/
def HasFpLimitChartModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (h : f ⁻¹ᵁ V = U) (F : X.Modules) : Prop :=
  ∃ N : V.toScheme.Modules, N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
    ∃ e : (Scheme.Modules.tensorPullback (fpLimitChartProjection f U V h)).obj N ≅
        F.restrict U.ι,
      ∃ θ : (ModuleCat.extendScalars (fpLimitChartProjection f U V h).appTop.hom).obj
          (ModuleCat.of Γ(V.toScheme, ⊤) Γ(N, ⊤)) ≅
          ModuleCat.of Γ(U.toScheme, ⊤) Γ(F.restrict U.ι, ⊤),
        ∀ (b : Γ(U.toScheme, ⊤)) (s : Γ(N, ⊤)),
          θ.hom (b ⊗ₜ[Γ(V.toScheme, ⊤), (fpLimitChartProjection f U V h).appTop.hom] s) =
            (e.hom.app ⊤) (b • @id
              Γ((Scheme.Modules.tensorPullback (fpLimitChartProjection f U V h)).obj N, ⊤)
              (Scheme.Modules.tensorPullbackSection (fpLimitChartProjection f U V h) N ⊤ s))

private abbrev RefinementExpr (n : ℕ) :=
  Option (Finset (Fin n) ⊕ (Fin n × Fin n × Option (Fin n)))

private noncomputable def evalRefinementExpr {n : ℕ} {X : Scheme.{u}}
    (C : Fin n → X.Opens) : RefinementExpr n → X.Opens
  | none => ⊤
  | some (.inl s) => ⨆ d : s, C d
  | some (.inr (a, b, none)) => C a ⊓ C b
  | some (.inr (a, b, some d)) => C a ⊓ C b ⊓ C d

private theorem preimage_evalRefinementExpr {n : ℕ} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (C : Fin n → Y.Opens) (e : RefinementExpr n) :
    f ⁻¹ᵁ evalRefinementExpr C e = evalRefinementExpr (fun d ↦ f ⁻¹ᵁ C d) e := by
  rcases e with _ | s | ⟨a, b, _ | d⟩ <;>
    simp only [evalRefinementExpr, Scheme.Hom.preimage_top, Scheme.Hom.preimage_iSup,
      Scheme.Hom.preimage_inf]

private theorem compact_evalRefinementExpr {n : ℕ} {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (C : Fin n → X.Opens)
    (hC : ∀ d, IsAffineOpen (C d)) (e : RefinementExpr n) :
    IsCompact (evalRefinementExpr C e : Set X) := by
  have hinter {U V : X.Opens} (hU : IsCompact (U : Set X))
      (hV : IsCompact (V : Set X)) : IsCompact (U ⊓ V : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU V.isOpen hV
  rcases e with _ | s | ⟨a, b, _ | d⟩
  · exact isCompact_univ
  · simpa only [evalRefinementExpr, TopologicalSpace.Opens.coe_iSup] using
      isCompact_iUnion (fun d : s ↦ (hC d).isCompact)
  · exact hinter (hC a).isCompact (hC b).isCompact
  · exact hinter (hinter (hC a).isCompact (hC b).isCompact) (hC d).isCompact

private theorem valid_of_refinement_equations
    {X Y : Scheme.{u}} (K : FiniteAffineRefinementShape)
    (C : Fin K.size → X.Opens) (B : Fin K.size → Y.Opens) (hC : K.Valid C)
    (hB : ∀ d, IsAffineOpen (B d))
    (h : ∀ e e' : RefinementExpr K.size,
      evalRefinementExpr C e = evalRefinementExpr C e' →
      evalRefinementExpr B e = evalRefinementExpr B e') : K.Valid B := by
  have hunion (s : Finset (Fin K.size)) :
      (⨆ d : s, C d) = ⨆ d ∈ s, C d := by simp only [iSup_subtype]
  have hunionB (s : Finset (Fin K.size)) :
      (⨆ d : s, B d) = ⨆ d ∈ s, B d := by simp only [iSup_subtype]
  have hle {d e : Fin K.size} (hd : C d ≤ C e) : B d ≤ B e := by
    have H := h (some (.inl {d})) (some (.inr (d, e, none)))
      (by simpa [evalRefinementExpr] using (inf_eq_left.mpr hd).symm)
    exact inf_eq_left.mp (by simpa [evalRefinementExpr] using H.symm)
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have H := h (some (.inl K.main)) none
      (by simpa only [evalRefinementExpr, hunion] using hC.main_cover)
    simpa only [evalRefinementExpr, hunionB] using H
  · intro a ha b hb
    have H := h (some (.inl (K.pair a b))) (some (.inr (a, b, none)))
      (by simpa only [evalRefinementExpr, hunion] using hC.pair_cover a ha b hb)
    simpa only [evalRefinementExpr, hunionB] using H
  · intro a ha b hb r hr t ht
    have H := h (some (.inl (K.overlap r t))) (some (.inr (r, t, none)))
      (by simpa only [evalRefinementExpr, hunion] using hC.overlap_cover a ha b hb r hr t ht)
    simpa only [evalRefinementExpr, hunionB] using H
  · intro a ha b hb d hd
    have H := h (some (.inl (K.triple a b d))) (some (.inr (a, b, some d)))
      (by simpa only [evalRefinementExpr, hunion] using hC.triple_cover a ha b hb d hd)
    simpa only [evalRefinementExpr, hunionB] using H
  · intro a ha b hb d hd t ht
    obtain ⟨hab, had, hbd, ht₁, ht₂, ht₃⟩ := hC.triple_subordinate a ha b hb d hd t ht
    exact ⟨hab, had, hbd, hle ht₁, hle ht₂, hle ht₃⟩
  · intro z hz
    exact hle (hC.inclusions z hz)

private theorem valid_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (K : FiniteAffineRefinementShape) (C : Fin K.size → Y.Opens) (hC : K.Valid C) :
    K.Valid (fun d ↦ f ⁻¹ᵁ C d) := by
  apply valid_of_refinement_equations K C _ hC (fun d ↦ (hC.affine d).preimage f)
  intro e e' he
  rw [← preimage_evalRefinementExpr, ← preimage_evalRefinementExpr, he]

private theorem exists_refinement_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (K : FiniteAffineRefinementShape) (C : Fin K.size → c.pt.Opens) (hC : K.Valid C) :
    ∃ (i : I) (_ : i₀ ≤ i) (B : Fin K.size → (D.obj (op i)).Opens),
      K.Valid B ∧ ∀ d, c.π.app (op i) ⁻¹ᵁ B d = C d := by
  classical
  choose j V hV hVC using fun d ↦ exists_isAffineOpen_preimage_eq D c hc (C d) (hC.affine d)
  obtain ⟨k, fk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let a (d : Fin K.size) : k ⟶ j d := (fk (by simp)).some
  let B (d : Fin K.size) := D.map (a d) ⁻¹ᵁ V d
  have hB (d) : IsAffineOpen (B d) := (hV d).preimage _
  have hBC (d) : c.π.app k ⁻¹ᵁ B d = C d := by
    rw [← hVC d, ← Scheme.Hom.comp_preimage, c.w]
  have heq (e e' : RefinementExpr K.size) :
      ∀ᶠ i in Filter.atTop, evalRefinementExpr C e = evalRefinementExpr C e' →
        ∀ hki : k.unop ≤ i,
          evalRefinementExpr (fun d ↦ D.map (homOfLE hki).op ⁻¹ᵁ B d) e =
          evalRefinementExpr (fun d ↦ D.map (homOfLE hki).op ⁻¹ᵁ B d) e' := by
    by_cases H : evalRefinementExpr C e = evalRefinementExpr C e'
    · have H' : c.π.app k ⁻¹ᵁ evalRefinementExpr B e =
          c.π.app k ⁻¹ᵁ evalRefinementExpr B e' := by
        simpa only [preimage_evalRefinementExpr, hBC] using H
      obtain ⟨j, f, hf⟩ := exists_map_preimage_eq_map_preimage D c hc
        (compact_evalRefinementExpr B hB e) (compact_evalRefinementExpr B hB e') H'
      apply Filter.eventually_atTop.mpr
      refine ⟨j.unop, fun i hji _ hki ↦ ?_⟩
      have hcomp : (homOfLE hji).op ≫ f = (homOfLE hki).op := Subsingleton.elim _ _
      have H'' := congrArg (fun U ↦ D.map (homOfLE hji).op ⁻¹ᵁ U) hf
      simpa only [← Scheme.Hom.comp_preimage, ← D.map_comp, hcomp,
        preimage_evalRefinementExpr] using H''
    · exact Filter.Eventually.of_forall (fun _ h ↦ (H h).elim)
  have hall := Filter.eventually_all.mpr (fun e ↦ Filter.eventually_all.mpr (heq e))
  obtain ⟨i, ⟨hi, hki⟩, h₀i⟩ :=
    ((hall.and (Filter.eventually_ge_atTop k.unop)).and
      (Filter.eventually_ge_atTop i₀)).exists
  let B' (d : Fin K.size) := D.map (homOfLE hki).op ⁻¹ᵁ B d
  refine ⟨i, h₀i, B', ?_, ?_⟩
  · exact valid_of_refinement_equations K C B' hC
      (fun d ↦ (hB d).preimage _) (fun e e' h ↦ hi e e' h hki)
  · intro d
    change c.π.app (op i) ⁻¹ᵁ D.map (homOfLE hki).op ⁻¹ᵁ B d = C d
    rw [← Scheme.Hom.comp_preimage, c.w]
    exact hBC d

private theorem affine_limit_module_model
    {J : Type u} [SmallCategory J] [IsCofiltered J] [Quiver.IsThin J]
    (D : J ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (P : c.pt.Modules)
    (hP : P.IsFinitePresentation) (hPq : P.IsQuasicoherent) :
    ∃ (j : J) (N : (D.obj j).Modules),
      N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.tensorPullback (c.π.app j)).obj N ≅ P) := by
  classical
  let T := ThinSkeleton Jᵒᵖ
  let E : T ⥤ Jᵒᵖ := ThinSkeleton.fromThinSkeleton Jᵒᵖ
  have : IsFiltered T := IsFiltered.of_equivalence (ThinSkeleton.equivalence Jᵒᵖ).symm
  have : Nonempty T := IsFiltered.nonempty
  have : IsDirected T (· ≤ ·) := IsFiltered.isDirectedOrder T
  let G := E ⋙ D.op ⋙ Scheme.Γ
  have (j : Jᵒᵖ) : IsAffine (D.op.obj j).unop := inferInstanceAs (IsAffine (D.obj j.unop))
  let t : Cocone G := (Scheme.Γ.mapCocone c.op).whisker E
  have ht : IsColimit t :=
    (Functor.Final.isColimitWhiskerEquiv E _).symm (isColimitOfPreserves Scheme.Γ hc.op)
  let q : colimit G ≅ Γ(c.pt, ⊤) := (colimit.isColimit G).coconePointUniqueUpToIso ht
  let A := Γ(c.pt, ⊤)
  let M := ModuleCat.of A Γ(P, ⊤)
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : P.IsFinitePresentation := hP
  have hM : Module.FinitePresentation A M :=
    Scheme.Modules.finitePresentation_sections_of_isFinitePresentation P
      (isAffineOpen_top c.pt)
  let X := (ModuleCat.extendScalars q.inv.hom).obj M
  let : Algebra A (colimit G : CommRingCat.{u}) := q.inv.hom.toAlgebra
  have : Module.FinitePresentation A M := hM
  have hX : Module.FinitePresentation (colimit G : CommRingCat.{u}) X := by
    change Module.FinitePresentation (colimit G : CommRingCat.{u})
      ((colimit G : CommRingCat.{u}) ⊗[A] M)
    infer_instance
  obtain ⟨a, Q, hQ, ⟨eQ⟩⟩ :=
    ModuleCat.exists_finitePresentation_model_of_preorder_colimit G X hX
  let j := (E.obj a).unop
  have hmap : q.hom.hom.comp (colimit.ι G a).hom = (c.π.app j).appTop.hom :=
    congrArg CommRingCat.Hom.hom
      ((colimit.isColimit G).comp_coconePointUniqueUpToIso_hom ht a)
  have hinv : q.hom.hom.comp q.inv.hom = RingHom.id A :=
    congrArg CommRingCat.Hom.hom q.inv_hom_id
  let cancel : (ModuleCat.extendScalars q.hom.hom).obj X ≅ M :=
    ((ModuleCat.extendScalarsComp q.inv.hom q.hom.hom).app M).symm ≪≫
      eqToIso (congrArg (fun r ↦ (ModuleCat.extendScalars r).obj M) hinv) ≪≫
      (ModuleCat.extendScalarsId A).app M
  let e : (ModuleCat.extendScalars (c.π.app j).appTop.hom).obj Q ≅ M :=
    (eqToIso (congrArg (fun r ↦ (ModuleCat.extendScalars r).obj Q) hmap)).symm ≪≫
      (ModuleCat.extendScalarsComp (colimit.ι G a).hom q.hom.hom).app Q ≪≫
      (ModuleCat.extendScalars q.hom.hom).mapIso eQ ≪≫ cancel
  obtain ⟨N, hN, hNq, ⟨eN⟩⟩ :=
    exists_finitePresentation_affine_sections_realization
      (X := D.obj j) (Y := c.pt) (c.π.app j) P hPq Q hQ ⟨e⟩
  let comparison := (Scheme.Modules.tensorPullbackSectionAdjunction (c.π.app j)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction (c.π.app j))
  exact ⟨j, N, hN, hNq, ⟨comparison.app N ≪≫ eN⟩⟩

private theorem affine_tensor_sections_comparison
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X ⟶ Y)
    (N : Y.Modules) (hN : N.IsQuasicoherent) :
    ∃ θ : (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Y, ⊤) Γ(N, ⊤)) ≅
        ModuleCat.of Γ(X, ⊤) Γ((Scheme.Modules.tensorPullback g).obj N, ⊤),
      ∀ (b : Γ(X, ⊤)) (s : Γ(N, ⊤)),
        θ.hom (b ⊗ₜ[Γ(Y, ⊤), g.appTop.hom] s) =
          b • @id Γ((Scheme.Modules.tensorPullback g).obj N, ⊤)
            (Scheme.Modules.tensorPullbackSection g N ⊤ s) := by
  classical
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := g.appTop.hom.toAlgebra
  let : Module A Γ((Scheme.Modules.tensorPullback g).obj N, ⊤) :=
    Module.compHom _ g.appTop.hom
  have H := Scheme.Modules.exists_tensorPullback_affine_sections g
    ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩ le_top
  have hh : g.appLE ⊤ ⊤ le_top = g.appTop := g.appLE_eq_app
  dsimp only at H
  rw [hh] at H
  obtain ⟨c, hc, hsmul, htmul, _⟩ := H
  let l : (ModuleCat.extendScalars g.appTop.hom).obj
      (ModuleCat.of A Γ(N, ⊤)) →ₗ[B]
      Γ((Scheme.Modules.tensorPullback g).obj N, ⊤) :=
    { toFun := fun t ↦ c N hN ((TensorProduct.comm A B Γ(N, ⊤)) t)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro b t
        have hs := hsmul N hN b ((TensorProduct.comm A B Γ(N, ⊤)) t)
        change c N hN ((TensorProduct.comm A Γ(N, ⊤) B).symm
          (b • (TensorProduct.comm A Γ(N, ⊤) B)
            ((TensorProduct.comm A B Γ(N, ⊤)) t))) =
          b • c N hN ((TensorProduct.comm A B Γ(N, ⊤)) t) at hs
        simpa only [TensorProduct.comm_symm, TensorProduct.comm_comm, RingHom.id_apply]
          using hs }
  have hl : Function.Bijective l :=
    (hc N hN).comp (TensorProduct.comm A B Γ(N, ⊤)).bijective
  refine ⟨(LinearEquiv.ofBijective l hl).toModuleIso, ?_⟩
  intro b s
  change c N hN (s ⊗ₜ[A] b) = _
  rw [htmul N hN s b]
  have hu := (Classical.choose_spec
    (Scheme.Modules.exists_tensorPullbackAdjunction g)) N (op ⊤) s
  change ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
    N).val.app (op ⊤) s = Scheme.Modules.tensorPullbackSection g N ⊤ s at hu
  have hr (t : Γ((Scheme.Modules.tensorPullback g).obj N, ⊤)) :
      ((Scheme.Modules.tensorPullback g).obj N).presheaf.map
        (homOfLE (show (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)).op t = t := by
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.tensorPullback g).obj N).presheaf.map_id (op ⊤)) t
  exact congrArg (fun x : Γ((Scheme.Modules.tensorPullback g).obj N, ⊤) ↦ b • x)
    ((hr _).trans hu)

private theorem has_model_of_sheaf_model
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : f ⁻¹ᵁ V = U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (F : X.Modules)
    (N : V.toScheme.Modules) (hN : N.IsFinitePresentation) (hNq : N.IsQuasicoherent)
    (e : (Scheme.Modules.tensorPullback (fpLimitChartProjection f U V h)).obj N ≅
      F.restrict U.ι) : HasFpLimitChartModel f U V h F := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨θ, hθ⟩ := affine_tensor_sections_comparison (fpLimitChartProjection f U V h) N hNq
  refine ⟨N, hN, hNq, e,
    θ ≪≫ (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).mapIso e, ?_⟩
  intro b t
  change (e.hom.app ⊤) (θ.hom (b ⊗ₜ[Γ(V.toScheme, ⊤),
    (fpLimitChartProjection f U V h).appTop.hom] t)) = _
  exact congrArg (e.hom.app ⊤) (hθ b t)

/-- A finite affine refinement collection exists on the limit; every chosen collection
and finitely presented module has independent local models at a common stage above `i₀`.

Source: Stacks, Limits, Tag 01ZR, first proof; Tags 01YX, 01YW, 01Z4; Algebra, Tag 05N7
(blueprint: lem-trf-fp-affine-limit-chart-models).

Proof:
1. The projection to i₀ is affine by lem-weil-pbc-limit-cone-affine-projections-opens.
A finite affine
cover of S_i₀ pulls back to a finite affine cover of S, proving quasi-compactness.
Intersections are inverse images of quasi-compact intersections at i₀; affine morphisms
are quasi-compact, so the affine-cover criterion proves quasi-separatedness of S.
2. Use lem-weil-pbc-qcqs-finite-affine-open-cover and pqf-lem-qs-intersection-qc to choose
finite pair and overlap covers. Cover each intersection of three chosen pair charts by
finitely many affines to obtain subordinate triple covers; empty opens use empty covers.
These prove existence. Retain the arbitrary collection in the universal clause.
3. Descend every labelled affine by lem-trf-affine-open-limit-descent. Directedness gives
one stage above their finitely many stages and i₀. Pullback along affine transitions
preserves affineness and the inverse-image equalities. With no labels keep i₀.
4. Encode inclusions as C = C ∩ C' and covers as equalities of finite open expressions.
Every expression is quasi-compact by pqf-lem-qs-intersection-qc, stage quasi-compactness,
and finite-union compactness. Part (2) of pqf-lem-limit-qc-open-descends stabilizes each
equality. Choose a common upper bound. Inverse image preserves all these equations.
5. The restriction and affine-ring clauses of lem-weil-pbc-limit-cone-affine-projections-opens give
the canonical restricted limiting cones and ring colimit cocones at this and every later
stage. Their vertices are the stated preimages, equal to the chosen C_d.
6. By lem-weil-pbc-quasi-coherent-finite-type-affine, F is quasi-coherent with finitely
presented affine sections. On each chart apply the object clause of
lem-pc-fp-preorder-colimit-model after reindexing the opposite tail by its thin skeleton.
7. Apply lem-pc-fp-affine-sections-realization to realize each algebraic sections model
as a finitely presented quasi-coherent sheaf and its supplied pullback isomorphism.
8. Take a common upper bound for all these stages. Pull the models to it using
lem-pc-tensor-pullback-finite-presentation. The canonical composition identifications of
def-pc-module-pullback give e_d. The canonical comparison of
lem-weil-pbc-module-pullback-affine-sections, followed by sections of e_d and tensor
symmetry, gives θ with the displayed pure-tensor formula. The cover equations persist,
and Step 5 applies at the final stage. There are no maps between distinct local models.
-/
theorem exists_finitePresentation_affine_limit_chart_models
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (F : c.pt.Modules) (hF : F.IsFinitePresentation) :
    (∃ (K : FiniteAffineRefinementShape) (C : Fin K.size → c.pt.Opens), K.Valid C) ∧
    ∀ (K : FiniteAffineRefinementShape) (C : Fin K.size → c.pt.Opens), K.Valid C →
      ∃ (i : I) (_ : i₀ ≤ i) (Ci : Fin K.size → (D.obj (op i)).Opens),
        K.Valid Ci ∧
        ∀ d : Fin K.size,
          ∃ h : c.π.app (op i) ⁻¹ᵁ Ci d = C d,
            (∀ j : Over (op i), IsAffine ((opensDiagram D (op i) (Ci d)).obj j)) ∧
            Nonempty (IsLimit (opensCone D c (op i) (Ci d))) ∧
            Nonempty (IsColimit (Scheme.Γ.mapCocone (opensCone D c (op i) (Ci d)).op)) ∧
            HasFpLimitChartModel (c.π.app (op i)) (C d) (Ci d) h F := by
  classical
  have hπ (i : Iᵒᵖ) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  have : F.IsFinitePresentation := hF
  have : F.IsQuasicoherent :=
    (Scheme.Modules.quasicoherent_finite_type_affine.{u, u} c.pt).1 F hF
  refine ⟨exists_finiteAffineRefinementCollection c.pt, ?_⟩
  intro K C hC
  obtain ⟨i, h₀i, B, hB, hBC⟩ := exists_refinement_stage D c hc i₀ K C hC
  have hCeq : C = fun d ↦ c.π.app (op i) ⁻¹ᵁ B d := (funext hBC).symm
  subst C
  have hex (d : Fin K.size) :
      ∃ (j : Over (op i)) (N : ((opensDiagram D (op i) (B d)).obj j).Modules),
        N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
        Nonempty ((Scheme.Modules.tensorPullback
          ((opensCone D c (op i) (B d)).π.app j)).obj N ≅
          F.restrict (c.π.app (op i) ⁻¹ᵁ B d).ι) := by
    have (j : Over (op i)) : IsAffine ((opensDiagram D (op i) (B d)).obj j) :=
      (hB.affine d).preimage (D.map j.hom)
    have : Quiver.IsThin (Over (op i)) := fun _ _ ↦
      ⟨fun f g ↦ (Over.forget (op i)).map_injective (Subsingleton.elim _ _)⟩
    let P := F.restrict (c.π.app (op i) ⁻¹ᵁ B d).ι
    have hP : P.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback _).app F).symm
    have hPq : P.IsQuasicoherent := inferInstance
    exact affine_limit_module_model (opensDiagram D (op i) (B d))
      (opensCone D c (op i) (B d)) (isLimitOpensCone D c hc (op i) (B d)) P hP hPq
  choose j N hN hNq e using hex
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists
    (insert (op i) (Finset.univ.image (fun d ↦ (j d).left)))
  let a : k ⟶ op i := (hk (by simp)).some
  let b (d : Fin K.size) : k ⟶ (j d).left := (hk (by simp)).some
  let B' (d : Fin K.size) := D.map a ⁻¹ᵁ B d
  have hB' : K.Valid B' := valid_preimage (D.map a) K B hB
  have hB'C (d) : c.π.app k ⁻¹ᵁ B' d = c.π.app (op i) ⁻¹ᵁ B d := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  refine ⟨k.unop, h₀i.trans (leOfHom a.unop), B', hB', ?_⟩
  intro d
  refine ⟨hB'C d, ?_, ⟨isLimitOpensCone D c hc k (B' d)⟩, ?_, ?_⟩
  · intro t
    exact (hB'.affine d).preimage (D.map t.hom)
  · have (t : Over k) : IsAffine ((opensDiagram D k (B' d)).obj t) :=
      (hB'.affine d).preimage (D.map t.hom)
    have (t : (Over k)ᵒᵖ) : IsAffine ((opensDiagram D k (B' d)).op.obj t).unop :=
      (hB'.affine d).preimage (D.map t.unop.hom)
    exact ⟨isColimitOfPreserves Scheme.Γ (isLimitOpensCone D c hc k (B' d)).op⟩
  · let g := fpLimitChartProjection (c.π.app k)
      (c.π.app (op i) ⁻¹ᵁ B d) (B' d) (hB'C d)
    have hres : D.map (b d) ⁻¹ᵁ (D.map (j d).hom ⁻¹ᵁ B d) = B' d := by
      rw [← Scheme.Hom.comp_preimage, ← D.map_comp]
      exact congrArg (fun f ↦ D.map f ⁻¹ᵁ B d) (Subsingleton.elim _ a)
    let r : (B' d).toScheme ⟶ ((opensDiagram D (op i) (B d)).obj (j d)) :=
      (D.map (b d)).resLE _ _ hres.ge
    have hgr : g ≫ r = (opensCone D c (op i) (B d)).π.app (j d) := by
      apply (cancel_mono (D.map (j d).hom ⁻¹ᵁ B d).ι).mp
      rw [Category.assoc]
      dsimp only [r]
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc]
      dsimp only [g, fpLimitChartProjection]
      rw [Scheme.Hom.resLE_comp_ι]
      change _ = (c.π.app (j d).left).resLE _ _ _ ≫ _
      rw [Scheme.Hom.resLE_comp_ι, Category.assoc, c.w]
    let N' := (Scheme.Modules.tensorPullback r).obj (N d)
    have : (N d).IsFinitePresentation := hN d
    have hN' : N'.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_tensorPullback r (N d)
    have hN'q : N'.IsQuasicoherent :=
      (Scheme.Modules.quasicoherent_finite_type_affine.{u, u} (B' d).toScheme).1 N' hN'
    let e' : (Scheme.Modules.tensorPullback g).obj N' ≅
        F.restrict (c.π.app (op i) ⁻¹ᵁ B d).ι :=
      ((Scheme.Modules.tensorPullbackSectionComp g r).app (N d)).symm ≪≫
        eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj (N d)) hgr) ≪≫
        (e d).some
    exact has_model_of_sheaf_model (c.π.app k) _ _ (hB'C d)
      (hB.affine d |>.preimage (c.π.app (op i))) (hB'.affine d) F N' hN' hN'q e'

end AlgebraicGeometry
