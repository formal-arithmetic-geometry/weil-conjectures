/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant

/-!
# Open subgroups and connected finite étale covers

Source: blueprint, sec-smooth-purity, sk-prop-a1-kummer,
cor-galois-open-subgroups; Stacks Project, Tags 0BND, 0BNB, 0BN4, 04JJ, 02K9 and 04MH
(blueprint: cor-galois-open-subgroups).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

open scoped FintypeCatDiscrete in
/-- Geometric points count the degree of a finite étale map over a connected base.
The pullback universal property identifies the fibre with algebra maps; the étale
algebra cardinality theorem computes their number, and local constancy extends the
calculation from the chosen geometric point to every point of the base. -/
private theorem degree_eq_fiber_card
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) :
    P.obj.hom.IsFiniteLocallyFreeOfDegree (Nat.card ((fiber s).obj P)) :=
    open CategoryTheory.Limits CategoryTheory.PreGaloisCategory in by
  classical
  let f : P.obj.left ⟶ Y := P.obj.hom
  let h := pullback.snd f s
  have : IsFinite f := P.property
  have : f.IsFiniteLocallyFree := ⟨⟩
  have : IsAffine (Limits.pullback f s) := isAffine_of_isAffineHom h
  let := h.ΓAlgebra
  have := h.etale_ΓAlgebra
  have hid : Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let e : (fiber s).obj P ≃
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω))) ⟶ Over.mk h) :=
    { toFun z := Over.homMk
        (pullback.lift z.left (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
          (by simpa [hid] using Over.w z)) (by simp [h])
      invFun z := Over.homMk (z.left ≫ pullback.fst f s) (by
        change (z.left ≫ pullback.fst f s) ≫ f = s
        calc
          (z.left ≫ pullback.fst f s) ≫ f = (z.left ≫ pullback.snd f s) ≫ s := by
            rw [Category.assoc, pullback.condition, Category.assoc]
          _ = Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) ≫ s :=
            congrArg (fun t ↦ t ≫ s) (Over.w z)
          _ = s := by rw [hid, Category.id_comp])
      left_inv z := by apply fiber_ext s; simp
      right_inv z := by
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · simp
        · simpa [h] using (Over.w z).symm }
  have hc : Nat.card ((fiber s).obj P) = h.finrankΓ := by
    rw [Nat.card_congr (e.trans (h.overHomEquivAlgHom Ω)),
      Algebra.Etale.natCard_algHom_eq_finrank]
    rfl
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  have hdeg : f.fiberDegree (s z) = h.finrankΓ := by
    exact (f.fiberDegree_of_isPullback (.of_hasPullback f s) z).symm.trans
      (fiberDegree_eq_finrankΓ h z)
  refine { toIsFiniteLocallyFree := inferInstance, fiberDegree_eq := ?_ }
  intro y
  have hloc := (finiteLocallyFree_fiberDimension_isLocallyConstant f).2.1
  exact (hloc.apply_eq_of_preconnectedSpace y (s z)).trans (hdeg.trans hc.symm)

/-- A nonempty transitive fibre reflects connectedness: every noninitial subobject
surjects onto the fibre, and a monomorphism is injective there. Conservativity and
`connectedSpace_of_isConnected` finish the comparison. -/
private theorem connected_of_pretransitive_fiber
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) [Nonempty ((fiber s).obj P)]
    [MulAction.IsPretransitive (Aut (fiber s)) ((fiber s).obj P)] :
    ConnectedSpace P.obj.left :=
    open CategoryTheory.PreGaloisCategory in by
  have : IsConnected P := by
    refine ⟨(not_initial_iff_fiber_nonempty (fiber s) P).mpr inferInstance, ?_⟩
    intro Z i _ hZ
    obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty (fiber s) Z).mp hZ
    have hs : Function.Surjective ((fiber s).map i) := by
      intro p
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut (fiber s)) ((fiber s).map i z) p
      exact ⟨g • z, ((mulAction_naturality (fiber s) g i z).symm).trans hg⟩
    have : IsIso ((fiber s).map i) := (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨ConcreteCategory.injective_of_mono_of_preservesPullback ((fiber s).map i), hs⟩
    exact isIso_of_reflects_iso i (fiber s)
  exact connectedSpace_of_isConnected P

open scoped FintypeCatDiscrete in
/-- An explicit pointed equivariant bijection lifts by fullness of the fibre action
functor. Equality of stabilizers is exactly the condition making the assignment
`a • p ↦ a • q` well-defined and injective; transitivity makes it surjective. -/
private theorem pointed_iso_iff_stabilizer
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (P Q : Y.FiniteEtale) [ConnectedSpace P.obj.left] [ConnectedSpace Q.obj.left]
    (p : (fiber s).obj P) (q : (fiber s).obj Q) :
    (∃ e : P ≅ Q, (fiber s).map e.hom p = q) ↔
      MulAction.stabilizer (Aut (fiber s)) p = MulAction.stabilizer (Aut (fiber s)) q :=
    open CategoryTheory.Limits CategoryTheory.PreGaloisCategory in by
  classical
  let F := fiber s
  let G := Aut F
  have : IsConnected P := isConnected_of_connectedSpace P
  have : IsConnected Q := isConnected_of_connectedSpace Q
  constructor
  · rintro ⟨e, he⟩
    ext g
    change g • p = p ↔ g • q = q
    have hn (x : F.obj P) : F.map e.hom (g • x) = g • F.map e.hom x :=
      (mulAction_naturality F g e.hom x).symm
    constructor
    · intro h
      rw [← he, ← hn, h]
    · intro h
      apply (ConcreteCategory.bijective_of_isIso (F.map e.hom)).1
      rw [hn, he, h]
  · intro he
    have hrel (a b : G) : a • p = b • p ↔ a • q = b • q := by
      have hmem := SetLike.ext_iff.mp he (b⁻¹ * a)
      change (b⁻¹ * a) • p = p ↔ (b⁻¹ * a) • q = q at hmem
      simpa only [mul_smul, inv_smul_eq_iff] using hmem
    choose k hk using (fun x : F.obj P ↦ MulAction.exists_smul_eq G p x)
    let f : F.obj P → F.obj Q := fun x ↦ k x • q
    have hf (a : G) : f (a • p) = a • q :=
      (hrel (k (a • p)) a).mp (hk _)
    have hfcomm (a : G) (x : F.obj P) : f (a • x) = a • f x := by
      obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G p x
      rw [← mul_smul, hf, hf, mul_smul]
    have hbij : Function.Bijective f := by
      constructor
      · intro x y h
        exact (hk x).symm.trans (((hrel (k x) (k y)).mpr h).trans (hk y))
      · intro y
        obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G q y
        exact ⟨a • p, hf a⟩
    let φ : (functorToAction F).obj P ⟶ (functorToAction F).obj Q :=
      ⟨FintypeCat.homMk f, fun a ↦ by ext x; exact hfcomm a x⟩
    let i : P ⟶ Q := (functorToAction F).preimage φ
    have hi : F.map i = FintypeCat.homMk f :=
      congrArg Action.Hom.hom ((functorToAction F).map_preimage φ)
    have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).mpr (by
      rw [hi]
      exact hbij)
    have : IsIso i := isIso_of_reflects_iso i F
    refine ⟨asIso i, ?_⟩
    change F.map i p = q
    rw [hi]
    exact (congrArg f (one_smul G p)).symm.trans ((hf 1).trans (one_smul G q))

open scoped FintypeCatDiscrete in
/-- Realize a finite coset action, transported to the universe of the geometric fibre.
The action isomorphism preserves its marked stabilizer and transitivity, and the latter
reflects connectedness of the cover. -/
private theorem realize_open_subgroup
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (H : Subgroup (Aut (fiber s))) (hH : IsOpen (H : Set (Aut (fiber s)))) :
    ∃ (P : Y.FiniteEtale), ConnectedSpace P.obj.left ∧
      ∃ p : (fiber s).obj P, MulAction.stabilizer (Aut (fiber s)) p = H :=
    open CategoryTheory.PreGaloisCategory in by
  classical
  let F := fiber s
  let G := Aut F
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let T := ULift.{u} (Fin (Fintype.card (G ⧸ H)))
  let e : T ≃ G ⧸ H := Equiv.ulift.trans (Fintype.equivFin _).symm
  let : TopologicalSpace T := ⊥
  have : DiscreteTopology T := ⟨rfl⟩
  let : MulAction G T := e.mulAction G
  let X : Action FintypeCat.{u} G := Action.FintypeCat.ofMulAction G (FintypeCat.of T)
  have hcont : X.IsContinuous := by
    rw [Action.isContinuous_def]
    change Continuous (fun p : G × T ↦ e.symm (p.1 • e p.2))
    exact (continuous_of_discreteTopology : Continuous e.symm).comp
      (continuous_fst.smul ((continuous_of_discreteTopology : Continuous e).comp continuous_snd))
  let X' : ContAction FintypeCat.{u} G := ⟨X, hcont⟩
  obtain ⟨P, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (functorToContAction F) X'
  let b : F.obj P ≃ T :=
    FintypeCat.equivEquivIso.symm ((Action.forget _ _).mapIso
      ((ObjectProperty.ι _).mapIso i))
  have hb (g : G) (x : F.obj P) : b (g • x) = e.symm (g • e (b x)) := by
    exact ConcreteCategory.congr_hom (i.hom.hom.comm g) x
  let p : F.obj P := b.symm (e.symm (QuotientGroup.mk 1))
  have hp : e (b p) = QuotientGroup.mk 1 := by simp [p]
  have : Nonempty (F.obj P) := ⟨p⟩
  have : MulAction.IsPretransitive G (F.obj P) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e (b x)) (e (b y))
    refine ⟨g, b.injective (e.injective ?_)⟩
    rw [hb, Equiv.apply_symm_apply, hg]
  refine ⟨P, connected_of_pretransitive_fiber s P, p, ?_⟩
  calc MulAction.stabilizer G p = MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ H) := by
         ext g
         change g • p = p ↔ g • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1
         rw [← b.injective.eq_iff, hb, ← e.injective.eq_iff, Equiv.apply_symm_apply, hp]
       _ = H := MulAction.stabilizer_quotient H

open scoped FintypeCatDiscrete in
/-- Stabilizers are open because evaluation is continuous into a discrete fibre. -/
private theorem fiber_stabilizer_open
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) (p : (fiber s).obj P) :
    IsOpen (MulAction.stabilizer (Aut (fiber s)) p : Set (Aut (fiber s))) := by
  exact stabilizer_isOpen (Aut (fiber s)) p

/-- Connected finite étale covers are classified by conjugacy classes of open subgroups;
marked covers are classified by individual open subgroups. The classification is expressed
by realization of every open subgroup and the exact isomorphism criteria, avoiding choices
of representatives. Degree is the index of the marked-point stabilizer.

Source: blueprint cor-galois-open-subgroups, corrected DAG statement; Stacks Project,
Tags 0BND, 0BNB, 0BN4, 04JJ, 02K9 and 04MH (blueprint: cor-galois-open-subgroups).

Proof:
1. The existing finite-etale Galois-category and fibre-functor instances let Mathlib's
   `functorToAction` and `functorToContAction` act directly on geometric fibres.
   Connected schemes give connected objects and hence transitive fibres.
2. Conversely, a nonempty transitive fibre makes every noninitial monomorphism into
   the cover surjective on fibres. It is also injective, hence an isomorphism by
   conservativity. The existing connected-object comparison gives scheme connectedness.
3. Continuity into discrete fibres gives open stabilizers; orbit-stabilizer identifies
   their index with fibre cardinality. For an open subgroup, compactness makes its
   coset space finite. Transport its continuous transitive action to a finite model
   in the universe of the fibres, and apply Mathlib's essential surjectivity.
4. Equal stabilizers make `a • p ↦ a • q` well-defined, bijective and equivariant.
   Fullness lifts this map, and conservativity makes the lift an isomorphism.
   Conversely naturality and injectivity of an isomorphism preserve stabilizers.
5. Every point of a connected fibre is `g • q`, whose stabilizer consists of the
   elements `h` with `g⁻¹ * h * g` fixing `q`. The pointed criterion therefore gives
   exactly the stated unpointed conjugacy criterion.
6. Identify the fibre with the algebra maps from the global sections of its geometric
   pullback to Ω. The existing étale-algebra cardinality theorem computes this number
   as its dimension. Base-change invariance computes the degree at the geometric
   point, and local constancy on the connected base computes it everywhere. -/
theorem connected_cover_open_subgroups
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    (∀ (P : Y.FiniteEtale), ConnectedSpace P.obj.left →
      ∀ p : (fiber s).obj P,
        IsOpen (MulAction.stabilizer (Aut (fiber s)) p : Set (Aut (fiber s))) ∧
        P.obj.hom.IsFiniteLocallyFreeOfDegree
          (MulAction.stabilizer (Aut (fiber s)) p).index) ∧
    (∀ H : Subgroup (Aut (fiber s)), IsOpen (H : Set (Aut (fiber s))) →
      ∃ (P : Y.FiniteEtale), ConnectedSpace P.obj.left ∧
        ∃ p : (fiber s).obj P, MulAction.stabilizer (Aut (fiber s)) p = H) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        (∃ e : P ≅ Q, (fiber s).map e.hom p = q) ↔
          MulAction.stabilizer (Aut (fiber s)) p = MulAction.stabilizer (Aut (fiber s)) q) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        Nonempty (P ≅ Q) ↔ ∃ g : Aut (fiber s),
          ∀ h : Aut (fiber s),
            h ∈ MulAction.stabilizer (Aut (fiber s)) p ↔
              g⁻¹ * h * g ∈ MulAction.stabilizer (Aut (fiber s)) q) :=
    open CategoryTheory.Limits CategoryTheory.PreGaloisCategory in by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP p
    have : ConnectedSpace P.obj.left := hP
    have : IsConnected P := isConnected_of_connectedSpace P
    refine ⟨fiber_stabilizer_open s P p, ?_⟩
    rw [MulAction.index_stabilizer_of_transitive]
    exact degree_eq_fiber_card s P
  · exact realize_open_subgroup s
  · intro P Q hP hQ p q
    have : ConnectedSpace P.obj.left := hP
    have : ConnectedSpace Q.obj.left := hQ
    exact pointed_iso_iff_stabilizer s P Q p q
  · intro P Q hP hQ p q
    have : ConnectedSpace P.obj.left := hP
    have : ConnectedSpace Q.obj.left := hQ
    have : IsConnected Q := isConnected_of_connectedSpace Q
    let G := Aut (fiber s)
    have hconj (g h : G) :
        h ∈ MulAction.stabilizer G (g • q) ↔
          g⁻¹ * h * g ∈ MulAction.stabilizer G q := by
      change h • (g • q) = g • q ↔ (g⁻¹ * h * g) • q = q
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
    constructor
    · rintro ⟨e⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G q ((fiber s).map e.hom p)
      have he := (pointed_iso_iff_stabilizer s P Q p (g • q)).mp ⟨e, hg.symm⟩
      exact ⟨g, fun h ↦ (SetLike.ext_iff.mp he h).trans (hconj g h)⟩
    · rintro ⟨g, hg⟩
      have he : MulAction.stabilizer G p = MulAction.stabilizer G (g • q) := by
        ext h
        exact (hg h).trans (hconj g h).symm
      obtain ⟨e, _⟩ := (pointed_iso_iff_stabilizer s P Q p (g • q)).mpr he
      exact ⟨e⟩

end AlgebraicGeometry.Scheme.FiniteEtale
