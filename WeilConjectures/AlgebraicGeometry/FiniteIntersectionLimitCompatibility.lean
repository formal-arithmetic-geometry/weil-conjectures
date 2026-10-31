/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # Finite intersection limits of affine ind-étale coverings

Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first-limit paragraph
and displayed intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility).

The stage diagrams are over the fixed scheme `U`, not étale over `X`.
Empty products in `Over U` handle deletion from a one-factor intersection.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The simultaneous stage family, with the product index ordered coordinatewise.
Source: Stacks Project, Tag 099U, first-limit product of directed sets
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
def firstLimitCoordinate {U : Scheme.{u}} {m : ℕ} {J : Fin m → Type u}
    [∀ a, Preorder (J a)] (D : ∀ a, (J a)ᵒᵖ ⥤ Over U) (a : Fin m) :
    (∀ b, J b)ᵒᵖ ⥤ Over U :=
  (CategoryTheory.Pi.eval J a).op ⋙ D a

/-- The canonical diagram of ordered intersections, including the empty intersection.
Repeated labels select separate product factors at the same stage index.
Source: Stacks Project, Tag 099U, displayed first-limit intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
noncomputable def firstLimitIntersectionDiagram {U : Scheme.{u}} {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U) (k : ℕ) (α : Fin k → Fin m) :
    (∀ a, J a)ᵒᵖ ⥤ Over U :=
  Functor.pi' (fun r ↦ firstLimitCoordinate D (α r)) ⋙ Limits.Pi.functor (Fin k)

/-- Delete the specified factor from a finite ordered fibre product over `U`.
For a one-factor product the target is the empty product, canonically `U`.
Source: Stacks Project, Tag 099U, functoriality of the intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
noncomputable def firstLimitDelete {U : Scheme.{u}} {m k : ℕ}
    (V : Fin m → Over U) (α : Fin (k + 1) → Fin m) (r : Fin (k + 1)) :
    (∏ᶜ fun s ↦ V (α s)) ⟶ ∏ᶜ fun s ↦ V (α (r.succAbove s)) :=
  Limits.Pi.map' r.succAbove (fun _ ↦ 𝟙 _)

private theorem presentation {S T : Scheme.{u}} (f : T ⟶ S)
    (hf : proAffineEtale f) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (D : Jᵒᵖ ⥤ Over S)
      (q : (Functor.const Jᵒᵖ).obj (Over.mk f) ⟶ D),
      (∀ i, IsAffine (D.obj i).left ∧ Etale (D.obj i).hom) ∧
      Nonempty (IsLimit ((Over.forget S).mapCone (Cone.mk (Over.mk f) q))) := by
  obtain ⟨I, _, _, E, t, s, hs, ht⟩ := hf
  obtain ⟨J, hJ, hd, hn, F, hF⟩ := exists_directed_reindexing Iᵒᵖ
  let := hJ
  let := hd
  let := hn
  let G : Jᵒᵖ ⥤ I := F.op ⋙ (opOpEquivalence I).functor
  let E' : Iᵒᵖᵒᵖ ⥤ Scheme.{u} := (opOpEquivalence I).functor ⋙ E
  have hE' : IsLimit ((Cone.mk T s).whisker (opOpEquivalence I).functor) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hs
  have hG := ((hF Scheme inferInstance).2 E' _ hE').some
  let D : Jᵒᵖ ⥤ Over S := G ⋙ Over.lift E t
  let q : (Functor.const Jᵒᵖ).obj (Over.mk f) ⟶ D :=
    { app i := Over.homMk (s.app (G.obj i)) (ht _).2
      naturality i j h := by
        ext
        exact s.naturality (G.map h) }
  refine ⟨J, hJ, hn, hd, D, q, ?_, ?_⟩
  · intro i
    exact ⟨(ht _).1.2.1, (ht _).1.1⟩
  · exact ⟨hG⟩

private theorem product_property {X S : Scheme.{u}} (g : S ⟶ X)
    (hg : proAffineEtale g) (k : ℕ) (W : Fin k → Over S)
    (hW : ∀ r, proAffineEtale ((W r).hom ≫ g)) :
    proAffineEtale ((∏ᶜ W).hom ≫ g) := by
  induction k with
  | zero =>
    let c : Fan W := Fan.mk (Over.mk (𝟙 S)) (fun r ↦ Fin.elim0 r)
    have hc : IsLimit c :=
      { lift s := Over.homMk s.pt.hom
        fac s j := Fin.elim0 j.as
        uniq s m hm := by ext; exact m.w }
    let e := (limit.isLimit (Discrete.functor W)).conePointUniqueUpToIso hc
    have he : (∏ᶜ W).hom ≫ g = e.hom.left ≫ g := by
      simpa [c] using congrArg (fun z ↦ z ≫ g) e.hom.w.symm
    rw [he]
    rw [proAffineEtale.cancel_left_of_respectsIso]
    exact hg
  | succ k ih =>
    let W' : Fin k → Over S := fun r ↦ W r.succ
    have htail := ih W' (fun r ↦ hW r.succ)
    have hS : IsAffine S := hg.isAffine
    have hA : IsAffine (W 0).left := (hW 0).isAffine
    have hB : IsAffine (∏ᶜ W').left := htail.isAffine
    have hrel : proAffineEtale (W 0).hom :=
      proAffineEtale.of_postcomp _ g hg (hW 0)
    let c := pullback.cone (W 0).hom (∏ᶜ W').hom
    let b := pullbackConeEquivBinaryFan.functor.obj c
    have hb := IsLimit.pullbackConeEquivBinaryFanFunctor
      (pullback.isLimit (W 0).hom (∏ᶜ W').hom)
    let e := (limit.isLimit (Discrete.functor W)).conePointUniqueUpToIso
      (extendFanIsLimit W (productIsProduct W') hb)
    have hp : proAffineEtale (pullback.snd (W 0).hom (∏ᶜ W').hom) :=
      MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
        (IsPullback.of_hasPullback (W 0).hom (∏ᶜ W').hom) hrel
    have hh : proAffineEtale ((extendFan (limit.cone (Discrete.functor W')) b).pt.hom ≫ g) := by
      change proAffineEtale (pullback.fst _ _ ≫ (W 0).hom ≫ g)
      rw [pullback.condition_assoc]
      exact proAffineEtale.comp_mem _ _ hp htail
    have he : (∏ᶜ W).hom ≫ g =
        e.hom.left ≫ (extendFan (f := W) (Fan.mk _ (Limits.Pi.π W')) b).pt.hom ≫ g := by
      exact congrArg (fun z ↦ z ≫ g) e.hom.w.symm
    rw [he]
    rw [proAffineEtale.cancel_left_of_respectsIso]
    exact hh

private noncomputable def productCone {C : Type*} [Category* C]
    {I : Type*} [Category* I] {k : ℕ} [HasProductsOfShape (Fin k) C]
    (E : Fin k → I ⥤ C) (W : Fin k → C)
    (q : ∀ r, (Functor.const I).obj (W r) ⟶ E r) :
    Cone (Functor.pi' E ⋙ Limits.Pi.functor (Fin k)) where
  pt := ∏ᶜ W
  π :=
    { app j := Limits.Pi.map (fun r ↦ (q r).app j)
      naturality i j h := by
        apply Limits.Pi.hom_ext
        intro r
        change (𝟙 _ ≫ Limits.Pi.map (fun r ↦ (q r).app j)) ≫ Limits.Pi.π _ r =
          (Limits.Pi.map (fun r ↦ (q r).app i) ≫
            Limits.Pi.map (fun r ↦ (E r).map h)) ≫ Limits.Pi.π _ r
        simp only [Category.id_comp, Limits.Pi.map_π, Limits.Pi.map_π_assoc, Category.assoc]
        simpa using congrArg (fun z ↦ Limits.Pi.π W r ≫ z) ((q r).naturality h) }

private noncomputable def productConeIsLimit {C : Type*} [Category* C]
    {I : Type*} [Category* I] {k : ℕ} [HasProductsOfShape (Fin k) C]
    (E : Fin k → I ⥤ C) (W : Fin k → C)
    (q : ∀ r, (Functor.const I).obj (W r) ⟶ E r)
    (hq : ∀ r, IsLimit (Cone.mk (W r) (q r))) :
    IsLimit (productCone E W q) := by
  let component (s : Cone (Functor.pi' E ⋙ Limits.Pi.functor (Fin k))) (r : Fin k) :
      Cone (E r) :=
    { pt := s.pt
      π :=
        { app j := s.π.app j ≫ Limits.Pi.π (fun t ↦ (E t).obj j) r
          naturality i j h := by
            change 𝟙 _ ≫ s.π.app j ≫ Limits.Pi.π _ r =
              (s.π.app i ≫ Limits.Pi.π _ r) ≫ (E r).map h
            have hw := congrArg
              (fun z ↦ z ≫ Limits.Pi.π (fun t ↦ (E t).obj j) r) (s.w h).symm
            change s.π.app j ≫ Limits.Pi.π _ r =
              (s.π.app i ≫ Limits.Pi.map (fun r ↦ (E r).map h)) ≫ Limits.Pi.π _ r at hw
            simpa only [Category.id_comp, Category.assoc, Limits.Pi.map_π] using hw } }
  refine
    { lift s := Limits.Pi.lift (fun r ↦ (hq r).lift (component s r))
      fac s j := ?_
      uniq s m hm := ?_ }
  · apply Limits.Pi.hom_ext
    intro r
    simp only [productCone, Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
    exact (hq r).fac (component s r) j
  · apply Limits.Pi.hom_ext
    intro r
    apply (hq r).hom_ext
    intro j
    have hw := congrArg (fun z ↦ z ≫ Limits.Pi.π (fun t ↦ (E t).obj j) r) (hm j)
    change (m ≫ Limits.Pi.map (fun r ↦ (q r).app j)) ≫ Limits.Pi.π _ r = _ at hw
    simpa only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
      (hq r).fac] using hw

private theorem delete_map {C : Type*} [Category* C] {k : ℕ}
    [HasProductsOfShape (Fin k) C] [HasProductsOfShape (Fin (k + 1)) C]
    (W Z : Fin (k + 1) → C) (t : ∀ s, W s ⟶ Z s) (r : Fin (k + 1)) :
    Limits.Pi.map' r.succAbove (fun _ ↦ 𝟙 _) ≫
        Limits.Pi.map (fun s ↦ t (r.succAbove s)) =
      Limits.Pi.map t ≫ Limits.Pi.map' r.succAbove (fun _ ↦ 𝟙 _) := by
  simp only [Limits.Pi.map'_comp_map, Limits.Pi.map_comp_map',
    Category.id_comp, Category.comp_id]

/-- A nonempty finite basis covering of `U` admits independent small directed affine
étale finite-presentation approximations. Every simultaneous stage still covers `U`.
The original and stage intersections are affine ind-étale over `X`, and their canonical
cones are scheme limits, compatible with deletion of every factor and with transitions.
Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first-limit paragraph
and displayed intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility).

Proof:
1. Use the proved relative pro-affine-etale property of each `V_a -> U`.
   Unpack its cofiltered affine etale presentation, replace its opposite index
   by a small directed preorder, and lift the diagram and cone to `Over U`.
2. The finite product of the nonempty directed index sets is nonempty and directed.
   Lift a point of `U` through the given basis covering and project it to the
   selected stage. Every simultaneous stage family is jointly surjective and etale.
3. Compose the stage maps with `U -> X`. Finite products remain in the basis:
   induct on their number, using `U` for the empty product and a pullback for
   a successor. Pro-affine-etale cancellation, base change, and composition
   prove the assertion. Maps between the resulting affine schemes are affine.
4. Coordinate evaluation is final, so its opposite is initial. Reindexing along
   it preserves each factor limit; `Over.forget U` reflects these limits.
5. Construct the intersection cone by the product maps of the factor legs.
   Project an arbitrary cone to each factor, apply the factor limit lifts, and
   combine these by the product lift. Factorwise uniqueness proves uniqueness.
   This also handles repeated labels and zero factors. The forgetful functor
   preserves this limit since the simultaneous opposite index is cofiltered.
6. Product-map composition gives both deletion equations, including deletion
   to the empty product. Hence the limit identifications commute with deletion. -/
theorem exists_finite_intersection_limit_compatibility
    (X : Scheme.{u}) [IsAffine X] (U : X.AffineProEt)
    {m : ℕ} (hm : 0 < m) (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ topology X U) :
    ∃ (J : Fin m → Type u) (_ : ∀ a, Preorder (J a))
      (_ : ∀ a, Nonempty (J a)) (_ : ∀ a, IsDirected (J a) (· ≤ ·))
      (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
      (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a),
      (∀ a i, IsAffine ((D a).obj i).left ∧ Etale ((D a).obj i).hom ∧
        LocallyOfFinitePresentation ((D a).obj i).hom ∧
        QuasiCompact ((D a).obj i).hom ∧
        proAffineEtale (((D a).obj i).hom ≫ U.hom)) ∧
      (∀ a, Nonempty (IsLimit ((Over.forget U.left).mapCone
        (Cone.mk (Over.mk (f a).left) (q a))))) ∧
      (∀ a (i j : (J a)ᵒᵖ) (h : i ⟶ j), IsAffineHom ((D a).map h).left) ∧
      (∀ a i, IsAffineHom ((q a).app i).left) ∧
      (∀ j : ∀ a, J a,
        Sieve.ofArrows (fun a ↦ ((D a).obj (op (j a))).left)
          (fun a ↦ ((D a).obj (op (j a))).hom) ∈ etaleTopology U.left) ∧
      ∃ (π : ∀ (k : ℕ) (α : Fin k → Fin m),
          (Functor.const (∀ a, J a)ᵒᵖ).obj
            (∏ᶜ fun r ↦ Over.mk (f (α r)).left) ⟶
              firstLimitIntersectionDiagram D k α),
        (∀ (k : ℕ) (α : Fin k → Fin m), Nonempty (IsLimit ((Over.forget U.left).mapCone
          (Cone.mk (∏ᶜ fun r ↦ Over.mk (f (α r)).left) (π k α))))) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m), IsAffine (∏ᶜ fun r ↦ Over.mk (f (α r)).left).left ∧
          proAffineEtale ((∏ᶜ fun r ↦ Over.mk (f (α r)).left).hom ≫ U.hom)) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ),
          IsAffine ((firstLimitIntersectionDiagram D k α).obj j).left ∧
          proAffineEtale (((firstLimitIntersectionDiagram D k α).obj j).hom ≫ U.hom)) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (i j : (∀ a, J a)ᵒᵖ) (h : i ⟶ j),
          IsAffineHom ((firstLimitIntersectionDiagram D k α).map h).left) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ), IsAffineHom ((π k α).app j).left) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ) (r : Fin k),
          (π k α).app j ≫ Limits.Pi.π
            (fun s ↦ (D (α s)).obj (op (unop j (α s)))) r =
          Limits.Pi.π (fun s ↦ Over.mk (f (α s)).left) r ≫
            (q (α r)).app (op (unop j (α r)))) ∧
        (∀ k (α : Fin (k + 1) → Fin m) (r : Fin (k + 1)) j,
          firstLimitDelete (fun a ↦ Over.mk (f a).left) α r ≫
            (π k (α ∘ r.succAbove)).app j =
          (π (k + 1) α).app j ≫
            firstLimitDelete (fun a ↦ (D a).obj (op (unop j a))) α r) ∧
        (∀ k (α : Fin (k + 1) → Fin m) (r : Fin (k + 1))
            (i j : (∀ a, J a)ᵒᵖ) (h : i ⟶ j),
          (firstLimitIntersectionDiagram D (k + 1) α).map h ≫
            firstLimitDelete (fun a ↦ (D a).obj (op (unop j a))) α r =
          firstLimitDelete (fun a ↦ (D a).obj (op (unop i a))) α r ≫
            (firstLimitIntersectionDiagram D k (α ∘ r.succAbove)).map h) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hp (a : Fin (m + 1)) := presentation (f a).left (proAffineEtale_hom (f a))
  choose J hJ hn hd D q hD hq using hp
  let (a : Fin (m + 1)) : Preorder (J a) := hJ a
  let (a : Fin (m + 1)) : Nonempty (J a) := hn a
  let (a : Fin (m + 1)) : IsDirected (J a) (· ≤ ·) := hd a
  have hstage (a : Fin (m + 1)) (i : (J a)ᵒᵖ) :
      proAffineEtale (((D a).obj i).hom ≫ U.hom) := by
    have := (hD a i).1
    have := (hD a i).2
    exact proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) U.prop
  have hprod (k : ℕ) (W : Fin k → Over U.left)
      (hW : ∀ r, proAffineEtale ((W r).hom ≫ U.hom)) :
      IsAffine (∏ᶜ W).left ∧ proAffineEtale ((∏ᶜ W).hom ≫ U.hom) := by
    have h := product_property U.hom U.prop k W hW
    exact ⟨h.isAffine, h⟩
  have hV (a : Fin (m + 1)) : proAffineEtale ((f a).left ≫ U.hom) := by
    simpa using (V a).prop
  let q' (a : Fin (m + 1)) : (Functor.const (∀ a, J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶
      firstLimitCoordinate D a := Functor.whiskerLeft (CategoryTheory.Pi.eval J a).op (q a)
  have hq' (a : Fin (m + 1)) : IsLimit (Cone.mk (Over.mk (f a).left) (q' a)) := by
    have h := isLimitOfReflects (Over.forget U.left) (hq a).some
    exact (Functor.Initial.isLimitWhiskerEquiv (CategoryTheory.Pi.eval J a).op _).symm h
  let c (k : ℕ) (α : Fin k → Fin (m + 1)) :=
    productCone (fun r ↦ firstLimitCoordinate D (α r))
      (fun r ↦ Over.mk (f (α r)).left) (fun r ↦ q' (α r))
  let π (k : ℕ) (α : Fin k → Fin (m + 1)) :
      (Functor.const (∀ a, J a)ᵒᵖ).obj (∏ᶜ fun r ↦ Over.mk (f (α r)).left) ⟶
        firstLimitIntersectionDiagram D k α := (c k α).π
  have hπ (k : ℕ) (α : Fin k → Fin (m + 1)) (j : (∀ a, J a)ᵒᵖ) (r : Fin k) :
      (π k α).app j ≫ Limits.Pi.π
        (fun s ↦ (D (α s)).obj (op (unop j (α s)))) r =
        Limits.Pi.π (fun s ↦ Over.mk (f (α s)).left) r ≫
          (q (α r)).app (op (unop j (α r))) := by
    change Limits.Pi.map (fun r ↦ (q (α r)).app (op (unop j (α r)))) ≫
      Limits.Pi.π _ r = _
    exact Limits.Pi.map_π _ r
  refine ⟨J, hJ, hn, hd, D, q, ?_, hq, ?_, ?_, ?_, π, ?_, ?_, ?_, ?_, ?_, hπ, ?_, ?_⟩
  · intro a i
    have := (hD a i).1
    have := (hD a i).2
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hstage a i⟩
  · intro a i j h
    have := (hD a i).1
    have := (hD a j).1
    infer_instance
  · intro a i
    have : IsAffine ((D a).obj i).left := (hD a i).1
    exact @isAffineHom_of_isAffine (V a).left ((D a).obj i).left
      ((q a).app i).left inferInstance (hD a i).1
  · intro j
    apply Precoverage.generate_mem_toGrothendieck
    apply (ofArrows_mem_precoverage_iff _).2
    refine ⟨?_, fun a ↦ (hD a _).2⟩
    intro x
    obtain ⟨ι, _, W, t, ht, hsurj⟩ :=
      exists_finite_jointly_surjective_of_mem_topology hcover
    obtain ⟨i, w, hw⟩ := hsurj x
    obtain ⟨Z, b, g, ⟨a⟩, hfac⟩ := ht i
    refine ⟨a, ((q a).app (op (j a))).left (b.left w), ?_⟩
    have hpoint := congrArg (fun z : W i ⟶ U ↦ z.left w) hfac
    calc
      _ = (f a).left (b.left w) :=
        congrArg (fun z : (V a).left ⟶ U.left ↦ z (b.left w))
          ((q a).app (op (j a))).w
      _ = x := hpoint.trans hw
  · intro k α
    exact ⟨isLimitOfPreserves (Over.forget U.left)
      (productConeIsLimit _ _ _ (fun r ↦ hq' (α r)))⟩
  · intro k α
    exact hprod k _ (fun r ↦ hV (α r))
  · intro k α j
    exact hprod k _ (fun r ↦ hstage (α r) _)
  · intro k α i j h
    have : IsAffine ((firstLimitIntersectionDiagram D k α).obj i).left :=
      (hprod k _ (fun r ↦ hstage (α r) (op (unop i (α r))))).1
    have : IsAffine ((firstLimitIntersectionDiagram D k α).obj j).left :=
      (hprod k _ (fun r ↦ hstage (α r) (op (unop j (α r))))).1
    infer_instance
  · intro k α j
    have : IsAffine (∏ᶜ fun r ↦ Over.mk (f (α r)).left).left :=
      (hprod k _ (fun r ↦ hV (α r))).1
    have : IsAffine ((firstLimitIntersectionDiagram D k α).obj j).left :=
      (hprod k _ (fun r ↦ hstage (α r) (op (unop j (α r))))).1
    exact @isAffineHom_of_isAffine
      (∏ᶜ fun r ↦ Over.mk (f (α r)).left).left
      ((firstLimitIntersectionDiagram D k α).obj j).left ((π k α).app j).left
      inferInstance inferInstance
  · intro k α r j
    exact delete_map (fun s ↦ Over.mk (f (α s)).left)
      (fun s ↦ (D (α s)).obj (op (unop j (α s))))
      (fun s ↦ (q (α s)).app (op (unop j (α s)))) r
  · intro k α r i j h
    exact (delete_map
      (fun s ↦ (firstLimitCoordinate D (α s)).obj i)
      (fun s ↦ (firstLimitCoordinate D (α s)).obj j)
      (fun s ↦ (firstLimitCoordinate D (α s)).map h) r).symm

end AlgebraicGeometry.Scheme.AffineProEt
