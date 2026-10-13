/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# The bracket on the Lie algebra of a group scheme

The bracket of `Lie(G)` as the mixed term of the commutator of infinitesimal points, the
rescaling of infinitesimal points, and the functoriality of infinitesimal points in the group
scheme.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

/-! ### The bracket as the mixed term of the commutator -/

/-- The points of `G` over `S[ε][δ]` reducing to the identity both for `ε = 0` and for `δ = 0`. -/
noncomputable def mixedPoints : Subgroup (Scheme.dualNumbers₂Over S ⟶ G) :=
  (pointsPrecomp G (Scheme.dualNumbersιεOver S)).ker ⊓
    (pointsPrecomp G (Scheme.dualNumbersιδOver S)).ker

theorem mem_mixedPoints {z : Scheme.dualNumbers₂Over S ⟶ G} :
    z ∈ mixedPoints G ↔ Scheme.dualNumbersιεOver S ≫ z = 1 ∧ Scheme.dualNumbersιδOver S ≫ z = 1 :=
  Iff.rfl

/-- The map `μ : infPoints G → mixedPoints G` induced by `η ↦ εδ`. -/
noncomputable def toMixed (v : infPoints G) : mixedPoints G :=
  ⟨Scheme.dualNumbersMulOver S ≫ v.1, by
    have hv := (mem_infPoints G).1 v.2
    rw [mem_mixedPoints, Scheme.dualNumbersιεOver_comp_dualNumbersMulOver_assoc,
      Scheme.dualNumbersιδOver_comp_dualNumbersMulOver_assoc, hv, MonObj.comp_one]
    exact ⟨rfl, rfl⟩⟩

@[simp]
theorem coe_toMixed (v : infPoints G) :
    (toMixed G v : Scheme.dualNumbers₂Over S ⟶ G) = Scheme.dualNumbersMulOver S ≫ v.1 :=
  rfl

private theorem mixed_comp_injective {Y : Scheme.{u}} (v w : S.dualNumbers ⟶ Y)
    (h : S.dualNumbersMul ≫ v = S.dualNumbersMul ≫ w) : v = w := by
  have hb : v.base = w.base := congrArg (fun f : S.dualNumbers.dualNumbers ⟶ Y ↦ f.base) h
  rcases v with ⟨⟨⟨vb, vc⟩, vp⟩⟩
  rcases w with ⟨⟨⟨wb, wc⟩, wp⟩⟩
  change vb = wb at hb
  subst wb
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  have e := Scheme.Hom.congr_app h U
  simp only [Scheme.Hom.comp_app, eqToHom_op, eqToHom_map] at e
  simp only [eqToHom_refl, Category.comp_id] at e
  ext a : 2
  have ea := ConcreteCategory.congr_hom e a
  change DualNumber.mulRingHom (vc.app _ a) = DualNumber.mulRingHom (wc.app _ a) at ea
  apply TrivSqZeroExt.ext
  · simpa using congrArg (fun x ↦ x.fst.fst) ea
  · simpa using congrArg (fun x ↦ x.snd.snd) ea

private def compressRingHom {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* DualNumber (DualNumber R))
    (he : ∀ a, (f a).fst.snd = 0) (hd : ∀ a, (f a).snd.fst = 0) :
    A →+* DualNumber R where
  toFun a := inl (f a).fst.fst + inr (f a).snd.snd
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [snd_mul, smul_eq_mul, he, hd]

private theorem mixed_factorization {Y : Scheme.{u}}
    (z : S.dualNumbers.dualNumbers ⟶ Y) (g : S ⟶ Y)
    (he : S.dualNumbers.dualNumbersι ≫ z = S.dualNumbersProj ≫ g)
    (hd : S.dualNumbersι.dualNumbers ≫ z = S.dualNumbersProj ≫ g) :
    ∃ v : S.dualNumbers ⟶ Y, S.dualNumbersMul ≫ v = z ∧ S.dualNumbersι ≫ v = g := by
  have hb : z.base = g.base :=
    congrArg (fun f : S.dualNumbers ⟶ Y ↦ f.base) he
  rcases z with ⟨⟨⟨zb, zc⟩, zp⟩⟩
  rcases g with ⟨⟨⟨gb, gc⟩, gp⟩⟩
  change zb = gb at hb
  subst gb
  have e (U : Y.Opens) := Scheme.Hom.congr_app he U
  have d (U : Y.Opens) := Scheme.Hom.congr_app hd U
  simp only [Scheme.Hom.comp_app, eqToHom_op, eqToHom_map] at e d
  simp only [eqToHom_refl, Category.comp_id] at e d
  have ef (U : Y.Opens) (a : Γ(Y, U)) : (zc.app (Opposite.op U) a).fst =
      inl (gc.app (Opposite.op U) a) := by
    exact ConcreteCategory.congr_hom (e U) a
  have es (U : Y.Opens) (a : Γ(Y, U)) :
      DualNumber.mapRingHom
        (fstHom Γ(S, (TopologicalSpace.Opens.map zb).obj U)
          Γ(S, (TopologicalSpace.Opens.map zb).obj U)
          Γ(S, (TopologicalSpace.Opens.map zb).obj U)).toRingHom
        (zc.app (Opposite.op U) a) =
        inl (gc.app (Opposite.op U) a) := by
    exact ConcreteCategory.congr_hom (d U) a
  have ez (U : Y.Opens) (a : Γ(Y, U)) : (zc.app (Opposite.op U) a).fst.snd = 0 :=
    (congrArg snd (ef U a)).trans (snd_inl _ _)
  have dz (U : Y.Opens) (a : Γ(Y, U)) : (zc.app (Opposite.op U) a).snd.fst = 0 := by
    simpa using congrArg snd (es U a)
  let vc : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat zb).obj
      S.dualNumbers.presheaf :=
    { app := fun U ↦ CommRingCat.ofHom (compressRingHom (zc.app U).hom (ez U.unop)
        (dz U.unop))
      naturality := by
        intro U V i
        ext a : 2
        have hn := ConcreteCategory.congr_hom (zc.naturality i) a
        change zc.app V (Y.presheaf.map i a) =
          DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map
            ((TopologicalSpace.Opens.map zb).map i.unop).op).hom) (zc.app U a) at hn
        change inl (zc.app V (Y.presheaf.map i a)).fst.fst +
            inr (zc.app V (Y.presheaf.map i a)).snd.snd =
          DualNumber.mapRingHom (S.presheaf.map _).hom
            (inl (zc.app U a).fst.fst + inr (zc.app U a).snd.snd)
        apply TrivSqZeroExt.ext
        · simp only [fst_add, fst_inl, fst_inr, add_zero, DualNumber.fst_mapRingHom]
          have hn' := congrArg (fun x ↦ x.fst.fst) hn
          change (zc.app V (Y.presheaf.map i a)).fst.fst =
            (DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map
              ((TopologicalSpace.Opens.map zb).map i.unop).op).hom)
              (zc.app U a)).fst.fst at hn'
          rw [DualNumber.fst_mapRingHom, DualNumber.fst_mapRingHom] at hn'
          exact hn'
        · simp only [snd_add, snd_inl, snd_inr, zero_add, DualNumber.snd_mapRingHom]
          have hn' := congrArg (fun x ↦ x.snd.snd) hn
          change (zc.app V (Y.presheaf.map i a)).snd.snd =
            (DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map
              ((TopologicalSpace.Opens.map zb).map i.unop).op).hom)
              (zc.app U a)).snd.snd at hn'
          rw [DualNumber.snd_mapRingHom, DualNumber.snd_mapRingHom] at hn'
          exact hn' }
  let v₀ : S.dualNumbers.toPresheafedSpace ⟶ Y.toPresheafedSpace := ⟨zb, vc⟩
  have hι : S.dualNumbersι.toPshHom ≫ v₀ =
      (⟨⟨⟨zb, gc⟩, gp⟩⟩ : S ⟶ Y).toPshHom := by
    refine PresheafedSpace.ext _ _ rfl ?_
    ext U a
    simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
      TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
      Category.comp_id]
    change (inl (zc.app (Opposite.op U) a).fst.fst +
      inr (zc.app (Opposite.op U) a).snd.snd).fst = gc.app _ a
    simpa [compressRingHom] using congrArg fst (ef U a)
  let v : S.dualNumbers ⟶ Y :=
    { toHom := v₀
      prop := fun x ↦ by
        have h := PresheafedSpace.stalkMap.comp S.dualNumbersι.toPshHom v₀ x
        rw [PresheafedSpace.stalkMap.congr_hom _ _ hι, eqToHom_refl,
          Category.id_comp] at h
        have hh := gp x
        rw [h, CommRingCat.hom_comp] at hh
        exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ hh }
  refine ⟨v, ?_, Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' hι)⟩
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  ext a : 2
  change DualNumber.mulRingHom (inl (zc.app (Opposite.op U) a).fst.fst +
    inr (zc.app (Opposite.op U) a).snd.snd) = zc.app _ a
  apply TrivSqZeroExt.ext
  · apply TrivSqZeroExt.ext
    · simp
    · simpa using (ez U a).symm
  · apply TrivSqZeroExt.ext
    · simpa using (dz U a).symm
    · simp

/-- `η ↦ εδ` identifies the infinitesimal points with the points over `S[ε][δ]` trivial for
`ε = 0` and for `δ = 0`: such a point has `z^♯(a) = e^♯(a) + εδ d(a)` for a derivation `d`. -/
theorem toMixed_bijective : Function.Bijective (toMixed G) := by
  constructor
  · intro v w h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply mixed_comp_injective
    exact congrArg (fun z : mixedPoints G ↦ z.1.left) h
  · intro z
    have h₁ : (1 : Scheme.dualNumbersOver S ⟶ G).left =
        S.dualNumbersProj ≫ unitSection G := by
      simp [Hom.one_def, Over.toUnit_left, unitSection]
    have he : S.dualNumbers.dualNumbersι ≫ z.1.left =
        S.dualNumbersProj ≫ unitSection G :=
      (congrArg (fun f ↦ f.left) ((mem_mixedPoints G).mp z.2).1).trans h₁
    have hd : S.dualNumbersι.dualNumbers ≫ z.1.left =
        S.dualNumbersProj ≫ unitSection G :=
      (congrArg (fun f ↦ f.left) ((mem_mixedPoints G).mp z.2).2).trans h₁
    obtain ⟨v, hv, hi⟩ := mixed_factorization z.1.left (unitSection G) he hd
    have hbase : v ≫ G.hom = S.dualNumbersProj := by
      apply mixed_comp_injective
      rw [← Category.assoc, hv, Over.w z.1, Scheme.dualNumbersMul_comp_proj]
      rfl
    let a : Scheme.dualNumbersOver S ⟶ G := Over.homMk v hbase
    have ha : a ∈ infPoints G := by
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      exact hi.trans (one_left G).symm
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact hv

/-- The infinitesimal points are the mixed points, through `η ↦ εδ`. -/
noncomputable def mixedEquiv : infPoints G ≃ mixedPoints G :=
  Equiv.ofBijective _ (toMixed_bijective G)

/-- The point `v_ε : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `δ`. -/
noncomputable def toε (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjεOver S ≫ v.1

/-- The point `v_δ : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `ε`. -/
noncomputable def toδ (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjδOver S ≫ v.1

/-- The commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` of two infinitesimal points reduces to the identity both
for `ε = 0` and for `δ = 0`. -/
theorem commutator_mem_mixedPoints (v w : infPoints G) :
    toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ ∈ mixedPoints G := by
  have he : Scheme.dualNumbersιεOver S ≫ Scheme.dualNumbersProjδOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    apply Over.OverMorphism.ext
    simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjδOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hd : Scheme.dualNumbersιδOver S ≫ Scheme.dualNumbersProjεOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    apply Over.OverMorphism.ext
    simp [Scheme.dualNumbersιδOver, Scheme.dualNumbersProjεOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hw : Scheme.dualNumbersιεOver S ≫ toδ G w = 1 := by
    rw [toδ, ← Category.assoc, he, Category.assoc, (mem_infPoints G).mp w.2]
    exact MonObj.comp_one _
  have hv : Scheme.dualNumbersιδOver S ≫ toε G v = 1 := by
    rw [toε, ← Category.assoc, hd, Category.assoc, (mem_infPoints G).mp v.2]
    exact MonObj.comp_one _
  rw [mem_mixedPoints]
  constructor
  · change pointsPrecomp G (Scheme.dualNumbersιεOver S) _ = 1
    simp only [map_mul, map_inv, pointsPrecomp_apply, hw]
    simp
  · change pointsPrecomp G (Scheme.dualNumbersιδOver S) _ = 1
    simp only [map_mul, map_inv, pointsPrecomp_apply, hv]
    simp

/-- The bracket of two infinitesimal points: the mixed term `εδ` of their group commutator
`v_ε w_δ v_ε⁻¹ w_δ⁻¹` over `S[ε][δ]`. It is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields extending `v` and `w`. (blueprint: `sk-d-tangent`) -/
noncomputable def infBracket (v w : infPoints G) : infPoints G :=
  (mixedEquiv G).symm ⟨_, commutator_mem_mixedPoints G v w⟩

/-- The Lie bracket on `Lie(G)`, transported from the infinitesimal points. -/
noncomputable instance : Bracket (Lie G) (Lie G) where
  bracket x y := lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y))

theorem lie_def (x y : Lie G) :
    ⁅x, y⁆ = lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y)) :=
  rfl

/-- The mixed-commutator bracket is additive in its first argument.
Source: the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint `sk-d-tangent`.

Proof: Put v = (lieEquiv G).symm x. Base change v along G → S and right-multiply the
universal point of G by this infinitesimal point. The resulting automorphism of G[ε]
reduces to the identity, so on every open its comorphism has the unique form
f ↦ f + ε D_x(f). Multiplicativity makes D_x a relative derivation; restriction of
comorphisms makes these derivations agree on overlaps. Associativity of multiplication
makes D_x left invariant. Evaluation at the identity recovers x, so x ↦ D_x is
injective. The product of two such automorphisms with the same ε has coefficient
D_x + D_y, since ε² = 0. The identity has coefficient zero. Together with
lieEquiv_mul and lieEquiv_one this gives D_(x+y) = D_x + D_y and D_0 = 0.
For independent ε and δ the pullback of right multiplication by the commutator is
(1+εD_x)(1+δD_y)(1-εD_x)(1-δD_y)
= 1 + εδ(D_x D_y - D_y D_x). Here the derivations act coefficientwise, killing
ε and δ; the inverse formulas use ε² = δ² = 0. The definition of infBracket and
mixedEquiv, followed by evaluation at the identity, therefore identifies
D_⁅x,y⁆ with D_x D_y - D_y D_x. These constructions are on the structure sheaf:
no affineness, smoothness, or characteristic restriction is used.
Now expand (D_x + D_y)D_z - D_z(D_x + D_y). Distributivity gives
(D_x D_z - D_z D_x) + (D_y D_z - D_z D_y), which is the derivation attached to
the right-hand side. Injectivity of the invariant extension proves the equality.
(blueprint: lem-ag-lie-bracket-add) -/
theorem lieBracket_add (x y z : Lie G) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by sorry

/-- The mixed-commutator bracket is additive in its second argument.
Source: the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint `sk-d-tangent`.

Proof: Put v = (lieEquiv G).symm x. Base change v along G → S and right-multiply the
universal point of G by this infinitesimal point. The resulting automorphism of G[ε]
reduces to the identity, so on every open its comorphism has the unique form
f ↦ f + ε D_x(f). Multiplicativity makes D_x a relative derivation; restriction of
comorphisms makes these derivations agree on overlaps. Associativity of multiplication
makes D_x left invariant. Evaluation at the identity recovers x, so x ↦ D_x is
injective. The product of two such automorphisms with the same ε has coefficient
D_x + D_y, since ε² = 0. The identity has coefficient zero. Together with
lieEquiv_mul and lieEquiv_one this gives D_(x+y) = D_x + D_y and D_0 = 0.
For independent ε and δ the pullback of right multiplication by the commutator is
(1+εD_x)(1+δD_y)(1-εD_x)(1-δD_y)
= 1 + εδ(D_x D_y - D_y D_x). Here the derivations act coefficientwise, killing
ε and δ; the inverse formulas use ε² = δ² = 0. The definition of infBracket and
mixedEquiv, followed by evaluation at the identity, therefore identifies
D_⁅x,y⁆ with D_x D_y - D_y D_x. These constructions are on the structure sheaf:
no affineness, smoothness, or characteristic restriction is used.
Now expand D_x(D_y + D_z) - (D_y + D_z)D_x. Distributivity gives
(D_x D_y - D_y D_x) + (D_x D_z - D_z D_x), which is the derivation attached to
the right-hand side. Injectivity of the invariant extension proves the equality.
(blueprint: lem-ag-lie-bracket-add-right) -/
theorem lieBracket_add_right (x y z : Lie G) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by sorry

/-- The mixed-commutator bracket is alternating, in every characteristic.
Source: the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint `sk-d-tangent`.

Proof: Put v = (lieEquiv G).symm x. Base change v along G → S and right-multiply the
universal point of G by this infinitesimal point. The resulting automorphism of G[ε]
reduces to the identity, so on every open its comorphism has the unique form
f ↦ f + ε D_x(f). Multiplicativity makes D_x a relative derivation; restriction of
comorphisms makes these derivations agree on overlaps. Associativity of multiplication
makes D_x left invariant. Evaluation at the identity recovers x, so x ↦ D_x is
injective. The product of two such automorphisms with the same ε has coefficient
D_x + D_y, since ε² = 0. The identity has coefficient zero. Together with
lieEquiv_mul and lieEquiv_one this gives D_(x+y) = D_x + D_y and D_0 = 0.
For independent ε and δ the pullback of right multiplication by the commutator is
(1+εD_x)(1+δD_y)(1-εD_x)(1-δD_y)
= 1 + εδ(D_x D_y - D_y D_x). Here the derivations act coefficientwise, killing
ε and δ; the inverse formulas use ε² = δ² = 0. The definition of infBracket and
mixedEquiv, followed by evaluation at the identity, therefore identifies
D_⁅x,y⁆ with D_x D_y - D_y D_x. These constructions are on the structure sheaf:
no affineness, smoothness, or characteristic restriction is used.
For y = x the commutator derivation is D_x D_x - D_x D_x = 0 = D_0.
Injectivity of the invariant extension proves the equality. This uses subtraction
of an expression from itself, with no division by two, and also applies in characteristic two.
(blueprint: lem-ag-lie-bracket-self) -/
theorem lieBracket_self (x : Lie G) :
    ⁅x, x⁆ = 0 := by sorry

/-- The mixed-commutator bracket satisfies the derivation form of the Jacobi identity.
Source: the Lie-ring paragraph of
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint `sk-d-tangent`.

Proof: Put v = (lieEquiv G).symm x. Base change v along G → S and right-multiply the
universal point of G by this infinitesimal point. The resulting automorphism of G[ε]
reduces to the identity, so on every open its comorphism has the unique form
f ↦ f + ε D_x(f). Multiplicativity makes D_x a relative derivation; restriction of
comorphisms makes these derivations agree on overlaps. Associativity of multiplication
makes D_x left invariant. Evaluation at the identity recovers x, so x ↦ D_x is
injective. The product of two such automorphisms with the same ε has coefficient
D_x + D_y, since ε² = 0. The identity has coefficient zero. Together with
lieEquiv_mul and lieEquiv_one this gives D_(x+y) = D_x + D_y and D_0 = 0.
For independent ε and δ the pullback of right multiplication by the commutator is
(1+εD_x)(1+δD_y)(1-εD_x)(1-δD_y)
= 1 + εδ(D_x D_y - D_y D_x). Here the derivations act coefficientwise, killing
ε and δ; the inverse formulas use ε² = δ² = 0. The definition of infBracket and
mixedEquiv, followed by evaluation at the identity, therefore identifies
D_⁅x,y⁆ with D_x D_y - D_y D_x. These constructions are on the structure sheaf:
no affineness, smoothness, or characteristic restriction is used.
Write A = D_x, B = D_y, C = D_z and use associative composition. The left
side becomes ABC - ACB - BCA + CBA. The two terms on the right expand to
ABC - BAC - CAB + CBA and BAC - BCA - ACB + CAB. Adding cancels BAC and CAB
with their negatives and gives precisely the left side. Thus the associated
derivations agree, and injectivity of the invariant extension proves the identity.
(blueprint: lem-ag-lie-bracket-leibniz) -/
theorem lieBracket_leibniz (x y z : Lie G) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by sorry

/-- `Lie(G)` is a Lie ring: the bracket is biadditive, alternating and satisfies the Jacobi
identity, as the commutator of derivations of `𝒪_G`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieRing (Lie G) where
  add_lie := lieBracket_add G
  lie_add := lieBracket_add_right G
  lie_self := lieBracket_self G
  leibniz_lie := lieBracket_leibniz G

/-! ### Rescaling infinitesimal points -/

omit [GrpObj G] in
/-- Multiplying the morphism attached to a derivation by a global function `r` multiplies the
derivation by `r`. -/
theorem homOfDerivation_comp_unitSmul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (r : Γ(S, ⊤)) :
    homOfDerivation G g D ≫ Scheme.Modules.unitSmul r = homOfDerivation G g
      (D.postcomp ((Scheme.Modules.pushforward g).map (Scheme.Modules.unitSmul r)).val) := by
  rw [homOfDerivation, homOfDerivation, ← Adjunction.homEquiv_naturality_right_symm,
    ← PresheafOfModules.Derivation.Universal.desc_comp]
  exact congrArg _ (PresheafOfModules.sheafificationHomEquiv_symm_comp _ _ _).symm

theorem dualNumbersScaleOver_comp_mem_infPoints (r : Γ(S, ⊤))
    {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    Scheme.dualNumbersScaleOver S r ≫ v ∈ infPoints G := by
  rw [mem_infPoints] at hv ⊢
  rw [Scheme.dualNumbersιOver_comp_scaleOver_assoc, hv]

/-- The rescaling `v ↦ v(rε)` of an infinitesimal point by a global function `r`. It is the
multiplication by `r` on the Lie algebra (`toLie_infPointsScale`). -/
noncomputable def infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) : infPoints G :=
  ⟨Scheme.dualNumbersScaleOver S r ≫ v.1, dualNumbersScaleOver_comp_mem_infPoints G r v.2⟩

theorem toLie_infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) :
    toLie G (infPointsScale G r v) = r • toLie G v := by
  rw [Scheme.Modules.homUnit_smul_def, toLie, toLie, Category.assoc, omegaHom_eq_homOfDerivation,
    omegaHom_eq_homOfDerivation, homOfDerivation_comp_unitSmul]
  refine pullbackCongr_inv_comp_homOfDerivation G _ _ _ _ fun {V} a ↦ heq_of_eq ?_
  rw [PresheafOfModules.Derivation.postcomp_d_apply]
  change (DualNumber.scale _ (v.1.left.app V.unop a)).snd =
    (v.1.left.app V.unop a).snd * S.presheaf.map (homOfLE le_top).op r
  rw [DualNumber.snd_scale, mul_comm]
  rfl

theorem lieEquiv_symm_smul (r : Γ(S, ⊤)) (x : Lie G) :
    (lieEquiv G).symm (r • x) = infPointsScale G r ((lieEquiv G).symm x) := by
  rw [Equiv.symm_apply_eq]
  change _ = toLie G _
  rw [toLie_infPointsScale]
  exact congrArg (r • ·) ((lieEquiv G).apply_symm_apply x).symm

/-- `Lie(G)` is a Lie algebra over `Γ(S, 𝒪_S)`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul := by
    intro r x y
    have hs (v w : infPoints G) :
        infBracket G v (infPointsScale G r w) = infPointsScale G r (infBracket G v w) := by
      let d₀ := S.dualNumbers.dualNumbersScale (inl r)
      have dbase : d₀ ≫ (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj) =
          S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj := by
        simp [d₀]
      let d : Scheme.dualNumbers₂Over S ⟶ Scheme.dualNumbers₂Over S := Over.homMk d₀ dbase
      have he : d ≫ Scheme.dualNumbersProjεOver S = Scheme.dualNumbersProjεOver S := by
        apply Over.OverMorphism.ext
        exact S.dualNumbers.dualNumbersScale_comp_proj (inl r)
      have hd : d ≫ Scheme.dualNumbersProjδOver S =
          Scheme.dualNumbersProjδOver S ≫ Scheme.dualNumbersScaleOver S r := by
        apply Over.OverMorphism.ext
        change d₀ ≫ S.dualNumbersProj.dualNumbers =
          S.dualNumbersProj.dualNumbers ≫ S.dualNumbersScale r
        refine Scheme.Hom.ext rfl fun U ↦ ?_
        simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
        erw [eqToHom_refl, Category.comp_id]
        ext a : 2
        let c := S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r
        let c₀ := S.dualNumbers.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (inl r)
        change DualNumber.scale c₀ (DualNumber.mapRingHom (inlHom Γ(S, U) Γ(S, U)) a) =
          DualNumber.mapRingHom (inlHom Γ(S, U) Γ(S, U)) (DualNumber.scale c a)
        have hc₀ : c₀ = inl c := by
          change DualNumber.mapRingHom (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
            (inl r) = inl c
          apply TrivSqZeroExt.ext <;> simp [c]
        rw [hc₀]
        apply TrivSqZeroExt.ext
        · apply TrivSqZeroExt.ext
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              fst_add, DualNumber.fst_scale, fst_inl, fst_smul, DualNumber.fst_eps,
              smul_eq_mul, mul_zero, add_zero, DualNumber.snd_scale, inl_mul]
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              fst_add, DualNumber.fst_scale, fst_inl, fst_smul, DualNumber.fst_eps,
              smul_eq_mul, mul_zero, add_zero, snd_inl, DualNumber.snd_scale, inl_mul]
        · apply TrivSqZeroExt.ext
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              snd_add, DualNumber.snd_scale, snd_inl, mul_zero, snd_smul, DualNumber.snd_eps,
              mul_one, smul_eq_mul, zero_add, fst_mul, fst_inl, DualNumber.fst_scale, inl_mul]
            exact mul_comm _ _
          · simp only [DualNumber.mapRingHom, inlHom_apply, DualNumber.inr_eq_smul_eps,
              RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add, map_smul,
              snd_add, DualNumber.snd_scale, snd_inl, mul_zero, snd_smul, DualNumber.snd_eps,
              mul_one, smul_eq_mul, zero_add, snd_mul, fst_inl, smul_zero, add_zero,
              DualNumber.fst_scale, inl_mul]
      have hm : d ≫ Scheme.dualNumbersMulOver S =
          Scheme.dualNumbersMulOver S ≫ Scheme.dualNumbersScaleOver S r := by
        apply Over.OverMorphism.ext
        change d₀ ≫ S.dualNumbersMul = S.dualNumbersMul ≫ S.dualNumbersScale r
        refine Scheme.Hom.ext rfl fun U ↦ ?_
        simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
        erw [eqToHom_refl, Category.comp_id]
        ext a : 2
        let c := S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r
        let c₀ := S.dualNumbers.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (inl r)
        change DualNumber.scale c₀ (DualNumber.mulRingHom a) =
          DualNumber.mulRingHom (DualNumber.scale c a)
        have hc₀ : c₀ = inl c := by
          change DualNumber.mapRingHom (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
            (inl r) = inl c
          apply TrivSqZeroExt.ext <;> simp [c]
        rw [hc₀]
        apply TrivSqZeroExt.ext
        · rw [DualNumber.fst_scale, DualNumber.fst_mulRingHom, DualNumber.fst_mulRingHom,
            DualNumber.fst_scale]
        · rw [DualNumber.snd_scale, DualNumber.snd_mulRingHom, DualNumber.snd_mulRingHom,
            DualNumber.snd_scale]
          change (inl c : DualNumber Γ(S, U)) * inr a.snd = inr (c * a.snd)
          rw [inl_mul_inr]
          rfl
      have hc (a b : infPoints G) :
          Scheme.dualNumbersMulOver S ≫ (infBracket G a b).1 =
            toε G a * toδ G b * (toε G a)⁻¹ * (toδ G b)⁻¹ :=
        congrArg Subtype.val ((mixedEquiv G).apply_symm_apply _)
      have hε : d ≫ toε G v = toε G v := by
        rw [toε, ← Category.assoc, he]
      have hδ : d ≫ toδ G w = toδ G (infPointsScale G r w) := by
        rw [toδ, ← Category.assoc, hd, Category.assoc]
        rfl
      apply (mixedEquiv G).injective
      apply Subtype.ext
      change Scheme.dualNumbersMulOver S ≫ (infBracket G v (infPointsScale G r w)).1 =
        Scheme.dualNumbersMulOver S ≫ Scheme.dualNumbersScaleOver S r ≫ (infBracket G v w).1
      rw [← Category.assoc, ← hm, Category.assoc, hc, hc]
      change _ = pointsPrecomp G d _
      simp only [map_mul, map_inv, pointsPrecomp_apply, hε, hδ]
    rw [lie_def, lieEquiv_symm_smul, hs, lie_def]
    exact toLie_infPointsScale G r _

/-! ### Functoriality -/

variable {G} {H : Over S} [GrpObj H]

theorem comp_mem_infPoints (f : G ⟶ H) [IsMonHom f] {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : v ∈ infPoints G) : v ≫ f ∈ infPoints H := by
  rw [mem_infPoints] at hv ⊢
  rw [← Category.assoc, hv, MonObj.one_comp]

/-- A homomorphism of group schemes `f : G ⟶ H` maps infinitesimal points to infinitesimal
points: `v ↦ v ≫ f`. -/
noncomputable def infPointsMap (f : G ⟶ H) [IsMonHom f] : infPoints G →* infPoints H :=
  ((IsMonHom.monoidHom f _).comp (infPoints G).subtype).codRestrict (infPoints H)
    fun v ↦ comp_mem_infPoints f v.2

@[simp]
theorem coe_infPointsMap_apply (f : G ⟶ H) [IsMonHom f] (v : infPoints G) :
    (infPointsMap f v : Scheme.dualNumbersOver S ⟶ H) = (v : Scheme.dualNumbersOver S ⟶ G) ≫ f :=
  rfl

/-- A homomorphism of group schemes preserves brackets of infinitesimal points: it preserves
group commutators and commutes with `η ↦ εδ`. -/
theorem infPointsMap_infBracket (f : G ⟶ H) [IsMonHom f] (v w : infPoints G) :
    infPointsMap f (infBracket G v w) = infBracket H (infPointsMap f v) (infPointsMap f w) := by
  apply (mixedEquiv H).injective
  apply Subtype.ext
  change Scheme.dualNumbersMulOver S ≫ (infBracket G v w).1 ≫ f =
    Scheme.dualNumbersMulOver S ≫
      (infBracket H (infPointsMap f v) (infPointsMap f w)).1
  have hc (K : Over S) [GrpObj K] (a b : infPoints K) :
      Scheme.dualNumbersMulOver S ≫ (infBracket K a b).1 =
        toε K a * toδ K b * (toε K a)⁻¹ * (toδ K b)⁻¹ := by
    exact congrArg Subtype.val ((mixedEquiv K).apply_symm_apply _)
  rw [← Category.assoc, hc G v w, hc H (infPointsMap f v) (infPointsMap f w)]
  change (IsMonHom.monoidHom f _) _ = _
  simp only [map_mul, map_inv]
  rfl

/-- Let `f : G ⟶ H` be a monomorphism of group schemes, a subgroup scheme of `H`. If the
commutators of the points of `H` over `S[ε][δ]` factor through `G`, then the bracket of two
infinitesimal points of `H` comes from `G`: the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `c ≫ f` for a
point `c` of `G` over `S[ε][δ]`, which is a mixed point of `G` since `f` is a monomorphism, and
its preimage under `η ↦ εδ` is an infinitesimal point of `G` mapping to `[v, w]`.
(blueprint: `sk-i-restriction`) -/
theorem infBracket_mem_range_infPointsMap (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over S ⟶ H, a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (v w : infPoints H) : infBracket H v w ∈ (infPointsMap f).range := by
  obtain ⟨c, hc⟩ := hf (toε H v) (toδ H w)
  change c ≫ f = toε H v * toδ H w * (toε H v)⁻¹ * (toδ H w)⁻¹ at hc
  have hm : c ∈ mixedPoints G := by
    rw [mem_mixedPoints]
    have hh := (mem_mixedPoints H).mp (commutator_mem_mixedPoints H v w)
    constructor
    · apply (cancel_mono f).mp
      rw [Category.assoc, hc, hh.1, MonObj.one_comp]
    · apply (cancel_mono f).mp
      rw [Category.assoc, hc, hh.2, MonObj.one_comp]
  let a := (mixedEquiv G).symm ⟨c, hm⟩
  refine ⟨a, ?_⟩
  apply (mixedEquiv H).injective
  apply Subtype.ext
  have ha : Scheme.dualNumbersMulOver S ≫ a.1 = c :=
    congrArg Subtype.val ((mixedEquiv G).apply_symm_apply ⟨c, hm⟩)
  change Scheme.dualNumbersMulOver S ≫ a.1 ≫ f = _
  rw [← Category.assoc, ha]
  exact hc.trans (congrArg Subtype.val ((mixedEquiv H).apply_symm_apply
    ⟨_, commutator_mem_mixedPoints H v w⟩)).symm

end GrpObj

end InfPoints

end AlgebraicGeometry
