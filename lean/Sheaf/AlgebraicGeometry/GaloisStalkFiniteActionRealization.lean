/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import Sheaf.FieldTheory.GaloisAutomorphismExtension
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Finite actions in the essential image of the Galois stalk functor

Source: Stacks Project, Tags 03QT and 03QR.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Source: Stacks Project, Tag 03QT, proof of theorem-equivalence-sheaves-point,
with the action of Tag 03QW and the point description of Tag 03QR.


Proof: The sheaf here is the sheafification of the universe-lifted representable
presheaf of X; no sheaf is chosen from an existence assertion. Sheafification
preserves the stalk, and the representable-stalk isomorphism identifies it with
the Omega-points of X, also after lifting the values. The inverse sends a point
to the germ of the image of the identity section under the sheafification unit.
An Omega-point of X factors uniquely through Spec Ks: factor through its residue
field, which is finite separable over K by the etale fibre theorem, and use that
the separable algebraic elements of Omega are exactly the image of Ks. Uniqueness
follows from the injectivity of Ks into Omega. Conversely precompose any Ks-point
with Spec of this inclusion. These operations are inverse even when X is empty,
and give the underlying equivalence in the conclusion, after composing with j.
For g, extend its automorphism of Ks to a K-automorphism of Omega (extend to the
algebraic closure of K inside Omega, fix a transcendence basis, then extend over
its algebraic closure). Apply the assumed germ formula to the identity germ.
Factoring that changed point through Ks gives precomposition with Spec g, since
the extending automorphism agrees with g on Ks. This proves the displayed
identity on identity germs. Every stalk element is such an identity germ by the
representable-stalk isomorphism, proving the identity for every element. -/
private theorem galoisStalkActionFunctor_representable_comparison
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      ∀ (X : S.Etale),
        let F := (presheafToSheaf J (Type (max (u + 1) v))).obj
          (yoneda.obj X ⋙ uliftFunctor.{max (u + 1) v, u})
        ∃ e : (T.obj F).obj.obj.V ≃
            ((Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) ⟶
              (Etale.forget S).obj X),
          ∀ (g : G) (z : (T.obj F).obj.obj.V),
            (e ((T.obj F).obj.obj.ρ g z)).left =
              Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e z).left := by
  classical
  dsimp only
  intro T j hj X
  let S := Spec (.of K)
  let J := S.smallEtaleTopology
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let p := pointSmallEtale s
  let W := Type (max (u + 1) v)
  let P := yoneda.obj X ⋙ uliftFunctor.{max (u + 1) v, u}
  let F := (presheafToSheaf J W).obj P
  let unit := CategoryTheory.toSheafify J P
  let zid := unit.app (op X) (ULift.up (𝟙 X))
  let η (x : p.fiber.obj X) : p.sheafFiber.obj F :=
    p.toPresheafFiber X x F.obj zid
  have hη : Function.Bijective η := by
    let η₀ (x : p.fiber.obj X) := p.toPresheafFiber X x P (ULift.up (𝟙 X))
    let φ (Y : S.Etale) (y : p.fiber.obj Y) :
        P.obj (op Y) ⟶ ULift.{max (u + 1) v} (p.fiber.obj X) :=
      ↾fun z ↦ ULift.up (p.fiber.map z.down y)
    have hφ : ∀ ⦃Y Z : S.Etale⦄ (f : Y ⟶ Z) (y : p.fiber.obj Y),
        P.map f.op ≫ φ Y y = φ Z (p.fiber.map f y) := by
      intro Y Z f y
      ext z
      change p.fiber.map (f ≫ z.down) y = p.fiber.map z.down (p.fiber.map f y)
      rw [Functor.map_comp]
      rfl
    let ψ := p.presheafFiberDesc φ hφ
    have hleft (x : p.fiber.obj X) : ψ (η₀ x) = ULift.up x := by
      change (p.toPresheafFiber X x P ≫ ψ) (ULift.up (𝟙 X)) = ULift.up x
      rw [p.toPresheafFiber_presheafFiberDesc φ hφ X x]
      change ULift.up (p.fiber.map (𝟙 X) x) = ULift.up x
      rw [p.fiber.map_id]
      rfl
    have hη₀ : Function.Bijective η₀ := by
      constructor
      · intro x x' hh
        have h := congrArg ψ hh
        rw [hleft, hleft] at h
        exact congrArg ULift.down h
      · intro z
        obtain ⟨Y, y, t, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := P) z
        refine ⟨p.fiber.map t.down y, ?_⟩
        have hm : P.map t.down.op (ULift.up (𝟙 X)) = t := by
          change ULift.up (t.down ≫ 𝟙 X) = t
          simp only [Category.comp_id, ULift.up_down]
        exact (p.toPresheafFiber_w_apply t.down y P
          (carrier := fun Z : W ↦ Z) (ULift.up (𝟙 X))).symm.trans
            (congrArg (p.toPresheafFiber Y y P) hm)
    let m := p.presheafFiber.map unit
    have hm : Function.Bijective m := (asIso m).toEquiv.bijective
    have heq : η = fun x ↦ m (η₀ x) := by
      funext x
      exact (p.toPresheafFiber_naturality_apply unit X x
        (carrier := fun Z : W ↦ Z) (ULift.up (𝟙 X))).symm
    rw [heq]
    exact hm.comp hη₀
  let β := CommRingCat.ofHom (algebraMap Ks Ω)
  let sk := Spec.map (CommRingCat.ofHom (algebraMap K Ks))
  have ht : Spec.map β ≫ sk = s := by
    rw [← Spec.map_comp]
    congr 1
    ext t
    exact (IsScalarTower.algebraMap_apply K Ks Ω t).symm
  let q : (Over.mk sk ⟶ (Etale.forget S).obj X) → p.fiber.obj X :=
    fun y ↦ Over.homMk (Spec.map β ≫ y.left) (by rw [Category.assoc, y.w]; exact ht)
  have hq : Function.Bijective q := by
    have : IsSepClosed Ks := IsSepClosure.sep_closed K
    constructor
    · intro y y' hh
      apply Over.OverMorphism.ext
      exact SpecMap_comp_injective β (congrArg Over.Hom.left hh)
    · intro x
      obtain ⟨y, hy, hw⟩ := X.hom.exists_SpecMap_comp_eq_of_isSepClosed
        β sk x.left (by exact x.w.trans ht.symm)
      refine ⟨Over.homMk y hw, ?_⟩
      apply Over.OverMorphism.ext
      exact hy
  let a := Equiv.ofBijective η hη
  let b := Equiv.ofBijective q hq
  let e : (T.obj F).obj.obj.V ≃ (Over.mk sk ⟶ (Etale.forget S).obj X) :=
    (j.app F).toEquiv.trans (a.symm.trans b.symm)
  refine ⟨e, ?_⟩
  intro g z
  obtain ⟨y, rfl⟩ := e.symm.surjective z
  obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
  let y' : Over.mk sk ⟶ (Etale.forget S).obj X :=
    Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y.left) (by
      rw [Category.assoc, y.w]
      change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sk = sk
      dsimp [sk]
      rw [← Spec.map_comp]
      congr 1
      ext t
      exact g.commutes t)
  have hx : (q y').left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (q y).left := by
    change Spec.map β ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y.left =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map β ≫ y.left
    rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom hτ
  have hg := hj F g τ hτ X (q y) (q y') hx zid
  have hz : e.symm y = (j.inv.app F) (η (q y)) := rfl
  have heq : e ((T.obj F).obj.obj.ρ g (e.symm y)) = y' := by
    apply b.injective
    change b (b.symm (a.symm ((j.hom.app F)
      ((T.obj F).obj.obj.ρ g (e.symm y))))) = b y'
    rw [b.apply_symm_apply]
    apply a.injective
    rw [a.apply_symm_apply]
    change (j.hom.app F) ((T.obj F).obj.obj.ρ g (e.symm y)) = η (q y')
    rw [hz]
    exact hg
  rw [heq, e.apply_symm_apply]
  rfl

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Tag 03QT, proof of theorem-equivalence-sheaves-point,
using Tag 03QR. (blueprint: lem-exc-galois-stalk-finite-action-realization).

Proof: Replace the finite underlying set of M by Fin n in Type u and transport its
continuous action along a bijection. Apply etaleFieldGsets to obtain an etale
K-scheme X with this small G-set of Ks-points. The representable presheaf of X
is a sheaf by smallEtaleRepresentablePresheaf_isSheaf; lift its values to
Type (max (u + 1) v). The representable-stalk isomorphism identifies its stalk
with the Omega-points of X. Every such point factors uniquely through Ks:
its residue field is finite separable over K, so its embedding into Omega lands
in the image of the separable closure. These factorizations identify Omega-points
with Ks-points. For each g extend its automorphism of Ks to Omega. The assumed
germ formula and the action formula in etaleFieldGsets show that this bijection,
transported through j, is equivariant. Its inverse is equivariant as well, hence
it gives the asserted isomorphism. The empty finite action is represented by
the empty etale scheme. This lemma asserts only finite-action realization. -/
theorem galoisStalkActionFunctor_finite_mem_essImage
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      ∀ (M : DiscreteContAction (Type (max (u + 1) v)) G),
        Finite M.obj.obj.V → T.essImage M := by
  classical
  dsimp only
  intro T j hj M hfinite
  let G := Gal(Ks/K)
  let W := Type (max (u + 1) v)
  let X₀ := (forget₂ (Action W G) TopCat).obj M.obj.obj
  let _ : MulAction G X₀ :=
    inferInstanceAs (MulAction G ((forget₂ (Action W G) TopCat).obj M.obj.obj))
  have : ContinuousSMul G X₀ := M.obj.property
  have : DiscreteTopology X₀ := M.property
  let : Finite X₀ := hfinite
  obtain ⟨n, ⟨a⟩⟩ := Finite.exists_equiv_fin X₀
  let B := ULift.{u} (Fin n)
  let _ : TopologicalSpace B := ⊥
  let b : B ≃ X₀ := Equiv.ulift.trans a.symm
  let _ : MulAction G B :=
    { smul := fun g x ↦ b.symm (g • b x)
      one_smul := fun x ↦ by
        change b.symm (1 • b x) = x
        simp
      mul_smul := fun g h x ↦ by
        change b.symm ((g * h) • b x) = b.symm (g • b (b.symm (h • b x)))
        simp [mul_smul] }
  let A : DiscreteContAction (Type u) G :=
    ⟨⟨Action.ofMulAction G B, by
      apply (Action.isContinuous_def _).mpr
      change Continuous (fun q : G × TopCat.discrete.obj B ↦
        (b.symm (q.1 • b q.2) : TopCat.discrete.obj B))
      let b' : TopCat.discrete.obj B ≃ₜ X₀ :=
        { toEquiv := b
          continuous_toFun := continuous_of_discreteTopology
          continuous_invFun := continuous_of_discreteTopology }
      exact b'.symm.continuous.comp
        (continuous_fst.smul (b'.continuous.comp continuous_snd))⟩, by
      change DiscreteTopology (TopCat.discrete.obj B)
      infer_instance⟩
  obtain ⟨E, points, _, haction, _⟩ := etaleFieldGsets.{u, u} K Ks
  let X := E.inverse.obj A
  let c : E.functor.obj X ≅ A := E.counitIso.app A
  let d : (E.functor.obj X).obj.obj.V ≃ B :=
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
      Action.forget (Type u) G).mapIso c).toEquiv
  let F := (presheafToSheaf (Spec (.of K)).smallEtaleTopology W).obj
    (yoneda.obj X ⋙ uliftFunctor.{max (u + 1) v, u})
  obtain ⟨e, he⟩ := galoisStalkActionFunctor_representable_comparison K Ks Ω T j hj X
  let f : (T.obj F).obj.obj.V ≃ M.obj.obj.V :=
    e.trans ((points X).symm.trans (d.trans b))
  have hf (g : G) (z : (T.obj F).obj.obj.V) :
      f ((T.obj F).obj.obj.ρ g z) = M.obj.obj.ρ g (f z) := by
    have hp : e ((T.obj F).obj.obj.ρ g z) =
        points X ((E.functor.obj X).obj.obj.ρ g ((points X).symm (e z))) := by
      apply Over.OverMorphism.ext
      rw [he, haction, Equiv.apply_symm_apply]
    have hd (x : (E.functor.obj X).obj.obj.V) :
        d ((E.functor.obj X).obj.obj.ρ g x) = g • d x :=
      ConcreteCategory.congr_hom (c.hom.hom.hom.comm g) x
    change b (d ((points X).symm (e ((T.obj F).obj.obj.ρ g z)))) = _
    rw [hp, Equiv.symm_apply_apply, hd]
    change b (b.symm (g • b (d ((points X).symm (e z))))) = _
    exact b.apply_symm_apply _
  refine ⟨F, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact Action.mkIso f.toIso (fun g ↦ by ext z; exact hf g z)


end AlgebraicGeometry.Scheme
