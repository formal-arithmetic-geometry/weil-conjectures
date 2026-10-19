/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Fundamental groups and algebraic constant-field limits

Source: Stacks Project, Fundamental Groups, Tag 0BTV (lemma-limit), second assertion,
specialized to the finite intermediate fields of a separable algebraic extension
(blueprint: lem-wf-pi1-algebraic-field-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

private theorem fieldBaseMap_comp {K A B C : Type u} [Field K] [Field A] [Field B]
    [Field C] [Algebra K A] [Algebra K B] [Algebra K C]
    (X₀ : Over (Spec (.of K))) (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    fieldExtensionBaseMap X₀ ψ ≫ fieldExtensionBaseMap X₀ φ =
      fieldExtensionBaseMap X₀ (ψ.comp φ) := by
  apply Limits.pullback.hom_ext
  · simp [fieldExtensionBaseMap]
  · simp [fieldExtensionBaseMap, ← Spec.map_comp]
    rfl

@[irreducible]
private noncomputable def projectionFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : Spec (.of Ω) ⟶ Y) (h : s ≫ f = t) : pullback f ⋙ fiber s ≅ fiber t :=
  pullbackFiberIso f s ≪≫ eqToIso (congrArg fiber h)

private theorem projectionFiberIso_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : Spec (.of Ω) ⟶ Y) (h : s ≫ f = t) (P : Y.FiniteEtale)
    (z : (fiber s).obj ((pullback f).obj P)) :
    ((projectionFiberIso f s t h).hom.app P z).left =
      z.left ≫ Limits.pullback.fst P.obj.hom f := by
  subst t
  unfold projectionFiberIso
  rfl

@[irreducible]
private noncomputable def pastingIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) (P : Z.FiniteEtale) :
    (pullback f).obj ((pullback g).obj P) ≅ (pullback h).obj P := by
  subst h
  exact ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk
    (Limits.pullbackLeftPullbackSndIso P.obj.hom g f) (by simp))

private theorem pastingIso_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) (P : Z.FiniteEtale) :
    (pastingIso f g h w P).hom.hom.left ≫ Limits.pullback.fst P.obj.hom h =
      Limits.pullback.fst _ f ≫ Limits.pullback.fst P.obj.hom g := by
  subst h
  unfold pastingIso
  exact Limits.pullbackLeftPullbackSndIso_hom_fst _ _ _

private theorem fiber_pasting {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    (τ : pullback g ⋙ fiber (s ≫ f) ≅ fiber (s ≫ h))
    (hτ : ∀ (P : Z.FiniteEtale) (z : (fiber (s ≫ f)).obj ((pullback g).obj P)),
      (τ.hom.app P z).left = z.left ≫ Limits.pullback.fst P.obj.hom g)
    (P : Z.FiniteEtale)
    (e : (pullback f).obj ((pullback g).obj P) ≅ (pullback h).obj P)
    (he : e.hom.hom.left ≫ Limits.pullback.fst P.obj.hom h =
      Limits.pullback.fst _ f ≫ Limits.pullback.fst P.obj.hom g)
    (z : (fiber s).obj ((pullback f).obj ((pullback g).obj P))) :
    (pullbackFiberIso h s).hom.app P ((fiber s).map e.hom z) =
      τ.hom.app P ((pullbackFiberIso f s).hom.app _ z) := by
  apply fiber_ext
  simp only [pullbackFiberIso_hom_app_left, fiber_map_left, hτ, Category.assoc, he]

private theorem map_comp_compatible {X Y Z : Scheme.{u}}
    [ConnectedSpace Y] [ConnectedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (τ : pullback g ⋙ fiber (s ≫ f) ≅ fiber (s ≫ p))
    (hτ : ∀ (P : Z.FiniteEtale) (z : (fiber (s ≫ f)).obj ((pullback g).obj P)),
      (τ.hom.app P z).left = z.left ≫ Limits.pullback.fst P.obj.hom g)
    (GX GY GZ : Type u) [Group GX] [Group GY] [Group GZ]
    [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [TopologicalSpace GZ] [IsTopologicalGroup GZ] [CompactSpace GZ]
    [∀ P, MulAction GX ((fiber s).obj P)] [IsNaturalSMul (fiber s) GX]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY]
    [∀ P, MulAction GZ ((fiber (s ≫ p)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ p)) GZ] (a : GX) :
    fundamentalGroupMap τ GY GZ
      (fundamentalGroupMap (pullbackFiberIso f s) GX GY a) =
      fundamentalGroupMap (pullbackFiberIso p s) GX GZ a := by
  apply (toAut_bijective (fiber (s ≫ p)) GZ).injective
  ext P z
  simp only [toAut_hom_app_apply]
  obtain ⟨e, he⟩ : ∃ e : (pullback f).obj ((pullback g).obj P) ≅ (pullback p).obj P,
      e.hom.hom.left ≫ Limits.pullback.fst P.obj.hom p =
        Limits.pullback.fst _ f ≫ Limits.pullback.fst P.obj.hom g :=
    ⟨pastingIso f g p w P, pastingIso_fst f g p w P⟩
  let z' := (pullbackFiberIso f s).inv.app _ (τ.inv.app P z)
  have hz : τ.hom.app P ((pullbackFiberIso f s).hom.app _ z') = z := by
    simp only [z', ← FintypeCat.comp_apply, Iso.inv_hom_id_app, FintypeCat.id_apply]
  rw [← hz, fundamentalGroupMap_smul, fundamentalGroupMap_smul]
  have hf := fiber_pasting f g p s τ hτ P e he
  rw [← hf z', fundamentalGroupMap_smul, ← IsNaturalSMul.naturality, hf]

private theorem naturality_through_isos {C : Type*} [Category C]
    {P Q P' Q' : C} (eP : P' ≅ P) (eQ : Q' ≅ Q)
    (aP : P ⟶ P) (aQ : Q ⟶ Q) (aP' : P' ⟶ P') (aQ' : Q' ⟶ Q')
    (hP : eP.hom ≫ aP = aP' ≫ eP.hom)
    (hQ : eQ.hom ≫ aQ = aQ' ≫ eQ.hom)
    (f : P ⟶ Q) (f' : P' ⟶ Q')
    (hf : eP.inv ≫ f' ≫ eQ.hom = f)
    (hn : f' ≫ aQ' = aP' ≫ f') : f ≫ aQ = aP ≫ f := by
  apply (cancel_epi eP.hom).1
  rw [← hf]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc f', hQ, ← Category.assoc f', hn, hP]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

-- Extend component automorphisms once descent has checked naturality between all models.
private theorem exists_aut_of_models
    {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
    (T : ∀ i, D i ⥤ C) (F : C ⥤ FintypeCat.{u})
    (A : ∀ i, Aut (T i ⋙ F))
    (hobj : ∀ P : C, ∃ (i : I) (Q : D i), Nonempty ((T i).obj Q ≅ P))
    (hmap : ∀ (i j : I) (P : D i) (Q : D j) (f : (T i).obj P ⟶ (T j).obj Q),
      F.map f ≫ (A j).hom.app Q = (A i).hom.app P ≫ F.map f) :
    ∃ a : Aut F, ∀ (i : I) (P : D i), a.hom.app ((T i).obj P) = (A i).hom.app P := by
  classical
  choose i Q he using hobj
  let e (P : C) : (T (i P)).obj (Q P) ≅ P := Classical.choice (he P)
  let σ (P : C) : F.obj P ≅ F.obj P :=
    (F.mapIso (e P)).symm ≪≫ (A (i P)).app (Q P) ≪≫ F.mapIso (e P)
  have hn {P R : C} (f : P ⟶ R) : (σ P).hom ≫ F.map f = F.map f ≫ (σ R).hom := by
    apply (cancel_epi (F.map (e P).hom)).1
    apply (cancel_mono (F.map (e R).inv)).1
    simpa [σ, Functor.map_comp, Category.assoc] using
      (hmap (i P) (i R) (Q P) (Q R) ((e P).hom ≫ f ≫ (e R).inv)).symm
  refine ⟨NatIso.ofComponents σ (fun f ↦ (hn f).symm), ?_⟩
  intro j P
  apply (cancel_epi (F.map (e ((T j).obj P)).hom)).1
  simpa [σ, Category.assoc] using
    (hmap (i ((T j).obj P)) j (Q ((T j).obj P)) P (e ((T j).obj P)).hom).symm

/-- Fundamental groups of the constant-field limit are the topological inverse limit of
fundamental groups at the finite intermediate fields.

Source: Stacks Tag 0BTV (lemma-limit), second assertion
(blueprint: lem-wf-pi1-algebraic-field-limit).

The groups are arbitrary small models of the recorded fibre-functor automorphism groups,
using `IsFundamentalGroup`; `toAutContinuousMulEquiv` identifies each with that group.
The finite-field index is the subtype of all finite-dimensional intermediate fields.
The witnesses `τ` are the canonical fibre identifications: their projection equation
specifies their value on every geometric point, and hence determines them uniquely.
The infimum of equalizer subgroups is precisely the subgroup of compatible families;
its topology is the subtype topology from the product. The final equation specifies
all components of the displayed topological group isomorphism.

Proof (the explicit fibre-functor argument for Tag 0BTV):
1. Finite intermediate fields have common finite upper bounds given by their compositum.
   Object and morphism descent are supplied by finiteEtale_fieldLimit_descent.
2. Work directly with the finite-etale fibre functors and IsFundamentalGroup. Their
   established toAutHomeo identifies each small group model with its automorphism group.
3. The projection fibre identifications of lem-galois-pi1-functoriality compose, since
   both composites send a point to its projection to the original cover. Thus the
   transition maps and the maps from G_L are compatible. The latter give a continuous
   homomorphism into the subgroup, since all product coordinates are continuous.
4. If all these coordinates kill g, object descent in
   lem-wf-finite-etale-field-limit-descent supplies a finite-field model of each cover.
   The action on that model is trivial; naturality transports this to the given cover.
   Faithful evaluation of def-galois-fibre-functor gives g = 1.
5. Given a compatible family, descend each cover to E and conjugate the action of its
   E-component by the fibre identification of that model with the given cover.
6. Enlarging E leaves this permutation unchanged, by compatibility and the action
   characterization of lem-galois-pi1-functoriality.
7. Compare two models at a common field. Morphism descent in
   lem-wf-finite-etale-field-limit-descent descends their comparison morphism after
   enlargement. Naturality intertwines the permutations. An isomorphism need not
   descend as an isomorphism for this argument, so the action is independent of models.
8. Descend any morphism between two covers after choosing models at a common field.
   Naturality there gives naturality of the constructed permutations. Their inverses
   are constructed from the inverse family, yielding an automorphism of the fibre functor.
9. On a cover already defined at E the construction has exactly the prescribed action
   of the E-component. This proves surjectivity and the asserted component formula;
   step 4 gives the other inverse identity.
10. Each finite-stage fundamental group is Hausdorff by toAutHomeo. The subgroup of
    compatible families is therefore Hausdorff. The continuous bijection from compact
    G_L is a homeomorphism, completing the topological group isomorphism.
-/
theorem fundamentalGroup_algebraicFieldLimit
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (X₀ : Over (Spec (.of K)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [ConnectedSpace (fieldExtensionBase X₀ L)]
    [∀ E : {E : IntermediateField K L // FiniteDimensional K E},
      ConnectedSpace (fieldExtensionBase X₀ E.val)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (G_L : Type u) [Group G_L] [TopologicalSpace G_L] [IsTopologicalGroup G_L]
    [CompactSpace G_L] [∀ P, MulAction G_L ((fiber s).obj P)]
    [IsFundamentalGroup (fiber s) G_L]
    (G : {E : IntermediateField K L // FiniteDimensional K E} → Type u)
    [∀ E, Group (G E)] [∀ E, TopologicalSpace (G E)]
    [∀ E, IsTopologicalGroup (G E)] [∀ E, CompactSpace (G E)]
    [∀ E P, MulAction (G E) ((fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val)).obj P)]
    [∀ E, IsFundamentalGroup (fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val)) (G E)] :
    ∃ τ : ∀ (E E' : {E : IntermediateField K L // FiniteDimensional K E}) (h : E.val ≤ E'.val),
        pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ⋙
            fiber (s ≫ fieldExtensionBaseMap X₀ E'.val.val) ≅
          fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val),
      (∀ (E E' : {E : IntermediateField K L // FiniteDimensional K E}) (h : E.val ≤ E'.val)
        (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
        (z : (fiber (s ≫ fieldExtensionBaseMap X₀ E'.val.val)).obj
          ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P)),
        ((τ E E' h).hom.app P z).left =
          z.left ≫ Limits.pullback.fst P.obj.hom
            (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))) ∧
      ∃ e : G_L ≃ₜ* ↥(⨅ E, ⨅ E', ⨅ h : E.val ≤ E'.val,
          MonoidHom.eqLocus
            ((fundamentalGroupMap (τ E E' h) (G E') (G E)).comp
              (Pi.evalMonoidHom G E'))
            (Pi.evalMonoidHom G E)),
        ∀ (g : G_L) (E : {E : IntermediateField K L // FiniteDimensional K E}),
          (e g).val E =
            fundamentalGroupMap (pullbackFiberIso (fieldExtensionBaseMap X₀ E.val.val) s)
              G_L (G E) g := by
  classical
  let I := {E : IntermediateField K L // FiniteDimensional K E}
  let p (E : I) := fieldExtensionBaseMap X₀ E.val.val
  let q (E E' : I) (h : E.val ≤ E'.val) :=
    fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)
  have pq (E E' : I) (h : E.val ≤ E'.val) : p E' ≫ q E E' h = p E :=
    fieldBaseMap_comp X₀ (IntermediateField.inclusion h) E'.val.val
  have hpaths (E E' : I) (h : E.val ≤ E'.val) :
      ∃ τ : pullback (q E E' h) ⋙ fiber (s ≫ p E') ≅ fiber (s ≫ p E),
        ∀ (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
          (z : (fiber (s ≫ p E')).obj ((pullback (q E E' h)).obj P)),
          (τ.hom.app P z).left = z.left ≫ Limits.pullback.fst P.obj.hom (q E E' h) :=
    ⟨projectionFiberIso _ _ _ (by rw [Category.assoc, pq]),
      projectionFiberIso_left _ _ _ _⟩
  choose τ hτ using hpaths
  refine ⟨τ, hτ, ?_⟩
  let r (E : I) : G_L →* G E :=
    fundamentalGroupMap (pullbackFiberIso (p E) s) G_L (G E)
  let t (E E' : I) (h : E.val ≤ E'.val) : G E' →* G E :=
    fundamentalGroupMap (τ E E' h) (G E') (G E)
  have re (E : I) (g : G_L) (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
      (z : (fiber s).obj ((pullback (p E)).obj P)) :
      r E g • (pullbackFiberIso (p E) s).hom.app P z =
        (pullbackFiberIso (p E) s).hom.app P (g • z) :=
    fundamentalGroupMap_smul _ _ _ _ _ _
  have te (E E' : I) (h : E.val ≤ E'.val) (g : G E')
      (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
      (z : (fiber (s ≫ p E')).obj ((pullback (q E E' h)).obj P)) :
      t E E' h g • (τ E E' h).hom.app P z = (τ E E' h).hom.app P (g • z) :=
    fundamentalGroupMap_smul _ _ _ _ _ _
  have rc (E E' : I) (h : E.val ≤ E'.val) (g : G_L) :
      t E E' h (r E' g) = r E g :=
    map_comp_compatible (p E') (q E E' h) (p E) (pq E E' h) s
      (τ E E' h) (hτ E E' h) G_L (G E') (G E) g
  let H : Subgroup (∀ E, G E) := ⨅ E, ⨅ E', ⨅ h : E.val ≤ E'.val,
    MonoidHom.eqLocus ((t E E' h).comp (Pi.evalMonoidHom G E')) (Pi.evalMonoidHom G E)
  let R : G_L →* H :=
    { toFun := fun g ↦ ⟨fun E ↦ r E g, by
        simp only [H, Subgroup.mem_iInf]
        intro E E' h
        exact rc E E' h g⟩
      map_one' := by ext E; exact map_one (r E)
      map_mul' := by intro a b; ext E; exact map_mul (r E) a b }
  have hR : Continuous R := by
    apply Continuous.subtype_mk
    exact continuous_pi fun E ↦ continuous_fundamentalGroupMap _ _ _
  have hRi : Function.Injective R := by
    apply (injective_iff_map_eq_one R).2
    intro g hg
    apply IsFundamentalGroup.non_trivial (F := fiber s) g
    intro P z
    obtain ⟨E, hE, Q, ⟨e⟩⟩ := (finiteEtale_fieldLimit_descent X₀).1 P
    let j : I := ⟨E, hE⟩
    have hr : r j g = 1 := congrArg (fun a : H ↦ a.val j) hg
    have hq (w : (fiber s).obj ((pullback (p j)).obj Q)) : g • w = w := by
      apply ((FintypeCat.equivEquivIso.symm ((pullbackFiberIso (p j) s).app Q))).injective
      change (pullbackFiberIso (p j) s).hom.app Q (g • w) =
        (pullbackFiberIso (p j) s).hom.app Q w
      rw [← re, hr, one_smul]
    let w := (fiber s).map e.inv z
    have hz : (fiber s).map e.hom w = z :=
      ConcreteCategory.congr_hom ((fiber s).mapIso e).inv_hom_id z
    rw [← hz, ← IsNaturalSMul.naturality, hq]
  have hRs : Function.Surjective R := by
    intro a
    have ha (E E' : I) (h : E.val ≤ E'.val) : t E E' h (a.val E') = a.val E :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp a.property E) E') h
    have hA (E : I) : ∃ A : Aut (pullback (p E) ⋙ fiber s),
        ∀ (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
          (z : (fiber s).obj ((pullback (p E)).obj P)),
          A.hom.app P z = (pullbackFiberIso (p E) s).inv.app P
            (a.val E • (pullbackFiberIso (p E) s).hom.app P z) :=
      ⟨pullbackFiberIso (p E) s ≪≫ toAut (fiber (s ≫ p E)) (G E) (a.val E) ≪≫
        (pullbackFiberIso (p E) s).symm, fun _ _ ↦ rfl⟩
    choose A ae using hA
    have ac (E E' : I) (h : E.val ≤ E'.val)
        (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
        (e : (pullback (p E')).obj ((pullback (q E E' h)).obj P) ≅
          (pullback (p E)).obj P)
        (he : e.hom.hom.left ≫ Limits.pullback.fst P.obj.hom (p E) =
          Limits.pullback.fst _ (p E') ≫ Limits.pullback.fst P.obj.hom (q E E' h)) :
        (fiber s).map e.hom ≫ (A E).hom.app P =
          (A E').hom.app ((pullback (q E E' h)).obj P) ≫ (fiber s).map e.hom := by
      ext z
      apply (FintypeCat.equivEquivIso.symm ((pullbackFiberIso (p E) s).app P)).injective
      change (pullbackFiberIso (p E) s).hom.app P
          ((A E).hom.app P ((fiber s).map e.hom z)) =
        (pullbackFiberIso (p E) s).hom.app P
          ((fiber s).map e.hom ((A E').hom.app _ z))
      rw [ae]
      have hc (w : (fiber (s ≫ p E)).obj P) :
          (pullbackFiberIso (p E) s).hom.app P
            ((pullbackFiberIso (p E) s).inv.app P w) = w :=
        ConcreteCategory.congr_hom ((pullbackFiberIso (p E) s).inv_hom_id_app P) w
      rw [hc]
      have hf := fiber_pasting (p E') (q E E' h) (p E) s
        (τ E E' h) (hτ E E' h) P e he
      rw [hf, hf, ← ha E E' h, te, ae]
      congr 1
      exact (ConcreteCategory.congr_hom
        ((pullbackFiberIso (p E') s).inv_hom_id_app _) _).symm
    have am (E : I) (P Q : (fieldExtensionBase X₀ E.val).FiniteEtale)
        (f : (pullback (p E)).obj P ⟶ (pullback (p E)).obj Q) :
        (fiber s).map f ≫ (A E).hom.app Q = (A E).hom.app P ≫ (fiber s).map f := by
      obtain ⟨J, hJ, h, f', eP, eQ, hp, hq, hf⟩ :=
        (finiteEtale_fieldLimit_descent X₀).2.1 E.val E.property P Q f
      let j : I := ⟨J, hJ⟩
      exact naturality_through_isos ((fiber s).mapIso eP) ((fiber s).mapIso eQ)
        _ _ _ _ (ac E j h P eP hp) (ac E j h Q eQ hq)
        ((fiber s).map f) ((fiber s).map ((pullback (p j)).map f'))
        (by simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, p, j]
          using congrArg ((fiber s).map) hf)
        ((A j).hom.naturality f')
    have am' (E E' : I) (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
        (Q : (fieldExtensionBase X₀ E'.val).FiniteEtale)
        (f : (pullback (p E)).obj P ⟶ (pullback (p E')).obj Q) :
        (fiber s).map f ≫ (A E').hom.app Q = (A E).hom.app P ≫ (fiber s).map f := by
      have : FiniteDimensional K E.val := E.property
      have : FiniteDimensional K E'.val := E'.property
      let J : I := ⟨E.val ⊔ E'.val, inferInstance⟩
      let h : E.val ≤ J.val := le_sup_left
      let h' : E'.val ≤ J.val := le_sup_right
      let eP := pastingIso (p J) (q E J h) (p E) (pq E J h) P
      let eQ := pastingIso (p J) (q E' J h') (p E') (pq E' J h') Q
      let f' := eP.hom ≫ f ≫ eQ.inv
      refine naturality_through_isos ((fiber s).mapIso eP) ((fiber s).mapIso eQ)
        _ _ _ _ (ac E J h P eP (pastingIso_fst _ _ _ _ _))
        (ac E' J h' Q eQ (pastingIso_fst _ _ _ _ _))
        ((fiber s).map f) ((fiber s).map f') ?_ (am J _ _ f')
      simp only [f', Functor.map_comp, ← Category.assoc,
        Functor.mapIso_inv, Functor.mapIso_hom]
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    obtain ⟨b, hb⟩ := exists_aut_of_models (fun E : I ↦ pullback (p E)) (fiber s) A
      (by
        intro P
        obtain ⟨E, hE, Q, he⟩ := (finiteEtale_fieldLimit_descent X₀).1 P
        exact ⟨⟨E, hE⟩, Q, he⟩) am'
    obtain ⟨g, hg⟩ := (toAut_bijective (fiber s) G_L).surjective b
    refine ⟨g, ?_⟩
    apply Subtype.ext
    funext E
    apply (toAut_bijective (fiber (s ≫ p E)) (G E)).injective
    ext P z
    simp only [toAut_hom_app_apply]
    change r E g • z = a.val E • z
    let w : (fiber s).obj ((pullback (p E)).obj P) :=
      (pullbackFiberIso (p E) s).inv.app P z
    have hz : (pullbackFiberIso (p E) s).hom.app P w = z :=
      ConcreteCategory.congr_hom ((pullbackFiberIso (p E) s).inv_hom_id_app P) z
    have hgw : g • w = (A E).hom.app P w := by
      rw [← toAut_hom_app_apply, hg]
      exact ConcreteCategory.congr_hom (hb E P) w
    rw [← hz, re, hgw, ae]
    exact ConcreteCategory.congr_hom ((pullbackFiberIso (p E) s).inv_hom_id_app P) _
  have hT2 (E : I) : T2Space (G E) :=
    (toAutHomeo (fiber (s ≫ p E)) (G E)).isEmbedding.t2Space
  let e := MulEquiv.ofBijective R ⟨hRi, hRs⟩
  have he : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hR, e.bijective⟩
  refine ⟨{ toMulEquiv := e
            continuous_toFun := he.continuous
            continuous_invFun := ?_ }, fun _ _ ↦ rfl⟩
  exact (e.toEquiv.toHomeomorphOfContinuousClosed hR hR.isClosedMap).symm.continuous

end AlgebraicGeometry.Scheme.FiniteEtale
