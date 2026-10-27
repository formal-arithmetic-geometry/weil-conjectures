module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.BaseChangeDiagramElementwise
import Mathlib.CategoryTheory.Filtered.Final

/-! # The scalar-extension diagram of a fixed module arrow

Source: Stacks Project, Algebra, Tags 00QX and 046Y, the fixed-stage construction.
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram)

We write scalar tensors with the ring factor first, using Mathlib's canonical
commutativity identification with the paper's module-first convention.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace Module

/-- The actual scalar-extension module on the upper tail of a fixed stage.
Source: Stacks Project, Tag 00QX, presentation construction
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowStage {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (c : I) (P : ModuleCat.{u} (B.obj c)) (j : Set.Ici c) : ModuleCat.{u} (B.obj j.1) :=
  (ModuleCat.extendScalars (B.map (homOfLE j.2)).hom).obj P

/-- A pure tensor in the fixed-stage module, in the paper's argument order.
Source: Stacks Project, Tags 00CX and 00QX
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowStageTmul {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (c : I) (P : ModuleCat.{u} (B.obj c)) (j : Set.Ici c)
    (x : P) (a : B.obj j.1) : fixedArrowStage B c P j :=
  a ⊗ₜ[B.obj c, (B.map (homOfLE j.2)).hom] x

/-- The fixed-stage module extended to the given ring cocone point.
Source: Stacks Project, Tag 00QX
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowLimit {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (A : CommRingCat.{u}) (κ : B ⟶ (Functor.const I).obj A)
    (c : I) (P : ModuleCat.{u} (B.obj c)) : ModuleCat.{u} A :=
  (ModuleCat.extendScalars (κ.app c).hom).obj P

/-- A pure tensor at the cocone point, in the paper's argument order.
Source: Stacks Project, Tags 00CX and 00QX
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowLimitTmul {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (A : CommRingCat.{u}) (κ : B ⟶ (Functor.const I).obj A)
    (c : I) (P : ModuleCat.{u} (B.obj c)) (x : P) (a : A) :
    fixedArrowLimit B A κ c P :=
  a ⊗ₜ[B.obj c, (κ.app c).hom] x

/-- The given arrow extended to a stage on the upper tail.
Source: Stacks Project, Tag 046Y, simultaneous module-arrow construction
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowStageArrow {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (c : I) {P Q : ModuleCat.{u} (B.obj c)} (v : P ⟶ Q) (j : Set.Ici c) :
    fixedArrowStage B c P j ⟶ fixedArrowStage B c Q j :=
  (ModuleCat.extendScalars (B.map (homOfLE j.2)).hom).map v

/-- The given arrow extended to the ring cocone point.
Source: Stacks Project, Tag 046Y, simultaneous module-arrow construction
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram). -/
noncomputable def fixedArrowLimitArrow {I : Type u} [Preorder I] (B : I ⥤ CommRingCat.{u})
    (A : CommRingCat.{u}) (κ : B ⟶ (Functor.const I).obj A)
    (c : I) {P Q : ModuleCat.{u} (B.obj c)} (v : P ⟶ Q) :
    fixedArrowLimit B A κ c P ⟶ fixedArrowLimit B A κ c Q :=
  (ModuleCat.extendScalars (κ.app c).hom).map v

private noncomputable def scalarComparison
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    (P : ModuleCat.{u} R) :
    (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj P) ≅
      (ModuleCat.extendScalars h).obj P := by
  subst h
  exact (ModuleCat.extendScalarsComp f g).symm.app P

private theorem scalarComparison_one
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    (P : ModuleCat.{u} R) (x : P) :
    (scalarComparison f g h hfg P).hom
      ((1 : T) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] x)) = (1 : T) ⊗ₜ[R,h] x := by
  subst h
  apply (scalarComparison f g (g.comp f) rfl P).toLinearEquiv.symm.injective
  change (ModuleCat.extendScalarsComp f g).hom.app P
    ((ModuleCat.extendScalarsComp f g).inv.app P
      ((1 : T) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] x))) = _
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply]
  exact (ModuleCat.extendScalarsComp_hom_app_one_tmul f g P x).symm

private noncomputable def scalarTransition
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    (P : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj P →ₛₗ[g] (ModuleCat.extendScalars h).obj P :=
  (ModuleCat.semilinearMapAddEquiv g _ _).symm
    (ModuleCat.ExtendRestrictScalarsAdj.Unit.map g ≫
      (ModuleCat.restrictScalars g).map (scalarComparison f g h hfg P).hom)

private theorem scalarComparison_formula
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    (P : ModuleCat.{u} R) (z : (ModuleCat.extendScalars f).obj P) (b : T) :
    (scalarComparison f g h hfg P).hom (b ⊗ₜ[S,g] z) =
      b • scalarTransition f g h hfg P z := by
  change (scalarComparison f g h hfg P).hom (b ⊗ₜ[S,g] z) =
    b • (scalarComparison f g h hfg P).hom ((1 : T) ⊗ₜ[S,g] z)
  rw [← map_smul, ModuleCat.ExtendScalars.smul_tmul, mul_one]

private theorem scalarTransition_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    (P : ModuleCat.{u} R) (a : S) (x : P) :
    scalarTransition f g h hfg P (a ⊗ₜ[R,f] x) = (g a) ⊗ₜ[R,h] x := by
  have hone : scalarTransition f g h hfg P ((1 : S) ⊗ₜ[R,f] x) =
      (1 : T) ⊗ₜ[R,h] x := scalarComparison_one f g h hfg P x
  have ha : (a ⊗ₜ[R,f] x : (ModuleCat.extendScalars f).obj P) =
      a • ((1 : S) ⊗ₜ[R,f] x) := by rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ha, map_smulₛₗ, hone, ModuleCat.ExtendScalars.smul_tmul, mul_one]

private theorem scalarTransition_natural
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    {P Q : ModuleCat.{u} R} (v : P ⟶ Q) (z : (ModuleCat.extendScalars f).obj P) :
    scalarTransition f g h hfg Q ((ModuleCat.extendScalars f).map v z) =
      (ModuleCat.extendScalars h).map v (scalarTransition f g h hfg P z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [ModuleCat.ExtendScalars.map_tmul, scalarTransition_tmul,
      scalarTransition_tmul, ModuleCat.ExtendScalars.map_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem scalarComparison_natural
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hfg : g.comp f = h)
    {P Q : ModuleCat.{u} R} (v : P ⟶ Q) :
    (ModuleCat.extendScalars g).map ((ModuleCat.extendScalars f).map v) ≫
        (scalarComparison f g h hfg Q).hom =
      (scalarComparison f g h hfg P).hom ≫ (ModuleCat.extendScalars h).map v := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  simp only [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  change scalarTransition f g h hfg Q ((ModuleCat.extendScalars f).map v z) =
    (ModuleCat.extendScalars h).map v (scalarTransition f g h hfg P z)
  exact scalarTransition_natural f g h hfg v z

private theorem eventual_equality
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : J ⥤ AddCommGrpCat.{u}) (M : Type u) [AddCommGroup M]
    (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
    (hzero : ∀ (i : J) (x : D.obj i), (ν.app i).hom x = 0 →
      ∃ (j : J) (h : i ≤ j), (D.map (homOfLE h)).hom x = 0)
    (i j : J) (x : D.obj i) (y : D.obj j) :
    (ν.app i).hom x = (ν.app j).hom y ↔
      ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
        (D.map (homOfLE hik)).hom x = (D.map (homOfLE hjk)).hom y := by
  have compat (i j : J) (h : i ≤ j) (x : D.obj i) :
      (ν.app j).hom ((D.map (homOfLE h)).hom x) = (ν.app i).hom x :=
    ConcreteCategory.congr_hom (ν.naturality (homOfLE h)) x
  constructor
  · intro hxy
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hz : (ν.app k).hom
        ((D.map (homOfLE hik)).hom x - (D.map (homOfLE hjk)).hom y) = 0 := by
      rw [map_sub, compat, compat, hxy, sub_self]
    obtain ⟨l, hkl, hl⟩ := hzero k _ hz
    refine ⟨l, hik.trans hkl, hjk.trans hkl, ?_⟩
    rw [map_sub, sub_eq_zero] at hl
    have c₁ := ConcreteCategory.congr_hom
      (D.map_comp (homOfLE hik) (homOfLE hkl)) x
    have c₂ := ConcreteCategory.congr_hom
      (D.map_comp (homOfLE hjk) (homOfLE hkl)) y
    exact c₁.trans (hl.trans c₂.symm)
  · rintro ⟨k, hik, hjk, he⟩
    rw [← compat i k hik x, ← compat j k hjk y, he]

private theorem additive_colimit
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : J ⥤ AddCommGrpCat.{u}) (M : Type u) [AddCommGroup M]
    (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
    (hrep : ∀ x : M, ∃ (i : J) (y : D.obj i), (ν.app i).hom y = x)
    (hzero : ∀ (i : J) (x : D.obj i), (ν.app i).hom x = 0 →
      ∃ (j : J) (h : i ≤ j), (D.map (homOfLE h)).hom x = 0)
    (H : AddCommGrpCat.{u}) (f : ∀ i, D.obj i →+ H)
    (hf : ∀ (i j : J) (h : i ≤ j) (z : D.obj i),
      f j ((D.map (homOfLE h)).hom z) = f i z) :
    ∃! g : M →+ H, ∀ (i : J) (z : D.obj i), g ((ν.app i).hom z) = f i z := by
  classical
  have compat (i j : J) (h : i ≤ j) (x : D.obj i) :
      (ν.app j).hom ((D.map (homOfLE h)).hom x) = (ν.app i).hom x :=
    ConcreteCategory.congr_hom (ν.naturality (homOfLE h)) x
  choose idx rep rep_eq using hrep
  let value (x : M) : H := f (idx x) (rep x)
  have value_rep (i : J) (x : D.obj i) : value ((ν.app i).hom x) = f i x := by
    obtain ⟨k, h₁, h₂, he⟩ :=
      (eventual_equality D M ν hzero _ i (rep ((ν.app i).hom x)) x).mp (rep_eq _)
    exact (hf _ _ h₁ _).symm.trans ((congrArg (f k) he).trans (hf _ _ h₂ _))
  let g : M →+ H :=
    { toFun := value
      map_zero' := by
        have hz := value_rep (Classical.arbitrary J) 0
        simpa only [map_zero] using hz
      map_add' := by
        intro x y
        obtain ⟨k, hxk, hyk⟩ := exists_ge_ge (idx x) (idx y)
        let a := (D.map (homOfLE hxk)).hom (rep x)
        let b := (D.map (homOfLE hyk)).hom (rep y)
        have ha : (ν.app k).hom a = x := (compat _ _ hxk _).trans (rep_eq x)
        have hb : (ν.app k).hom b = y := (compat _ _ hyk _).trans (rep_eq y)
        have hab : (ν.app k).hom (a + b) = x + y := by rw [map_add, ha, hb]
        rw [← hab, value_rep, map_add, ← value_rep k a, ← value_rep k b, ha, hb] }
  refine ⟨g, value_rep, ?_⟩
  intro g' hg'
  apply AddMonoidHom.ext
  intro x
  rw [← rep_eq x, hg']
  exact (value_rep _ _).symm

/-- The coherent scalar-extension diagrams of a fixed finitely presented module arrow.
Source: Stacks Project, Tags 00QX and 046Y; explicit fixed-stage construction.
(blueprint: lem-trf-fixed-arrow-scalar-extension-diagram)

Proof:
1. The upper tail contains c and is directed. Upper bounds with c make its inclusion
   cofinal, so the given ring colimit restricts to the tail, by
   lem-weil-pbc-colimit-initial-full-subcategory applied to the opposite categories.
2. The balanced tensor universal property defines the transitions and cocone legs
   by the displayed pure-tensor formulas. Ring functoriality and cocone compatibility
   give balancing, semilinearity, identities, composition and cocone compatibility.
3. Extending v sends x tensor a to v(x) tensor a. Evaluating on pure tensors proves
   both arrow squares; pure tensors additively generate.
4. Tensor a finite free presentation of P or Q. Tensor right exactness
   (lem-weil-pbc-tensor-right-exact), finite products including the empty product
   (lem-weil-pbc-tensor-finite-product), and R tensor_R B = B give finite presentation
   at every stage. Neither flatness nor a nonzero presentation size is needed.
5. The canonical comparison sends z tensor b to b times the transition of z.
   Its inverse sends x tensor b to (x tensor 1) tensor b. The balancing relation
   proves this is well defined and proves both inverse identities on generators.
6. On (x tensor a) tensor b both composites in each comparison square have value
   v(x) tensor h(a)b. Additive generation gives the two intertwining identities.
7. Apply lem-weil-pbc-base-change-diagram-elementwise to P and Q. The comparisons
   of step 5 match its ring-first convention by the tensor flip. It gives stage
   representatives and eventual zero. Move two representatives to an upper bound
   and apply eventual zero to their difference to obtain the common-stage criterion.
8. A compatible additive family to H defines a map on each limit module by a stage
   representative. The common-stage criterion makes this well defined. Moving two
   representatives to one stage proves additivity; representatives force uniqueness.
   This is precisely the colimit universal property in abelian groups.
-/
theorem fixedArrow_scalarExtension_diagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : B ⟶ (Functor.const I).obj A)
    (hκ : Nonempty (IsColimit (Cocone.mk A κ)))
    (c : I) (P Q : ModuleCat.{u} (B.obj c))
    [Module.FinitePresentation (B.obj c) P] [Module.FinitePresentation (B.obj c) Q]
    (v : P ⟶ Q) :
    ∃ (p : ∀ (j k : Set.Ici c) (h : j ≤ k),
          fixedArrowStage B c P j →ₛₗ[(B.map (homOfLE h)).hom] fixedArrowStage B c P k)
      (q : ∀ (j k : Set.Ici c) (h : j ≤ k),
          fixedArrowStage B c Q j →ₛₗ[(B.map (homOfLE h)).hom] fixedArrowStage B c Q k)
      (μ : ∀ j : Set.Ici c,
          fixedArrowStage B c P j →ₛₗ[(κ.app j.1).hom] fixedArrowLimit B A κ c P)
      (ν : ∀ j : Set.Ici c,
          fixedArrowStage B c Q j →ₛₗ[(κ.app j.1).hom] fixedArrowLimit B A κ c Q),
      (∀ (j k : Set.Ici c) (h : j ≤ k) (x : P) (a : B.obj j.1),
        p j k h (fixedArrowStageTmul B c P j x a) =
          fixedArrowStageTmul B c P k x ((B.map (homOfLE h)).hom a)) ∧
      (∀ (j : Set.Ici c) (x : P) (a : B.obj j.1),
        μ j (fixedArrowStageTmul B c P j x a) =
          fixedArrowLimitTmul B A κ c P x ((κ.app j.1).hom a)) ∧
      (∀ (j : Set.Ici c) (x : fixedArrowStage B c P j), p j j le_rfl x = x) ∧
      (∀ (j k l : Set.Ici c) (hjk : j ≤ k) (hkl : k ≤ l)
          (x : fixedArrowStage B c P j),
        p k l hkl (p j k hjk x) = p j l (hjk.trans hkl) x) ∧
      (∀ (j k : Set.Ici c) (h : j ≤ k) (x : fixedArrowStage B c P j),
        μ k (p j k h x) = μ j x) ∧
      (∀ j : Set.Ici c, Module.FinitePresentation (B.obj j.1) (fixedArrowStage B c P j)) ∧
      (∀ (j k : Set.Ici c) (h : j ≤ k) (x : Q) (a : B.obj j.1),
        q j k h (fixedArrowStageTmul B c Q j x a) =
          fixedArrowStageTmul B c Q k x ((B.map (homOfLE h)).hom a)) ∧
      (∀ (j : Set.Ici c) (x : Q) (a : B.obj j.1),
        ν j (fixedArrowStageTmul B c Q j x a) =
          fixedArrowLimitTmul B A κ c Q x ((κ.app j.1).hom a)) ∧
      (∀ (j : Set.Ici c) (x : fixedArrowStage B c Q j), q j j le_rfl x = x) ∧
      (∀ (j k l : Set.Ici c) (hjk : j ≤ k) (hkl : k ≤ l)
          (x : fixedArrowStage B c Q j),
        q k l hkl (q j k hjk x) = q j l (hjk.trans hkl) x) ∧
      (∀ (j k : Set.Ici c) (h : j ≤ k) (x : fixedArrowStage B c Q j),
        ν k (q j k h x) = ν j x) ∧
      (∀ j : Set.Ici c, Module.FinitePresentation (B.obj j.1) (fixedArrowStage B c Q j)) ∧
      (∀ (j k : Set.Ici c) (h : j ≤ k) (x : fixedArrowStage B c P j),
        q j k h (fixedArrowStageArrow B c v j x) =
          fixedArrowStageArrow B c v k (p j k h x)) ∧
      (∀ (j : Set.Ici c) (x : fixedArrowStage B c P j),
        ν j (fixedArrowStageArrow B c v j x) =
          fixedArrowLimitArrow B A κ c v (μ j x)) ∧
      (∀ (j k : Set.Ici c) (h : j ≤ k),
        ∃ (eP : (ModuleCat.extendScalars (B.map (homOfLE h)).hom).obj
              (fixedArrowStage B c P j) ≅ fixedArrowStage B c P k)
          (eQ : (ModuleCat.extendScalars (B.map (homOfLE h)).hom).obj
              (fixedArrowStage B c Q j) ≅ fixedArrowStage B c Q k),
          (∀ (z : fixedArrowStage B c P j) (b : B.obj k.1),
            eP.hom (b ⊗ₜ[B.obj j.1, (B.map (homOfLE h)).hom] z) = b • p j k h z) ∧
          (∀ (z : fixedArrowStage B c Q j) (b : B.obj k.1),
            eQ.hom (b ⊗ₜ[B.obj j.1, (B.map (homOfLE h)).hom] z) = b • q j k h z) ∧
          (ModuleCat.extendScalars (B.map (homOfLE h)).hom).map
              (fixedArrowStageArrow B c v j) ≫ eQ.hom =
            eP.hom ≫ fixedArrowStageArrow B c v k) ∧
      (∀ j : Set.Ici c,
        ∃ (eP : (ModuleCat.extendScalars (κ.app j.1).hom).obj
              (fixedArrowStage B c P j) ≅ fixedArrowLimit B A κ c P)
          (eQ : (ModuleCat.extendScalars (κ.app j.1).hom).obj
              (fixedArrowStage B c Q j) ≅ fixedArrowLimit B A κ c Q),
          (∀ (z : fixedArrowStage B c P j) (b : A),
            eP.hom (b ⊗ₜ[B.obj j.1, (κ.app j.1).hom] z) = b • μ j z) ∧
          (∀ (z : fixedArrowStage B c Q j) (b : A),
            eQ.hom (b ⊗ₜ[B.obj j.1, (κ.app j.1).hom] z) = b • ν j z) ∧
          (ModuleCat.extendScalars (κ.app j.1).hom).map
              (fixedArrowStageArrow B c v j) ≫ eQ.hom =
            eP.hom ≫ fixedArrowLimitArrow B A κ c v) ∧
      (∀ (H : AddCommGrpCat.{u}) (f : ∀ j : Set.Ici c, fixedArrowStage B c P j →+ H),
        (∀ (j k : Set.Ici c) (h : j ≤ k) (z : fixedArrowStage B c P j),
          f k (p j k h z) = f j z) →
        ∃! g : fixedArrowLimit B A κ c P →+ H,
          ∀ (j : Set.Ici c) (z : fixedArrowStage B c P j), g (μ j z) = f j z) ∧
      (∀ x : fixedArrowLimit B A κ c P,
        ∃ (j : Set.Ici c) (z : fixedArrowStage B c P j), μ j z = x) ∧
      (∀ (j k : Set.Ici c) (x : fixedArrowStage B c P j) (y : fixedArrowStage B c P k),
        μ j x = μ k y ↔ ∃ (l : Set.Ici c) (hjl : j ≤ l) (hkl : k ≤ l),
          p j l hjl x = p k l hkl y) ∧
      (∀ (H : AddCommGrpCat.{u}) (f : ∀ j : Set.Ici c, fixedArrowStage B c Q j →+ H),
        (∀ (j k : Set.Ici c) (h : j ≤ k) (z : fixedArrowStage B c Q j),
          f k (q j k h z) = f j z) →
        ∃! g : fixedArrowLimit B A κ c Q →+ H,
          ∀ (j : Set.Ici c) (z : fixedArrowStage B c Q j), g (ν j z) = f j z) ∧
      (∀ x : fixedArrowLimit B A κ c Q,
        ∃ (j : Set.Ici c) (z : fixedArrowStage B c Q j), ν j z = x) ∧
      (∀ (j k : Set.Ici c) (x : fixedArrowStage B c Q j) (y : fixedArrowStage B c Q k),
        ν j x = ν k y ↔ ∃ (l : Set.Ici c) (hjl : j ≤ l) (hkl : k ≤ l),
          q j l hjl x = q k l hkl y) ∧
      Nonempty (Set.Ici c) ∧ IsDirected (Set.Ici c) (· ≤ ·) := by
  classical
  let : Nonempty (Set.Ici c) := ⟨⟨c, le_rfl⟩⟩
  let : IsDirected (Set.Ici c) (· ≤ ·) := ⟨by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  have transRing (j k : Set.Ici c) (h : j ≤ k) :
      (B.map (homOfLE h)).hom.comp (B.map (homOfLE j.2)).hom =
        (B.map (homOfLE k.2)).hom := by
    exact congrArg CommRingCat.Hom.hom (B.map_comp (homOfLE j.2) (homOfLE h)).symm
  have limitRing (j : Set.Ici c) :
      (κ.app j.1).hom.comp (B.map (homOfLE j.2)).hom = (κ.app c).hom := by
    exact congrArg CommRingCat.Hom.hom (κ.naturality (homOfLE j.2))
  let t (T : ModuleCat.{u} (B.obj c)) (j k : Set.Ici c) (h : j ≤ k) :
      fixedArrowStage B c T j →ₛₗ[(B.map (homOfLE h)).hom] fixedArrowStage B c T k :=
    scalarTransition _ _ _ (transRing j k h) T
  let τ (T : ModuleCat.{u} (B.obj c)) (j : Set.Ici c) :
      fixedArrowStage B c T j →ₛₗ[(κ.app j.1).hom] fixedArrowLimit B A κ c T :=
    scalarTransition _ _ _ (limitRing j) T
  have ht (T : ModuleCat.{u} (B.obj c)) (j k : Set.Ici c) (h : j ≤ k)
      (x : T) (a : B.obj j.1) :
      t T j k h (fixedArrowStageTmul B c T j x a) =
        fixedArrowStageTmul B c T k x ((B.map (homOfLE h)).hom a) :=
    scalarTransition_tmul _ _ _ _ _ _ _
  have hτ (T : ModuleCat.{u} (B.obj c)) (j : Set.Ici c) (x : T) (a : B.obj j.1) :
      τ T j (fixedArrowStageTmul B c T j x a) =
        fixedArrowLimitTmul B A κ c T x ((κ.app j.1).hom a) :=
    scalarTransition_tmul _ _ _ _ _ _ _
  have tid (T : ModuleCat.{u} (B.obj c)) (j : Set.Ici c)
      (x : fixedArrowStage B c T j) : t T j j le_rfl x = x := by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul a x =>
      change t T j j le_rfl (fixedArrowStageTmul B c T j x a) = _
      rw [ht]
      simp only [homOfLE_refl, B.map_id, CommRingCat.hom_id, RingHom.id_apply]
      rfl
    | add x y hx hy => rw [map_add, hx, hy]
  have tcomp (T : ModuleCat.{u} (B.obj c)) (j k l : Set.Ici c)
      (hjk : j ≤ k) (hkl : k ≤ l) (x : fixedArrowStage B c T j) :
      t T k l hkl (t T j k hjk x) = t T j l (hjk.trans hkl) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      change t T k l hkl (t T j k hjk (fixedArrowStageTmul B c T j x a)) =
        t T j l (hjk.trans hkl) (fixedArrowStageTmul B c T j x a)
      rw [ht, ht, ht]
      exact congrArg (fixedArrowStageTmul B c T l x)
        (ConcreteCategory.congr_hom (B.map_comp (homOfLE hjk) (homOfLE hkl)) a).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have τcomp (T : ModuleCat.{u} (B.obj c)) (j k : Set.Ici c)
      (h : j ≤ k) (x : fixedArrowStage B c T j) : τ T k (t T j k h x) = τ T j x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      change τ T k (t T j k h (fixedArrowStageTmul B c T j x a)) =
        τ T j (fixedArrowStageTmul B c T j x a)
      rw [ht, hτ, hτ]
      exact congrArg (fixedArrowLimitTmul B A κ c T x)
        (ConcreteCategory.congr_hom (κ.naturality (homOfLE h)) a)
    | add x y hx hy => simp only [map_add, hx, hy]
  have fp (T : ModuleCat.{u} (B.obj c)) [Module.FinitePresentation (B.obj c) T]
      (j : Set.Ici c) : Module.FinitePresentation (B.obj j.1) (fixedArrowStage B c T j) := by
    let := (B.map (homOfLE j.2)).hom.toAlgebra
    change Module.FinitePresentation (B.obj j.1) (TensorProduct (B.obj c) (B.obj j.1) T)
    infer_instance
  have nat (j k : Set.Ici c) (h : j ≤ k) (x : fixedArrowStage B c P j) :
      t Q j k h (fixedArrowStageArrow B c v j x) =
        fixedArrowStageArrow B c v k (t P j k h x) :=
    scalarTransition_natural _ _ _ _ v x
  have natA (j : Set.Ici c) (x : fixedArrowStage B c P j) :
      τ Q j (fixedArrowStageArrow B c v j x) =
        fixedArrowLimitArrow B A κ c v (τ P j x) :=
    scalarTransition_natural _ _ _ _ v x
  let e (T : ModuleCat.{u} (B.obj c)) (j k : Set.Ici c) (h : j ≤ k) :
      (ModuleCat.extendScalars (B.map (homOfLE h)).hom).obj (fixedArrowStage B c T j) ≅
        fixedArrowStage B c T k := scalarComparison _ _ _ (transRing j k h) T
  let eA (T : ModuleCat.{u} (B.obj c)) (j : Set.Ici c) :
      (ModuleCat.extendScalars (κ.app j.1).hom).obj (fixedArrowStage B c T j) ≅
        fixedArrowLimit B A κ c T := scalarComparison _ _ _ (limitRing j) T
  have he (T : ModuleCat.{u} (B.obj c)) (j k : Set.Ici c) (h : j ≤ k)
      (z : fixedArrowStage B c T j) (b : B.obj k.1) :
      (e T j k h).hom (b ⊗ₜ[B.obj j.1, (B.map (homOfLE h)).hom] z) =
        b • t T j k h z := scalarComparison_formula _ _ _ _ _ _ _
  have heA (T : ModuleCat.{u} (B.obj c)) (j : Set.Ici c)
      (z : fixedArrowStage B c T j) (b : A) :
      (eA T j).hom (b ⊗ₜ[B.obj j.1, (κ.app j.1).hom] z) =
        b • τ T j z := scalarComparison_formula _ _ _ _ _ _ _
  have enat (j k : Set.Ici c) (h : j ≤ k) :
      (ModuleCat.extendScalars (B.map (homOfLE h)).hom).map
          (fixedArrowStageArrow B c v j) ≫ (e Q j k h).hom =
        (e P j k h).hom ≫ fixedArrowStageArrow B c v k :=
    scalarComparison_natural _ _ _ _ v
  have enatA (j : Set.Ici c) :
      (ModuleCat.extendScalars (κ.app j.1).hom).map
          (fixedArrowStageArrow B c v j) ≫ (eA Q j).hom =
        (eA P j).hom ≫ fixedArrowLimitArrow B A κ c v :=
    scalarComparison_natural _ _ _ _ v
  let F : Set.Ici c ⥤ I :=
    { obj := Subtype.val
      map := fun h ↦ homOfLE (leOfHom h) }
  have : F.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro i
      obtain ⟨j, hij, hcj⟩ := exists_ge_ge i c
      exact ⟨⟨j, hcj⟩, ⟨homOfLE hij⟩⟩
    · intro i j a b
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  let κ' : F ⋙ B ⟶ (Functor.const (Set.Ici c)).obj A :=
    (Cocone.mk A κ).whisker F |>.ι
  have hκ' : Nonempty (IsColimit (Cocone.mk A κ')) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm hκ.some⟩
  let D (T : ModuleCat.{u} (B.obj c)) : Set.Ici c ⥤ AddCommGrpCat.{u} :=
    { obj := fun j ↦ AddCommGrpCat.of (fixedArrowStage B c T j)
      map := fun h ↦ AddCommGrpCat.ofHom (t T _ _ (leOfHom h)).toAddMonoidHom
      map_id := by
        intro j
        apply AddCommGrpCat.ext
        exact tid T j
      map_comp := by
        intro i j k h g
        apply AddCommGrpCat.ext
        intro x
        exact (tcomp T i j k (leOfHom h) (leOfHom g) x).symm }
  let δ (T : ModuleCat.{u} (B.obj c)) :
      D T ⟶ (Functor.const (Set.Ici c)).obj
        (AddCommGrpCat.of (fixedArrowLimit B A κ c T)) :=
    { app := fun j ↦ AddCommGrpCat.ofHom (τ T j).toAddMonoidHom
      naturality := by
        intro j k h
        apply AddCommGrpCat.ext
        exact τcomp T j k (leOfHom h) }
  have elem (T : ModuleCat.{u} (B.obj c)) :=
    baseChange_diagram_elementwise (F ⋙ B) A κ' hκ'
      (fixedArrowLimit B A κ c T) (D T) (δ T)
      (fun j y x ↦ (τ T j).map_smulₛₗ y x)
      (fun j k h ↦ ⟨(e T j k h).toLinearEquiv, fun y x ↦ he T j k h x y⟩)
      (fun j ↦ ⟨(eA T j).toLinearEquiv, fun y x ↦ heA T j x y⟩)
  refine ⟨t P, t Q, τ P, τ Q, ht P, hτ P, tid P, tcomp P, τcomp P, fp P,
    ht Q, hτ Q, tid Q, tcomp Q, τcomp Q, fp Q, nat, natA, ?_, ?_,
    additive_colimit (D P) _ (δ P) (elem P).1 (elem P).2, (elem P).1,
    eventual_equality (D P) _ (δ P) (elem P).2,
    additive_colimit (D Q) _ (δ Q) (elem Q).1 (elem Q).2, (elem Q).1,
    eventual_equality (D Q) _ (δ Q) (elem Q).2, inferInstance, inferInstance⟩
  · exact fun j k h ↦ ⟨e P j k h, e Q j k h, he P j k h, he Q j k h, enat j k h⟩
  · exact fun j ↦ ⟨eA P j, eA Q j, heA P j, heA Q j, enatA j⟩

end Module
