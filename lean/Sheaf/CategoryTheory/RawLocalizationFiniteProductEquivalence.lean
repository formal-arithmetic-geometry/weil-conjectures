module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Raw scalar localization of a finite product equivalence

Source: Weil conjectures blueprint, main-20261015, `def-pur-section-invariant`, final
invertibility assertion, finite-clopen transport subargument; Stacks Tags 00CV, 05G3,
02C3, 09MJ and 09MK (blueprint: lem-pur-raw-localization-finite-product-equivalence).

Tensor products are scalar-first, as in the recorded `ScalarLocalization` definition.
The product category has pointwise Hom modules. Forward linearity is expressed on
projections, and inverse linearity directly on these modules, without choosing an
additional preadditive structure on the product category.
-/

@[expose] public section

universe r u v w

open TensorProduct

namespace CategoryTheory

open Classical in
/-- Raw scalar localization preserves a finite product equivalence, including the
canonical Hom comparison, integral object representatives and the empty product.
Source: `def-pur-section-invariant`, finite-clopen coefficient transport subargument
(blueprint: lem-pur-raw-localization-finite-product-equivalence).

Proof plan, following the six steps of the node:
1. `lem-sf-quasi-inverse-hom-bijection` makes the integral Hom map bijective. Each
component is linear by `def-weil-linear-functor`; its inverse is linear by injectivity.
2. Extend the component Hom maps by `def-weil-module-base-change`. On pure tensors
identities and composition follow from functoriality and the raw composition formula
in `def-weil-linear-scalar-localization`; extend by bilinearity.
3. `lem-weil-pbc-tensor-finite-product` gives the canonical tensor/product isomorphism
(`TensorProduct.piRight` in scalar-first order). Composing it with the base change
of the integral Hom isomorphism gives the displayed Hom map and its bijectivity.
4. A quasi-inverse to the integral product functor gives integral representatives and
component isomorphisms. Tensor their arrows with one; their inverse identities persist.
5. `lem-trf-fully-faithful-ess-surj-equivalence` produces the equivalence. Its inverse
Hom maps are linear because they are inverse linear bijections followed by conjugation,
whose linearity is `def-weil-linear-category`.
6. For an empty index, the integral quasi-inverse gives an object. The integral Hom
isomorphisms identify every Hom module with the zero empty product. Its scalar extension
is zero too, so every localized Hom set is a singleton. No retracts are adjoined. -/
theorem rawLocalization_finiteProduct_equivalence
    (R : Type r) [CommRing R] (t : R)
    (A : Type u) [Category.{v} A] [Preadditive A] [Linear R A]
    (I : Type w) [Fintype I] (B : I → Type u)
    [∀ i : I, Category.{v} (B i)] [∀ i : I, Preadditive (B i)]
    [∀ i : I, Linear R (B i)]
    (F : ∀ i : I, A ⥤ B i) [∀ i : I, (F i).Additive]
    [∀ i : I, (F i).Linear R] [(Functor.pi' F).IsEquivalence] :
    ∃ E : ScalarLocalization R A t ≌ (∀ i : I, ScalarLocalization R (B i) t),
      (∀ i : I, (E.functor ⋙ Pi.eval (fun j ↦ ScalarLocalization R (B j) t) i).Additive ∧
        (E.functor ⋙ Pi.eval (fun j ↦ ScalarLocalization R (B j) t) i).Linear
          (Localization.Away t)) ∧
      (∀ (L M : ∀ i : I, ScalarLocalization R (B i) t)
          (f g : ∀ i : I, L i ⟶ M i) (a : Localization.Away t),
        E.inverse.map (f + g) = E.inverse.map f + E.inverse.map g ∧
        E.inverse.map (a • f) = a • E.inverse.map f) ∧
      (∀ (K : A) (i : I),
        E.functor.obj ⟨K⟩ i = ScalarLocalization.mk ((F i).obj K)) ∧
      (∀ (K M : A) (f : K ⟶ M) (a : Localization.Away t),
        HEq (E.functor.map (a ⊗ₜ[R] f :
          ScalarLocalization.mk (R := R) (p := t) K ⟶ ScalarLocalization.mk M))
          (fun i : I ↦ a ⊗ₜ[R] (F i).map f)) ∧
      (∀ K M : A,
        ∃ h : (K ⟶ M) ≃ₗ[R] (∀ i : I, (F i).obj K ⟶ (F i).obj M),
          (∀ f : K ⟶ M, h f = fun i : I ↦ (F i).map f) ∧
          (∀ z : Localization.Away t ⊗[R] (K ⟶ M),
            HEq (E.functor.map (z :
              ScalarLocalization.mk (R := R) (p := t) K ⟶ ScalarLocalization.mk M))
              ((TensorProduct.piRight R (Localization.Away t) (Localization.Away t)
                (fun i : I ↦ (F i).obj K ⟶ (F i).obj M))
                  (h.toLinearMap.baseChange (Localization.Away t) z)))) ∧
      (∀ L : ∀ i : I, ScalarLocalization R (B i) t,
        ∃ (K : A) (α : ∀ i : I, (F i).obj K ≅ (L i).obj)
          (β : ∀ i : I, E.functor.obj ⟨K⟩ i ≅ L i),
          ∀ i : I,
            HEq (β i).hom ((1 : Localization.Away t) ⊗ₜ[R] (α i).hom) ∧
            HEq (β i).inv ((1 : Localization.Away t) ⊗ₜ[R] (α i).inv)) ∧
      (IsEmpty I → Nonempty A ∧ (∀ K M : A, Subsingleton (K ⟶ M)) ∧
        ∀ K M : ScalarLocalization R A t, Subsingleton (K ⟶ M)) := by
  classical
  let S := Localization.Away t
  let hom (K M : A) : (K ⟶ M) ≃ₗ[R] (∀ i, (F i).obj K ⟶ (F i).obj M) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i ↦ (F i).mapLinearMap R)
      ((Functor.FullyFaithful.ofFullyFaithful (Functor.pi' F)).map_bijective K M)
  let extend (i : I) : ScalarLocalization R A t ⥤ ScalarLocalization R (B i) t :=
    { obj := fun K ↦ ⟨(F i).obj K.obj⟩
      map := fun f ↦ ((F i).mapLinearMap R).baseChange S f
      map_id := fun K ↦ by
        change ((F i).mapLinearMap R).baseChange S (1 ⊗ₜ[R] 𝟙 K.obj) =
          (1 : S) ⊗ₜ[R] 𝟙 ((F i).obj K.obj)
        simp
      map_comp := fun {K L M} f g ↦ by
        change ((F i).mapLinearMap R).baseChange S
            (ScalarLocalization.composition R A t K.obj L.obj M.obj g f) =
          ScalarLocalization.composition R (B i) t _ _ _
            (((F i).mapLinearMap R).baseChange S g)
            (((F i).mapLinearMap R).baseChange S f)
        induction g using TensorProduct.induction_on with
        | zero => simp
        | add g g' hg hg' => simp [hg, hg']
        | tmul b g =>
          induction f using TensorProduct.induction_on with
          | zero => simp
          | add f f' hf hf' => simp [hf, hf']
          | tmul a f =>
            rw [ScalarLocalization.composition_tmul]
            simp only [LinearMap.baseChange_tmul]
            change (b * a) ⊗ₜ[R] (F i).map (f ≫ g) =
              ScalarLocalization.composition R (B i) t _ _ _
                (b ⊗ₜ[R] (F i).map g) (a ⊗ₜ[R] (F i).map f)
            rw [Functor.map_comp]
            exact (ScalarLocalization.composition_tmul R (B i) t _ _ _
              ((F i).map g) ((F i).map f) b a).symm }
  have extend_add (i : I) : (extend i).Additive :=
    ⟨fun {K M f g} ↦ (((F i).mapLinearMap R).baseChange S).map_add f g⟩
  have extend_lin (i : I) : (extend i).Linear S :=
    ⟨fun {K M} f a ↦ (((F i).mapLinearMap R).baseChange S).map_smul a f⟩
  let G := Functor.pi' extend
  have comparison (K M : A) (z : S ⊗[R] (K ⟶ M)) :
      G.map (X := ⟨K⟩) (Y := ⟨M⟩) z =
        TensorProduct.piRight R S S (fun i ↦ (F i).obj K ⟶ (F i).obj M)
          ((hom K M).toLinearMap.baseChange S z) := by
    induction z using TensorProduct.induction_on with
    | zero =>
      change (fun i ↦ ((F i).mapLinearMap R).baseChange S 0) = _
      simp only [map_zero]
      rfl
    | add x y hx hy =>
      change (fun i ↦ ((F i).mapLinearMap R).baseChange S (x + y)) = _
      simp only [map_add]
      funext i
      exact congrArg₂ (· + ·) (congrFun hx i) (congrFun hy i)
    | tmul a f => rfl
  have bij (K M : ScalarLocalization R A t) :
      Function.Bijective (G.map : (K ⟶ M) → _) := by
    have h := ((hom K.obj M.obj).baseChange R S _ _ |>.trans
      (TensorProduct.piRight R S S (fun i ↦ (F i).obj K.obj ⟶ (F i).obj M.obj))).bijective
    have eqmap : (G.map : (K ⟶ M) → _) =
        (fun z ↦ TensorProduct.piRight R S S
          (fun i ↦ (F i).obj K.obj ⟶ (F i).obj M.obj)
            ((hom K.obj M.obj).toLinearMap.baseChange S z)) := by
      funext z
      exact comparison K.obj M.obj z
    rw [eqmap]
    exact h
  have : G.Faithful := ⟨fun h ↦ (bij _ _).injective h⟩
  have : G.Full := ⟨(bij _ _).surjective⟩
  have representatives (L : ∀ i, ScalarLocalization R (B i) t) :
      ∃ (K : A) (α : ∀ i, (F i).obj K ≅ (L i).obj)
        (β : ∀ i, G.obj ⟨K⟩ i ≅ L i),
        ∀ i, HEq (β i).hom ((1 : S) ⊗ₜ[R] (α i).hom) ∧
          HEq (β i).inv ((1 : S) ⊗ₜ[R] (α i).inv) := by
    let K := (Functor.pi' F).objPreimage (fun i ↦ (L i).obj)
    let α : ∀ i, (F i).obj K ≅ (L i).obj := fun i ↦
      Pi.isoApp ((Functor.pi' F).objObjPreimageIso (fun i ↦ (L i).obj)) i
    let β : ∀ i, G.obj ⟨K⟩ i ≅ L i := fun i ↦
      (ScalarLocalization.localization R (B i) t).mapIso (α i)
    exact ⟨K, α, β, fun i ↦ ⟨HEq.rfl, HEq.rfl⟩⟩
  have : G.EssSurj := ⟨fun L ↦ by
    obtain ⟨K, α, β, hβ⟩ := representatives L
    exact ⟨⟨K⟩, ⟨Pi.isoMk β⟩⟩⟩
  have : G.IsEquivalence := {}
  let E := G.asEquivalence
  let : Preadditive (∀ i, ScalarLocalization R (B i) t) :=
    { homGroup := fun L M ↦ inferInstanceAs (AddCommGroup (∀ i, L i ⟶ M i))
      add_comp := fun L M N f g h ↦ funext fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i)
      comp_add := fun L M N f g h ↦ funext fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i) }
  let : Linear S (∀ i, ScalarLocalization R (B i) t) :=
    { homModule := fun L M ↦ inferInstanceAs (Module S (∀ i, L i ⟶ M i))
      smul_comp := fun L M N a f g ↦ funext fun i ↦ Linear.smul_comp _ _ _ a (f i) (g i)
      comp_smul := fun L M N f a g ↦ funext fun i ↦ Linear.comp_smul _ _ _ (f i) a (g i) }
  have : G.Additive := ⟨fun {K M f g} ↦ funext fun i ↦ (extend_add i).map_add⟩
  have : G.Linear S := ⟨fun {K M} f a ↦ funext fun i ↦ (extend_lin i).map_smul f a⟩
  have : E.functor.Additive := inferInstanceAs G.Additive
  have : E.functor.Linear S := inferInstanceAs (G.Linear S)
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, representatives, ?_⟩
  · intro i
    exact ⟨extend_add i, extend_lin i⟩
  · intro L M f g a
    exact ⟨E.inverse.map_add, E.inverse.map_smul a f⟩
  · intro K i
    rfl
  · intro K M f a
    exact HEq.rfl
  · intro K M
    exact ⟨hom K M, fun f ↦ rfl, fun z ↦ heq_of_eq (comparison K M z)⟩
  · intro hI
    let := hI
    have hA (K M : A) : Subsingleton (K ⟶ M) :=
      ⟨fun f g ↦ (hom K M).injective (Subsingleton.elim _ _)⟩
    refine ⟨⟨(Functor.pi' F).objPreimage (fun i ↦ isEmptyElim i)⟩, hA, ?_⟩
    intro K M
    refine ⟨fun f g ↦ (bij K M).injective ?_⟩
    apply funext
    intro i
    exact isEmptyElim i

end CategoryTheory
