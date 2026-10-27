# Native derived Weil tensor declarations and proof imports

## Reason

The exchange proof needs the existing native compact structure tensor comparison. Its
old import of DerivedWeilOperations led back to VerdierDual, although the tensor
construction does not use duality. Extract the tensor block verbatim into
Sheaf.Paper.DerivedWeilTensorOperations and re-export it from DerivedWeilOperations.
The four unclaimed tensor modules import this lower module. The structure
comparison explicitly imports the lower tensor module used by its public
statements, and is rebuilt in this same dependency-layer migration. Every public declaration,
attribute, binder and definition body is preserved. Targets retain the same meaning.
No module held by another group is edited. The imported declaration set of the four
lower modules no longer includes the later Verdier declarations; their direct
importers are checked against this change.

## Old

In Sheaf.Paper.DerivedWeilOperations:

```lean
namespace DerivedNativeTensorProof

universe v w

open WeilConjectures

variable {D : Type v} [Category.{w} D]

private noncomputable def isoOfHomEquiv {A B : D}
    (e : ∀ Z : D, (B ⟶ Z) ≃ (A ⟶ Z))
    (hn : ∀ (Z Z' : D) (a : B ⟶ Z) (b : Z ⟶ Z'),
      e Z' (a ≫ b) = e Z a ≫ b) : A ≅ B where
  hom := e B (𝟙 B)
  inv := (e A).symm (𝟙 A)
  hom_inv_id := by
    rw [← hn B A (𝟙 B) ((e A).symm (𝟙 A)), Category.id_comp,
      Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (e B).injective
    rw [hn A B, Equiv.apply_symm_apply, Category.id_comp]

private theorem tensor_right_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {K K' : D} (f : K ⟶ K') (L : D) :
    (@MonoidalCategory.tensorRight D _ S.monoidal L).map f =
      S.tensor.map (Prod.mkHom f (𝟙 L)) := by
  let := S.monoidal
  exact (MonoidalCategory.tensorHom_id f L).symm

private theorem tensor_left_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K : D) {L L' : D} (f : L ⟶ L') :
    (@MonoidalCategory.tensorLeft D _ S.monoidal K).map f =
      S.tensor.map (Prod.mkHom (𝟙 K) f) := by
  let := S.monoidal
  exact (MonoidalCategory.id_tensorHom K f).symm

private theorem uncurry_formula {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L M : D) (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L M).symm a =
      S.tensor.map (Prod.mkHom a (𝟙 L)) ≫ S.evaluation L M := by
  let := S.monoidal
  simp only [CoefficientClosedStructure.transpose,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id]
  rfl

private theorem uncurry_parameter {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L L' M : D) (g : L' ⟶ L)
    (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L' M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫ (S.transpose K L M).symm a := by
  rw [uncurry_formula, uncurry_formula]
  have h := S.evaluation_naturality L L' M g
  rw [tensor_right_map, tensor_left_map] at h
  change S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
      S.evaluation L' M =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op L, M))) g) ≫ S.evaluation L M at h
  change S.tensor.map (Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
    S.evaluation L' M = _
  have hc : Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') =
      Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') := by
    ext <;> simp
  rw [hc, S.tensor.map_comp, Category.assoc, h, ← Category.assoc,
    ← S.tensor.map_comp]
  have hc' : Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (𝟙 (H.obj (op L, M))) g =
      Prod.mkHom (𝟙 K) g ≫ Prod.mkHom a (𝟙 L) := by
    ext <;> simp
  rw [hc', S.tensor.map_comp, Category.assoc]

private theorem uncurry_both {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K K' L L' M : D)
    (f : K ⟶ K') (g : L ⟶ L') (a : K' ⟶ H.obj (op L', M)) :
    (S.transpose K L M).symm
        (f ≫ a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose K' L' M).symm a := by
  change ((S.adjunction L).homEquiv K M).symm
    (f ≫ (a ≫ H.map (Prod.mkHom g.op (𝟙 M)))) = _
  rw [Adjunction.homEquiv_naturality_left_symm, tensor_right_map]
  change S.tensor.map (Prod.mkHom f (𝟙 L)) ≫
    (S.transpose K' L M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) = _
  rw [uncurry_parameter, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp

private theorem modelsOfHomEquiv {K : Type*} [Category K]
    (Q : K ⥤ D) (B : K ⥤ K ⥤ K) (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (W : K → Prop)
    (e : ∀ P T : K, W T → ∀ Z : D,
      (Q.obj ((B.obj P).obj T) ⟶ Z) ≃ (Q.obj P ⟶ H.obj (op (Q.obj T), Z)))
    (hn : ∀ (P T : K) (hT : W T) (Z Z' : D)
      (a : Q.obj ((B.obj P).obj T) ⟶ Z) (b : Z ⟶ Z'),
      e P T hT Z' (a ≫ b) = e P T hT Z a ≫ H.map (Prod.mkHom (𝟙 _) b))
    (hf : ∀ (P P' T T' : K) (hT : W T) (hT' : W T')
      (f : P ⟶ P') (g : T ⟶ T') (Z : D)
      (a : Q.obj ((B.obj P').obj T') ⟶ Z),
      e P T hT Z (Q.map ((B.map f).app T ≫ (B.obj P').map g) ≫ a) =
        Q.map f ≫ e P' T' hT' Z a ≫ H.map (Prod.mkHom (Q.map g).op (𝟙 Z))) :
    ∃ i : ∀ P T : K, W P → W T →
      (S.tensor.obj (Q.obj P, Q.obj T) ≅ Q.obj ((B.obj P).obj T)),
    ∀ (P P' T T' : K) (hP : W P) (hP' : W P') (hT : W T) (hT' : W T')
      (f : P ⟶ P') (g : T ⟶ T'),
      S.tensor.map (Prod.mkHom (Q.map f) (Q.map g)) ≫ (i P' T' hP' hT').hom =
        (i P T hP hT).hom ≫ Q.map ((B.map f).app T ≫ (B.obj P').map g) := by
  let c (P T : K) (hT : W T) (Z : D) :=
    (e P T hT Z).trans (S.transpose (Q.obj P) (Q.obj T) Z).symm
  have hc (P T : K) (hT : W T) (Z Z' : D)
      (a : Q.obj ((B.obj P).obj T) ⟶ Z) (b : Z ⟶ Z') :
      c P T hT Z' (a ≫ b) = c P T hT Z a ≫ b := by
    change (S.transpose _ _ _).symm (e P T hT Z' (a ≫ b)) = _
    rw [hn]
    exact (S.adjunction (Q.obj T)).homEquiv_naturality_right_symm _ _
  let i (P T : K) (hT : W T) := isoOfHomEquiv (c P T hT) (hc P T hT)
  refine ⟨fun P T _ hT ↦ i P T hT, ?_⟩
  intro P P' T T' hP hP' hT hT' f g
  have hi := hc P T hT (Q.obj ((B.obj P).obj T)) (Q.obj ((B.obj P').obj T'))
    (𝟙 _) (Q.map ((B.map f).app T ≫ (B.obj P').map g))
  rw [Category.id_comp] at hi
  change _ = c P T hT _ (𝟙 _) ≫ _
  rw [← hi]
  change S.tensor.map (Prod.mkHom (Q.map f) (Q.map g)) ≫
    (S.transpose _ _ _).symm (e P' T' hT' _ (𝟙 _)) =
    (S.transpose _ _ _).symm (e P T hT _ _)
  rw [← Category.comp_id (Q.map ((B.map f).app T ≫ (B.obj P').map g)), hf]
  exact (uncurry_both S (Q.obj P) (Q.obj P') (Q.obj T) (Q.obj T') _
    (Q.map f) (Q.map g) _).symm

end DerivedNativeTensorProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Tensoring a map in the fixed right factor, obtained by transposing
precomposition of the existing sheaf internal Hom. This is the module tensor map.
Source: TensorHomAdjunction.lean, tensorIhomAdjunction
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def nativeTensorMap {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B) :
    tensorFunctor k₀ l X A ⟶ tensorFunctor k₀ l X B :=
  (conjugateEquiv (tensorIhomAdjunction k₀ l X B)
    (tensorIhomAdjunction k₀ l X A)).symm ((ihomBifunctor k₀ l X).map f.op)

/-- The tensor map respects identity maps.
Source: TensorHomAdjunction.lean and the identity law for conjugateEquiv
(blueprint: def-sf-derived-weil-category-and-operations).
Proof: internal-Hom precomposition sends the identity to the identity. The
conjugate of the identity under the same adjunction is the identity. -/
theorem nativeTensorMap_id (A : ProEtaleWeilSheaf k₀ l X) :
    nativeTensorMap k₀ l X (𝟙 A) = 𝟙 (tensorFunctor k₀ l X A) := by
  unfold nativeTensorMap
  change (conjugateEquiv (tensorIhomAdjunction k₀ l X A)
    (tensorIhomAdjunction k₀ l X A)).symm
      ((ihomBifunctor k₀ l X).map (𝟙 (op A))) = _
  rw [(ihomBifunctor k₀ l X).map_id]
  exact conjugateEquiv_symm_id (tensorIhomAdjunction k₀ l X A)

/-- Tensor maps respect composition.
Source: TensorHomAdjunction.lean and conjugateEquiv_symm_comp
(blueprint: def-sf-derived-weil-category-and-operations).
Proof: precomposition reverses composition. Conjugation of transformations
between right adjoints reverses composition again, giving the displayed order. -/
theorem nativeTensorMap_comp {A B C : ProEtaleWeilSheaf k₀ l X}
    (f : A ⟶ B) (g : B ⟶ C) :
    nativeTensorMap k₀ l X (f ≫ g) =
      nativeTensorMap k₀ l X f ≫ nativeTensorMap k₀ l X g := by
  unfold nativeTensorMap
  rw [op_comp, Functor.map_comp]
  exact (conjugateEquiv_symm_comp (tensorIhomAdjunction k₀ l X C)
    (tensorIhomAdjunction k₀ l X B) (tensorIhomAdjunction k₀ l X A) _ _).symm

/-- The existing relative tensor, curried with its right argument first.
Source: Dual.lean, tensor and tensorFunctor; TensorHomAdjunction.lean
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def nativeTensorBifunctor :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj := tensorFunctor k₀ l X
  map := nativeTensorMap k₀ l X
  map_id := nativeTensorMap_id k₀ l X
  map_comp := nativeTensorMap_comp k₀ l X

/-- The flipped tensor is additive in its left argument.
Source: relative module tensor, Stacks 03EK
(blueprint: def-sf-derived-weil-category-and-operations).
Proof: evaluate the natural transformations at each fixed right factor. The
resulting functor is the left adjoint in tensorIhomAdjunction. Its right adjoint,
the sheaf internal Hom, is additive, so Mathlib gives additivity of the left adjoint. -/
@[instance] theorem nativeTensorBifunctor_flip_additive :
    (nativeTensorBifunctor k₀ l X).flip.Additive := by
  constructor
  intro A B f g
  apply NatTrans.ext
  funext T
  have : (tensorFunctor k₀ l X T).Additive :=
    (tensorIhomAdjunction k₀ l X T).left_adjoint_additive
  exact (tensorFunctor k₀ l X T).map_add

/-- The flipped tensor is additive in its right argument.
Source: relative module tensor, Stacks 03EK
(blueprint: def-sf-derived-weil-category-and-operations).
Proof: the inverse mates formula uses the unit, the additive tensor functor,
and the counit. Internal-Hom precomposition preserves sums. Distribute the tensor
functor over that sum and use bilinearity of composition. -/
@[instance] theorem nativeTensorBifunctor_flip_obj_additive
    (A : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).flip.obj A).Additive := by
  constructor
  intro B C f g
  have : (tensorFunctor k₀ l X B).Additive :=
    (tensorIhomAdjunction k₀ l X B).left_adjoint_additive
  change ((nativeTensorMap k₀ l X (f + g)).app A) =
    (nativeTensorMap k₀ l X f).app A + (nativeTensorMap k₀ l X g).app A
  simp [nativeTensorMap, conjugateEquiv, mateEquiv, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- Direct-sum total tensor with left degree first and differential
`d_P tensor 1 + (-1)^p 1 tensor d_T` on the (p,q) summand.
Source: Stacks 012Z, 06YL; def-pc-tensor-complex-sheaves
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def nativeTensorTotal :
    CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
      CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
        CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ :=
  (nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex

/-- The two-sided total-tensor preservation test defining K-flatness, specialized
to the native Weil tensor. No monoidal structure on complexes is assumed.
Source: def-sfb-preserves-kflat-quasi-iso, the two quasi-isomorphism tests
(blueprint: def-sf-derived-weil-category-and-operations). -/
def NativeIsKFlat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) : Prop :=
  (∀ {Q Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (((nativeTensorTotal k₀ l X).obj P).map s)) ∧
  (∀ {Q Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (((nativeTensorTotal k₀ l X).flip.obj P).map s))

/-- A K-flat resolution is a quasi-isomorphism from a two-sided K-flat complex.
Source: Stacks 06YN, specialized to the native abelian Weil category
(blueprint: def-sf-derived-weil-category-and-operations). -/
structure NativeKFlatResolution (K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) where
  complex : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ
  isKFlat : NativeIsKFlat k₀ l X complex
  augmentation : complex ⟶ K
  quasiIso : QuasiIso augmentation

/-- A K-injective resolution in the equivariant abelian category. Mathlib's
IsKInjective means every map from an acyclic complex is null-homotopic.
Source: Stacks 070H; DerivedHom.lean
(blueprint: def-sf-derived-weil-category-and-operations). -/
structure NativeKInjectiveResolution (K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) where
  complex : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ
  isKInjective : complex.IsKInjective
  augmentation : K ⟶ complex
  quasiIso : QuasiIso augmentation

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The native closed derived tensor structure supplied by the recorded theorem.
Its tensor is determined up to the adjunction-compatible unique isomorphism by
the specified internal Hom, with the K-flat normalization in that theorem.
Source: native_closed_forgetful, steps 3--7
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def nativeDerivedClosedComparison : NativeClosedComparison k₀ l X :=
  (native_closed_forgetful k₀ l X).the project server.choose

/-- Derived relative tensor on the ambient native category, supplied by the
closed structure constructed by localization of total K-flat tensors.
Source: native_closed_forgetful, steps 3--5
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def nativeDerivedTensor :
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
        DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  (nativeDerivedClosedComparison k₀ l X).weilClosed.tensor


private noncomputable def nativeTensorParametrizedAdjunction :
    nativeTensorBifunctor k₀ l X ⊣₂ ihomBifunctor k₀ l X :=
  { adj := tensorIhomAdjunction k₀ l X
    unit_whiskerRight_map := by
      intro A B f
      apply NatTrans.ext
      funext P
      exact (unit_conjugateEquiv_symm
        (tensorIhomAdjunction k₀ l X B)
        (tensorIhomAdjunction k₀ l X A) ((ihomBifunctor k₀ l X).map f.op) P).symm }

attribute [local irreducible] nativeDerivedClosedComparison nativeTensorBifunctor ihomBifunctor

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
/-- The chosen derived tensor is the localization of the actual diagonal total
on K-flat complexes, naturally in both complexes. This records the defining
representative property, not constructible closure or a new adjunction assertion.
Source: native_closed_forgetful, its native Hom representative clause;
Stacks 0A96 and 08J9 (K-flat/K-injective tensor--Hom).
(blueprint: def-sf-derived-weil-category-and-operations).
Proof: the native tensor--Hom adjunction is parametrized by inverse mates.
The general K-flat bifunctor tensor--Hom theorem identifies maps out of the
localized total tensor with maps into the specified derived Hom. Compose this
bijection with the chosen closed adjunction to identify maps out of the chosen
derived tensor. The identity morphisms give mutually inverse comparison maps.
Naturality in the two complex variables follows from the naturality of the
Hom bijection and the closed adjunction, including evaluation in its parameter. -/
theorem nativeDerivedTensor_models :
    ∃ e : ∀ (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeIsKFlat k₀ l X P → NativeIsKFlat k₀ l X T →
      ((nativeDerivedTensor k₀ l X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj (((nativeTensorTotal k₀ l X).obj P).obj T)),
    ∀ (P P' T T' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeIsKFlat k₀ l X P) (hP' : NativeIsKFlat k₀ l X P')
      (hT : NativeIsKFlat k₀ l X T) (hT' : NativeIsKFlat k₀ l X T')
      (f : P ⟶ P') (g : T ⟶ T'),
      (nativeDerivedTensor k₀ l X).map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (e P' T' hP' hT').hom =
        (e P T hP hT).hom ≫ DerivedCategory.Q.map
          (((nativeTensorTotal k₀ l X).map f).app T ≫
            ((nativeTensorTotal k₀ l X).obj P').map g) := by
  classical
  let F := nativeTensorBifunctor k₀ l X
  let H₀ := ihomBifunctor k₀ l X
  let : F.flip.Additive := nativeTensorBifunctor_flip_additive k₀ l X
  let (A : ProEtaleWeilSheaf k₀ l X) : (F.flip.obj A).Additive :=
    nativeTensorBifunctor_flip_obj_additive k₀ l X A
  let : H₀.Additive := inferInstance
  let (A : (ProEtaleWeilSheaf k₀ l X)ᵒᵖ) : (H₀.obj A).Additive := inferInstance
  let : HasCountableProducts (ProEtaleWeilSheaf k₀ l X) := inferInstance
  let : HasCountableCoproducts (ProEtaleWeilSheaf k₀ l X) := inferInstance
  let : Abelian.HasKInjectiveResolutions (ProEtaleWeilSheaf k₀ l X) := inferInstance
  let C := nativeDerivedClosedComparison k₀ l X
  let H := C.homModels.weilHom
  let S := C.weilClosed
  let adj : F ⊣₂ H₀ := nativeTensorParametrizedAdjunction k₀ l X
  have flat : ∀ (T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeIsKFlat k₀ l X T →
        ∀ {P P' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (f : P ⟶ P'),
          QuasiIso f → QuasiIso (((nativeTensorTotal k₀ l X).flip.obj T).map f) := by
    intro T hT P P' f h
    exact hT.2 f h
  obtain ⟨e, hn, hf⟩ := kFlatBifunctorTensorHom (A := ProEtaleWeilSheaf k₀ l X)
    F (nativeTensorTotal k₀ l X) rfl H₀ adj H
    C.homModels.weilRepresentatives (NativeIsKFlat k₀ l X)
    flat
  exact DerivedNativeTensorProof.modelsOfHomEquiv DerivedCategory.Q
    (nativeTensorTotal k₀ l X) H S (NativeIsKFlat k₀ l X) e hn hf

end AlgebraicGeometry.ProEtaleWeilSheaf
```

The four lower modules publicly imported Sheaf.Paper.DerivedWeilOperations.

The following additional existing blocks of NativeOpenDerivedTensor are
relocated verbatim to bound compilation time per file. They introduce no new
statement and retain every original name, signature, field and body.

```lean
namespace CategoryTheory

/-- The unit-transpose normalization of an open tensor comparison.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorUnitNormalization {A B : Type a} [Category.{b} A] [Category.{b} B]
    (E : A ⥤ B) (R : B ⥤ A) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (adj : E ⊣ R)
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E) : Prop :=
  ∀ (M : A) (N : B), adj.homEquiv _ _ (gamma.inv.app (M, N)) =
    TA.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ rho.inv.app (E.obj M, N)

/-- The two-sided localization square for a total-complex open tensor map.
The comparison is fixed on arbitrary K-flat representatives.
Source: Stacks 0GL1, 06YN (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorRepresentativeNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hE : ∀ P, flatA P → flatB ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (total : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
      (E.mapHomologicalComplex (.up ℤ)).obj
        ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T)))
    (gamma : E.mapDerivedCategory.prod (𝟭 _) ⋙ DB ≅
      (𝟭 _).prod R.mapDerivedCategory ⋙ DA ⋙ E.mapDerivedCategory) : Prop :=
  ∀ P T (hP : flatA P) (hT : flatB T),
    gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      E.mapDerivedCategory.map
        (DA.map (Prod.mkHom (𝟙 _) (R.mapDerivedCategoryFactors.hom.app T))) ≫
      E.mapDerivedCategory.map
        (modelA P ((R.mapHomologicalComplex (.up ℤ)).obj T) hP (hR T hT)).hom ≫
      E.mapDerivedCategoryFactors.hom.app _ =
    DB.map (Prod.mkHom (E.mapDerivedCategoryFactors.hom.app P) (𝟙 _)) ≫
      (modelB ((E.mapHomologicalComplex (.up ℤ)).obj P) T (hE P hP) hT).hom ≫
        DerivedCategory.Q.map (total P T).hom

/-- Localization normalization of restriction/tensor, on arbitrary K-flat inputs.
Source: Stacks 0GL1, 06YN (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorRestrictionNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (total : ∀ P T, (R.mapHomologicalComplex (.up ℤ)).obj ((TB.obj P).obj T) ≅
      (TA.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (rho : DB ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) : Prop :=
  ∀ P T (hP : flatB P) (hT : flatB T),
    rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      DA.map (Prod.mkHom (R.mapDerivedCategoryFactors.hom.app P)
        (R.mapDerivedCategoryFactors.hom.app T)) ≫
      (modelA _ _ (hR P hP) (hR T hT)).hom =
    R.mapDerivedCategory.map (modelB P T hP hT).hom ≫
      R.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (total P T).hom

/-- Forgetting the equivariant open map gives the ordinary map under the specified
open and tensor comparisons. Both inverses are fixed by the same square.
Source: Stacks 0GL1; native closed-forgetful normalization
(blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorForgetNormalization
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A')
    (FA : A ⥤ A') (FB : B ⥤ B')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E)
    (gamma' : E'.prod (𝟭 B') ⋙ TB' ≅ (𝟭 A').prod R' ⋙ TA' ⋙ E') : Prop :=
  ∀ M N, FB.map (gamma.hom.app (M, N)) ≫
      eE.hom.app (TA.obj (M, R.obj N)) ≫ E'.map (tA.hom.app (M, R.obj N)) ≫
      E'.map (TA'.map (Prod.mkHom (𝟙 _) (eR.hom.app N))) =
    tB.hom.app (E.obj M, N) ≫ TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 _)) ≫
      gamma'.hom.app (FA.obj M, FB.obj N)

/-- Every summand of the total open map is its sheaf map. The input insertion maps
are the actual total-complex coproduct insertions, not chosen generators.
Source: Stacks 012Z, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorSummandNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (p q n : ℤ), p + q = n →
      (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (p q n : ℤ), p + q = n →
      (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n))
    (sheaf : ∀ M N, SB.obj (E.obj M, N) ≅ E.obj (SA.obj (M, R.obj N)))
    (total : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
      (E.mapHomologicalComplex (.up ℤ)).obj
        ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T))) : Prop :=
  ∀ P T (p q n : ℤ) (h : p + q = n),
    iB ((E.mapHomologicalComplex (.up ℤ)).obj P) T p q n h ≫ (total P T).hom.f n =
      (sheaf (P.X p) (T.X q)).hom ≫
        E.map (iA P ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h)

/-- A presentation of the open tensor calculation, with all functors, K-flat models,
and normalizations retained. The theorem pins every functor and representative map
to the existing native constructions, using equality rather than recomputation.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
structure OpenTensorPresentation
    (A B : Type a) [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B] where
  /-- Actual extension on sheaves. -/
  E : A ⥤ B
  /-- Actual restriction on sheaves. -/
  R : B ⥤ A
  /-- Extension is additive. -/
  [e_add : E.Additive]
  /-- Restriction is additive. -/
  [r_add : R.Additive]
  /-- Extension is exact on the left. -/
  [e_lim : PreservesFiniteLimits E]
  /-- Extension is exact on the right. -/
  [e_colim : PreservesFiniteColimits E]
  /-- Restriction is exact on the left. -/
  [r_lim : PreservesFiniteLimits R]
  /-- Restriction is exact on the right. -/
  [r_colim : PreservesFiniteColimits R]
  /-- Tensor on open sheaves, left argument first. -/
  SA : A × A ⥤ A
  /-- Tensor on ambient sheaves, left argument first. -/
  SB : B × B ⥤ B
  /-- The recorded direct-sum total tensor on the open. -/
  TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ
  /-- The recorded direct-sum total tensor on the ambient site. -/
  TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ
  /-- Derived tensor on the open. -/
  DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A
  /-- Derived tensor on the ambient site. -/
  DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B
  /-- Categorical two-sided K-flatness on the open. -/
  flatA : CochainComplex A ℤ → Prop
  /-- Categorical two-sided K-flatness on the ambient site. -/
  flatB : CochainComplex B ℤ → Prop
  /-- Preservation by extension. -/
  hE : ∀ P, flatA P → flatB ((E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Preservation by restriction. -/
  hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Chosen native K-flat model on the open. -/
  modelA : ∀ P T, flatA P → flatA T →
    (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TA.obj P).obj T))
  /-- Chosen native K-flat model on the ambient site. -/
  modelB : ∀ P T, flatB P → flatB T →
    (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TB.obj P).obj T))
  /-- Actual summand insertions on the open. -/
  iA : ∀ P T (p q n : ℤ), p + q = n →
    (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n)
  /-- Actual summand insertions on the ambient site. -/
  iB : ∀ P T (p q n : ℤ), p + q = n →
    (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n)
  /-- The normalized balanced sheaf isomorphism. -/
  sheafGamma : ∀ M N, SB.obj (E.obj M, N) ≅ E.obj (SA.obj (M, R.obj N))
  /-- Its totalization. -/
  totalGamma : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
    (E.mapHomologicalComplex (.up ℤ)).obj
      ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T))
  /-- It is termwise the fixed sheaf map. -/
  summands : OpenTensorSummandNormalization E R SA SB TA TB iA iB sheafGamma totalGamma
  /-- The canonical balanced sheaf restriction/tensor comparison. -/
  sheafRestriction : ∀ M N, R.obj (SB.obj (M, N)) ≅ SA.obj (R.obj M, R.obj N)
  /-- The totalization of the same restriction comparison. -/
  totalRestriction : ∀ P T,
    (R.mapHomologicalComplex (.up ℤ)).obj ((TB.obj P).obj T) ≅
      (TA.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Each summand is precisely the balanced sheaf restriction map. -/
  restriction_summands : ∀ P T (p q n : ℤ) (h : p + q = n),
    R.map (iB P T p q n h) ≫ (totalRestriction P T).hom.f n =
      (sheafRestriction (P.X p) (T.X q)).hom ≫
        iA ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h
  /-- The derived restriction comparison. -/
  restriction : DB ⋙ R.mapDerivedCategory ≅
    R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA
  /-- It is the localization of the specified total restriction comparison. -/
  restriction_model : OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR
    modelA modelB totalRestriction restriction
  /-- The natural ambient derived isomorphism. -/
  gamma : E.mapDerivedCategory.prod (𝟭 _) ⋙ DB ≅
    (𝟭 _).prod R.mapDerivedCategory ⋙ DA ⋙ E.mapDerivedCategory
  /-- It is the localization of the specified total comparison. -/
  model : OpenTensorRepresentativeNormalization E R TA TB DA DB flatA flatB hE hR
    modelA modelB totalGamma gamma

/-- Normalized comparison with ordinary module categories. Its tensor comparisons
are required to be the canonical ones, and its open maps are fixed by their units.
Source: Stacks 0GL1 and openTensorNormalization
(blueprint: lem-sf-native-open-derived-tensor). -/
structure OpenTensorForgetData
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A')
    (FA : A ⥤ A') (FB : B ⥤ B')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (adj' : E' ⊣ R')
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E) where
  /-- Ordinary restriction with its canonical tensor comparison. -/
  restriction : TB' ⋙ R' ≅ R'.prod R' ⋙ TA'
  /-- On forgotten inputs, restriction/tensor is the canonical native comparison
  under the fixed tensor and open comparisons. Thus it cannot be rescaled. -/
  restriction_compatibility : ∀ M N,
    FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) ≫
      TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) =
    eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
      restriction.hom.app (FB.obj M, FB.obj N)
  /-- The ordinary unit-normalized open tensor isomorphism. -/
  gamma' : E'.prod (𝟭 B') ⋙ TB' ≅ (𝟭 A').prod R' ⋙ TA' ⋙ E'
  /-- Exactly the ordinary unit transpose, including the inverse. -/
  inverse_unit : OpenTensorUnitNormalization E' R' TA' TB' adj' restriction gamma'
  /-- Equality after forgetting under the actual open and tensor comparisons. -/
  compatibility : OpenTensorForgetNormalization E R E' R' FA FB TA TB TA' TB'
    eE eR tA tB gamma gamma'

end CategoryTheory

```

```lean
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The existing termwise pullback, localized on the ambient Weil category.
Source: native framework, Category.lean (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenPull {V W : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [W.Over (Spec (CommRingCat.of k₀))] (f : V ⟶ W)
    [f.IsOver (Spec (CommRingCat.of k₀))] :=
  (upperStar k₀ l f).mapDerivedCategory

/-- The existing exact extension, localized on the ambient Weil category.
Source: Stacks 03DJ; OpenImmersion.lean
(blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenExtension {V W : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [W.Over (Spec (CommRingCat.of k₀))] (j : V ⟶ W) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :=
  (extensionByZero k₀ l j).mapDerivedCategory

/-- The canonical balanced compositor, oriented from iterated to composite pullback.
The underlying module compositor is the adjunction-determined balanced map
b tensor (c tensor t) to b j*(c) tensor t; its inverse inserts the coefficient 1.
This definition localizes that actual sheaf compositor, including its Weil action.
Source: Stacks 03D8; UpperStarComp.lean
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenPullComp {V W Y : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (j : V ⟶ W) (p : W ⟶ Y)
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))] :
    nativeOpenPull k₀ l p ⋙ nativeOpenPull k₀ l j ≅ nativeOpenPull k₀ l (j ≫ p) :=
  (Functor.mapDerivedCategoryCompIso (upperStar k₀ l p) (upperStar k₀ l j)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarCompIso k₀ l j p).symm

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The two-variable tensor, with left argument first, on Weil sheaves.
Source: diagonal tensor in the native framework
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenSheafTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf k₀ l X × ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X :=
  Functor.uncurry.obj (nativeTensorBifunctor k₀ l X).flip

/-- The left side of the ordinary sheaf open tensor comparison on native objects.
Source: Stacks 0E8I (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenSheafLeft :=
  (extensionByZero k₀ l j).prod (𝟭 _) ⋙ nativeOpenSheafTensor k₀ l Z

/-- The right side of the ordinary sheaf open tensor comparison on native objects.
Source: Stacks 0E8I (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenSheafRight :=
  (𝟭 _).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U ⋙ extensionByZero k₀ l j

/-- The left side of the ambient derived open tensor comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenDerivedLeft :=
  (nativeOpenExtension k₀ l j).prod (𝟭 _) ⋙ nativeDerivedTensor k₀ l Z

/-- The right side of the ambient derived open tensor comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenDerivedRight :=
  (𝟭 _).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U ⋙
    nativeOpenExtension k₀ l j

/-- The actual summand inclusion for the recorded left-first total tensor.
Source: Stacks 012Z and nativeTensorTotal
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenTensorInsertion (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    tensor k₀ l X (T.X q) (P.X p) ⟶
      (((nativeTensorTotal k₀ l X).obj P).obj T).X n :=
  HomologicalComplex.ιMapBifunctor P T (nativeTensorBifunctor k₀ l X).flip
    (.up ℤ) p q n h

/-- The K-flat model of the chosen native tensor, with its existing normalization.
Source: nativeDerivedTensor_models (blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenTensorModel (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T) :
    (nativeDerivedTensor k₀ l X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj (((nativeTensorTotal k₀ l X).obj P).obj T) :=
  (nativeDerivedTensor_models k₀ l X).choose P T hP hT

/-- Forgetting commutes with the actual open extension, using exact-functor factors.
Source: OpenImmersion.lean, mapOfNatIso; Stacks 015F
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenForgetExtension :
    nativeOpenExtension k₀ l j ⋙ nativeForget k₀ l Z ≅
      nativeForget k₀ l U ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (extensionByZero k₀ l j)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))).symm ≪≫
  Functor.mapDerivedCategoryNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    rfl)) ≪≫
  Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)))

/-- Forgetting commutes with the actual open pullback, with the same exact factors.
Source: Category.lean, mapOfNatIso; Stacks 015F
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenForgetPull :
    nativeOpenPull k₀ l j ⋙ nativeForget k₀ l U ≅
      nativeForget k₀ l Z ⋙
        (ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (upperStar k₀ l j)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))).symm ≪≫
  Functor.mapDerivedCategoryNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    rfl)) ≪≫
  Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (ProEtale.adicUpperStar l (Scheme.Hom.geometricFiberMap j (comp_over j _)))

end AlgebraicGeometry.ProEtaleWeilSheaf
```

## New

NativeOpenTensorPresentation holds the generic normalization records;
NativeOpenTensorOperations holds the existing concrete open operations,
representative maps and forget comparisons. NativeOpenDerivedTensor publicly
imports both and retains its original data records, compatibility assertion and
unproved native_open_derived_tensor, unchanged. This splits type checking over
three files after the local reducibility/import improvement alone remained
near the compile limit.

NativeOpenDerivedTensor additionally removes its unused public import of
Sheaf.SixFunctors.OpenTensorNormalization: its declarations use their own
normalization records. ExactDerivedAdjunction becomes a public import because
its derived adjunction occurs in public structure fields. Its unused private
imports listed in report.md are removed.
The large nativeDerivedClosedComparison is marked locally irreducible to avoid
expanding its full constructed model while checking normalization types. The
attribute is local to this file and changes no exported reducibility setting.
No declaration, definition body, instance, or theorem statement changes.


The exact block above is in Sheaf.Paper.DerivedWeilTensorOperations.
DerivedWeilOperations retains its original public imports and adds a public import
of the extracted module. Its ambientVerdierDual and verdierDualOfPreserves remain
in place unchanged. The four lower modules replace their public import of
DerivedWeilOperations with DerivedWeilTensorOperations. The structure comparison
adds a direct public import of DerivedWeilTensorOperations, used by its public
tensor statements, so the whole migrated comparison chain is rebuilt together.

## Users

Computed with tools/downstream.py on the original five changed existing Sheaf modules,
with the structure comparison and its new item consumer included below,
including textual users of the relocated tensor declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in local snapshot | Same tensor declarations; lower proof dependency; compiled in sandbox. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed in local snapshot | Same tensor declarations; lower proof dependency; compiled in sandbox. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed in local snapshot | Same tensor declarations; lower proof dependency; compiled in sandbox. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed in local snapshot | Same tensor declarations; lower proof dependency; compiled in sandbox. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed in local snapshot | Same tensor declarations; lower proof dependency; compiled in sandbox. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in local snapshot | Same declarations through re-export; unchanged consumer compiled; no adaptation. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed in local snapshot | Explicit public tensor-layer import; same declarations and bodies; rebuilt before the item. |
| Sheaf.Paper.DerivedWeilTensorOperations | new in C4 delivery | Existing tensor block relocated verbatim; no new mathematical data. |
| WeilConjectures.WeilSheaf.VerdierDual | C4 | Uses the lower comparison import and proves exchange. |
| Sheaf.Paper.NativeOpenTensorPresentation | new in C4 delivery | Existing generic records relocated verbatim; no new mathematical data. |
| Sheaf.Paper.NativeOpenTensorOperations | new in C4 delivery | Existing native operation definitions relocated verbatim; no new mathematical data. |

## Status

landed 20261027T034622-L-3666564 2026-10-27 (merge of deliver/C4/WeilConjectures.WeilSheaf.VerdierDual)
