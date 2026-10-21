/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Finite free coordinates for internal scalar extension

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

The formulas are equalities of morphisms involving the canonical coequalizer projection.
They consequently specify the formulas on local elementary tensors without identifying
sections of a tensor sheaf with objectwise tensors. Finite products represent the finite
powers and, in an additive category, also the finite direct sums.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- The finite-free coordinate assertion, including existence of the coequalizers and
preservation properties needed to form scalar extension. The quantification over their
instances merely allows the statement to use these consequences; it is independent of
proof choices. The finite-power functor is the constant-diagram functor followed by limit.
The chosen free module and its basis inclusions use `Mod.finiteFree` and `biproduct.ι`.

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).
-/
def FiniteFreeScalarCoordinates
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  HasCoequalizers H ∧
  (∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
    PreservesColimitsOfSize.{0, 0} (tensorRight X)) ∧
  ∀ [MonoidalPreadditive H] [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (R B : H) [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (φ : R ⟶ B) [IsMonHom φ] (n : ℕ)
    (θ : finiteFree R n ≅ (comap φ).obj (regular B)),
    ∃ Φ : extendScalars φ ⋙ comap φ ≅
        Functor.const (Discrete (Fin n)) ⋙ lim,
      ∀ M : Mod H R,
        (∀ i : Fin n,
          extendπ φ M ≫ (Φ.hom.app M).hom ≫
              (Pi.π (fun _ : Fin n ↦ M) i).hom =
            (θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i).hom ▷ M.X ≫ γ[R,M.X]) ∧
        (Φ.inv.app M).hom =
          ∑ i : Fin n,
            (Pi.π (fun _ : Fin n ↦ M) i).hom ≫ (λ_ M.X).inv ≫
              (η[R] ≫ (biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ θ.hom).hom) ▷ M.X ≫
              extendπ φ M

section Coordinates

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R B : H} [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
  (φ : R ⟶ B) [IsMonHom φ]

omit [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [MonObj R] [IsCommMonObj R] [IsMonHom φ] in
private lemma scalar_right_action :
    (β_ B R).hom ≫ φ ▷ B ≫ μ[B] = B ◁ φ ≫ μ[B] := by
  rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]

private noncomputable def scalarTensorIso (M : Mod H R) :
    (comap φ).obj (extendScalarsObj φ M) ≅ (comap φ).obj (regular B) ⊗ M := by
  let N := (comap φ).obj (regular B)
  have h : ((β_ B R).hom ≫ γ[R,N.X]) = B ◁ φ ≫ μ[B] :=
    scalar_right_action φ
  let f : (extendScalarsObj φ M).X ⟶ (N ⊗ M).X :=
    extendDescHom φ (tensorObjπ N M) (by
      rw [← h]
      exact tensorObjπ_condition N M)
  let g : (N ⊗ M).X ⟶ (extendScalarsObj φ M).X :=
    coequalizer.desc (extendπ φ M) (by
      change ((β_ B R).hom ≫ γ[R,N.X]) ▷ M.X ≫ extendπ φ M = _
      rw [h]
      exact extendπ_condition φ M)
  have hf : extendπ φ M ≫ f = tensorObjπ N M :=
    extendπ_extendDescHom φ _ _
  have hg : tensorObjπ N M ≫ g = extendπ φ M := coequalizer.π_desc _ _
  let e : (extendScalarsObj φ M).X ≅ (N ⊗ M).X :=
    { hom := f
      inv := g
      hom_inv_id := by
        rw [← cancel_epi (extendπ φ M)]
        simp only [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        rw [← cancel_epi (tensorObjπ N M)]
        simp only [← Category.assoc, hg, hf, Category.comp_id] }
  refine isoMk (M := (comap φ).obj (extendScalarsObj φ M)) (N := N ⊗ M) e ?_
  change (φ ▷ _ ≫ γ[B,(extendScalarsObj φ M).X]) ≫ f = R ◁ f ≫ γ[R,(N ⊗ M).X]
  simp only [Category.assoc]
  rw [← cancel_epi (R ◁ extendπ φ M)]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
    ← whiskerLeft_comp_assoc, hf, whiskerLeft_tensorπ_smul]
  erw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]
  rfl

omit [Abelian H] [MonoidalPreadditive H] in
private lemma scalarTensorIso_hom (M : Mod H R) :
    extendπ φ M ≫ (scalarTensorIso φ M).hom.hom =
      tensorObjπ ((comap φ).obj (regular B)) M := by
  dsimp only [scalarTensorIso]
  exact extendπ_extendDescHom φ _ _

omit [Abelian H] [MonoidalPreadditive H] in
private lemma scalarTensorIso_inv (M : Mod H R) :
    tensorObjπ ((comap φ).obj (regular B)) M ≫ (scalarTensorIso φ M).inv.hom =
      extendπ φ M := by
  dsimp only [scalarTensorIso]
  exact coequalizer.π_desc _ _

omit [Abelian H] [MonoidalPreadditive H] in
private lemma tensorUnit_hom (M : Mod H R) :
    tensorObjπ (regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X] := by
  change tensorObjπ (regular R) M ≫
    (Bimod.whiskerRight (toBimodRegularIso (R := R)).hom ((toBimod R).obj M)).hom ≫
      Bimod.LeftUnitorBimod.hom ((toBimod R).obj M) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

omit [Abelian H] [MonoidalPreadditive H] in
private lemma tensorUnit_inv (M : Mod H R) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[R] ▷ M.X ≫ tensorObjπ (regular R) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [Category.assoc, Category.assoc, tensorUnit_hom, ModObj.one_smul_self,
    Iso.inv_hom_id]
  exact congrArg Hom.hom (λ_ M).inv_hom_id

omit [Abelian H] [MonoidalPreadditive H] in
private lemma scalarTensorIso_naturality {M N : Mod H R} (f : M ⟶ N) :
    (comap φ).map ((extendScalars φ).map f) ≫ (scalarTensorIso φ N).hom =
      (scalarTensorIso φ M).hom ≫ ((comap φ).obj (regular B) ◁ f) := by
  apply hom_ext
  rw [← cancel_epi (extendπ φ M)]
  change extendπ φ M ≫ (extendScalarsMap φ f).hom ≫ (scalarTensorIso φ N).hom.hom =
    extendπ φ M ≫ (scalarTensorIso φ M).hom.hom ≫ _
  rw [extendπ_extendScalarsMap_assoc, scalarTensorIso_hom,
    ← Category.assoc, scalarTensorIso_hom, tensorObjπ_whiskerLeft]
  rfl

variable {φ} {n : ℕ} (θ : finiteFree R n ≅ (comap φ).obj (regular B))

private noncomputable def finiteCoordinateIso (M : Mod H R) :
    (comap φ).obj (extendScalarsObj φ M) ≅ ∏ᶜ (fun _ : Fin n ↦ M) :=
  scalarTensorIso φ M ≪≫ whiskerRightIso θ.symm M ≪≫
    rightDistributor (fun _ : Fin n ↦ regular R) M ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ λ_ M) ≪≫ biproduct.isoProduct _

private lemma finiteCoordinateIso_π (M : Mod H R) (i : Fin n) :
    (finiteCoordinateIso θ M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i =
      (scalarTensorIso φ M).hom ≫
        ((θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i) ▷ M) ≫ (λ_ M).hom := by
  simp [finiteCoordinateIso, biproduct.isoProduct_hom, comp_whiskerRight, Category.assoc]

private lemma finiteCoordinateIso_inv (M : Mod H R) :
    (finiteCoordinateIso θ M).inv =
      ∑ i : Fin n, Pi.π (fun _ : Fin n ↦ M) i ≫ (λ_ M).inv ≫
        ((biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ θ.hom) ▷ M) ≫
          (scalarTensorIso φ M).inv := by
  classical
  simp [finiteCoordinateIso, rightDistributor_inv, Preadditive.comp_sum,
    Preadditive.sum_comp, biproduct.isoProduct_inv, comp_whiskerRight, Category.assoc]

private lemma finiteCoordinateIso_naturality {M N : Mod H R} (f : M ⟶ N) :
    (comap φ).map ((extendScalars φ).map f) ≫ (finiteCoordinateIso θ N).hom =
      (finiteCoordinateIso θ M).hom ≫
        (Functor.const (Discrete (Fin n)) ⋙ lim).map f := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, finiteCoordinateIso_π]
  have hp : (Functor.const (Discrete (Fin n)) ⋙ lim).map f ≫
      Pi.π (fun _ : Fin n ↦ N) i = Pi.π (fun _ : Fin n ↦ M) i ≫ f :=
    limMap_π ((Functor.const (Discrete (Fin n))).map f) ⟨i⟩
  rw [hp]
  rw [← Category.assoc (finiteCoordinateIso θ M).hom (Pi.π _ i) f,
    finiteCoordinateIso_π]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality]
  erw [← whisker_exchange_assoc]
  rw [← Category.assoc, scalarTensorIso_naturality]
  simp only [Category.assoc]

end Coordinates

/-- A chosen finite free basis of a commutative ring sheaf gives a natural coordinate
isomorphism `Res (B ⊗_R -) ≅ (-)^n`, with both specified local formulas.

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

Proof:
1. Put `e_i = θ ι_i` and `q_i = π_i θ⁻¹`. The inverse identities give
`q_i e_j = δ_ij` and `∑ e_i q_i = id`. Set `b_i = e_i(1)`. These maps commute with
restrictions, and linearity gives `e_i(r) = φ(r)b_i`. Finite powers have the componentwise
module action and sheaf gluing, as realized by the module-category finite product.
2. The bilinear rule `(s,m) ↦ q_i(s)m` induces a map from the sheafified tensor by
`sk-def-sfb-sheaf-tensor`. It equalizes the two relative-tensor arrows since
`q_i(s φ(r))m = q_i(s)(rm)`. The coequalizer of `sk-def-sfb-change-of-scalars` gives the
coordinate map. It is R-linear; assemble the coordinates into `Φ_M`.
3. Tensor the map `η_R ≫ e_i` with M after the inverse left unitor, then compose with
`extendπ`. This sends m to `b_i ⊗ m` and is R-linear by balancing and commutativity.
Sum these maps after the projections to obtain the displayed inverse tuple formula.
4. The i-th coordinate of the first composite is `∑ q_i(b_j)m_j = m_i`, so it is the
identity on each test object, hence as a module-sheaf morphism.
5. Precompose the other composite with `extendπ`. Balancing gives
`∑ b_i ⊗ q_i(s)m = ∑ b_i φ(q_i(s)) ⊗ m = s ⊗ m`.
The objectwise bilinear universal property, sheafification and coequalizer uniqueness
then give equality of sheaf morphisms, without a sectionwise tensor assertion.
6. For an R-linear f, `q_i(s)f(m) = f(q_i(s)m)` proves naturality by the same universal
properties; the inverse is natural as well. At n = 0 the basis identity is `id_B = 0`
and both sides are zero, so the empty-sum formulas apply. The sheaf tensor dependency
supplies the coequalizers and tensor-colimit preservation used in the assertion.
-/
theorem sheaf_finiteFreeScalarCoordinates
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @FiniteFreeScalarCoordinates (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  let t := sfbSheafTensorStructure (A := Ab.{w}) J
  let : MonoidalCategory (Sheaf J Ab.{w}) := t.monoidal
  let : SymmetricCategory (Sheaf J Ab.{w}) := t.symmetric
  let : HasSheafify J Ab.{w} := hasSheafifyEssentiallySmallSite J Ab.{w}
  let : Abelian (Sheaf J Ab.{w}) := sheafIsAbelian
  obtain ⟨_, ⟨closed⟩, props⟩ := sfbSheafTensor_properties (A := Ab.{w}) J
  let : MonoidalClosed (Sheaf J Ab.{w}) := closed
  refine ⟨⟨sfbSheafTensor_monoidalPreadditive⟩, inferInstance,
    (fun X ↦ ⟨(props X).1, (props X).2.1⟩), ?_⟩
  intro _ _ _ _ R B _ _ _ _ φ _ n θ
  refine ⟨NatIso.ofComponents (finiteCoordinateIso θ)
    (fun f ↦ finiteCoordinateIso_naturality θ f), ?_⟩
  intro M
  constructor
  · intro i
    change extendπ φ M ≫
      (((finiteCoordinateIso θ M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i).hom) = _
    rw [finiteCoordinateIso_π]
    simp only [comp_hom']
    rw [← Category.assoc, scalarTensorIso_hom, tensorObjπ_whiskerRight_assoc,
      tensorUnit_hom]
    rfl
  · change (finiteCoordinateIso θ M).inv.hom = _
    rw [finiteCoordinateIso_inv]
    change (forget R).map (∑ i : Fin n, _) = _
    rw [Functor.map_sum]
    simp only [forget_map, comp_hom']
    apply Finset.sum_congr rfl
    intro i _
    rw [tensorUnit_inv]
    simp only [Category.assoc]
    rw [tensorObjπ_whiskerRight_assoc, scalarTensorIso_inv]
    simp only [comp_hom', comp_whiskerRight, Category.assoc]

end CategoryTheory.Mod
