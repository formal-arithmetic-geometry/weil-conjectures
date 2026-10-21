/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import WeilConjectures.CategoryTheory.Sites.MonObj

/-!
# Coordinates of a finite subfield basis on condensed modules

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

private noncomputable def continuousAddHom
    {A B : Type} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+ B) (hf : Continuous f) :
    continuousMapRingObj.{u} A ⟶ continuousMapRingObj B :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
      { toFun s := ULift.up (⟨fun x ↦ f (s.down x), hf.comp s.down.continuous⟩ : C(S.unop, B))
        map_zero' := by apply ULift.ext; ext x; exact f.map_zero
        map_add' s t := by apply ULift.ext; ext x; exact f.map_add _ _ }
     naturality := fun _ _ _ ↦ rfl }⟩

private noncomputable abbrev abelianize :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  sheafCompose _ (forget₂ RingCat Ab)

open MonoidalCategory MonObj Functor.LaxMonoidal in
private lemma sectionwise_linear
    (R S T : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (φ : R ⟶ S) (ψ : R ⟶ T) (f : abelianize.obj S ⟶ abelianize.obj T)
    (hf : (Functor.whiskerRight φ.hom (forget₂ RingCat Ab) ▷
        (S.obj ⋙ forget₂ RingCat Ab)) ≫ μ[S.obj ⋙ forget₂ RingCat Ab] ≫ f.hom =
      (R.obj ⋙ forget₂ RingCat Ab) ◁ f.hom ≫
        (Functor.whiskerRight ψ.hom (forget₂ RingCat Ab) ▷
          (T.obj ⋙ forget₂ RingCat Ab)) ≫ μ[T.obj ⋙ forget₂ RingCat Ab]) :
    (abelianize.map φ ▷ abelianize.obj S) ≫ μ[abelianize.obj S] ≫ f =
      abelianize.obj R ◁ f ≫
        (abelianize.map ψ ▷ abelianize.obj T) ≫ μ[abelianize.obj T] := by
  let : MonObj (abelianize.obj S).obj := S.obj.monObjCompForget₂
  let : MonObj (abelianize.obj T).obj := T.obj.monObjCompForget₂
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← μ_natural_left_assoc,
    reassoc_of% (Sheaf.μ_comp_map_mul (abelianize.obj S)),
    ← μ_natural_right_assoc, ← μ_natural_left_assoc, Sheaf.μ_comp_map_mul]
  exact hf

private noncomputable abbrev coefficientMap
    {A B : Type} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) :=
  abelianize.{u}.map (continuousMapRingSheafMap φ hφ)

private lemma coefficientMap_self
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (h : Continuous (algebraMap A A)) :
    coefficientMap.{u} (algebraMap A A) h = 𝟙 _ := rfl

open MonoidalCategory MonObj Functor.LaxMonoidal in
private lemma continuousLinearAction
    (K A B : Type) [CommRing K] [Ring A] [Ring B]
    [TopologicalSpace K] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing K] [IsTopologicalRing A] [IsTopologicalRing B]
    [Algebra K A] [Algebra K B]
    (hA : Continuous (algebraMap K A)) (hB : Continuous (algebraMap K B))
    (f : A →ₗ[K] B) (hf : Continuous f) :
    (coefficientMap (algebraMap K A) hA ▷ continuousMapRingObj.{u} A) ≫ μ ≫
        continuousAddHom f.toAddMonoidHom hf =
      continuousMapRingObj K ◁ continuousAddHom f.toAddMonoidHom hf ≫
        (coefficientMap (algebraMap K B) hB ▷ continuousMapRingObj B) ≫ μ := by
  apply sectionwise_linear (continuousMapRingSheaf K) (continuousMapRingSheaf A)
    (continuousMapRingSheaf B)
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a x
  apply ULift.ext
  ext s
  change f (algebraMap K A (a.down s) * x.down s) =
    algebraMap K B (a.down s) * f (x.down s)
  simpa only [Algebra.smul_def] using f.map_smul (a.down s) (x.down s)

private lemma module_sum_app
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R}
    {I : Type*} (s : Finset I) (f : I → (M ⟶ N))
    (S : Profinite.{u}ᵒᵖ) (a : M.X.obj.obj S) :
    (∑ i ∈ s, f i).hom.hom.app S a = ∑ i ∈ s, (f i).hom.hom.app S a :=
  map_sum
    ({ toFun := fun f ↦ f.hom.hom.app S a
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : (M ⟶ N) →+ N.X.obj.obj S) f s

private lemma sum_down_apply
    {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    {S : Profinite.{u}} {I : Type*} (s : Finset I)
    (f : I → ULift.{u + 1} C(S, A)) (x : S) :
    (∑ i ∈ s, f i).down x = ∑ i ∈ s, (f i).down x :=
  map_sum
    ({ toFun := fun f ↦ f.down x
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : ULift.{u + 1} C(S, A) →+ A) f s

/-- A finite field basis gives a coordinate homeomorphism and inverse internal condensed
module maps, with the prescribed formulas on every profinite set. The compatible algebra
structure expresses the inclusion of the two subfields in the fixed algebraic closure.
Finite biproduct projections identify the chosen finite free object's sections with tuples;
the sum of its injections represents a tuple in that object.

Source: blueprint main-20261015, lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).

Proof:
1. Over the complete nontrivially normed field Q_ell, F is finite dimensional and Hausdorff.
Each E-linear coordinate is Q_ell-linear, so
`lem-sfb-finite-dimensional-linear-map-continuous` makes it continuous. Their product is
continuous. This uses the induced topologies of `sk-def-sfb-condensed-ring`.
2. The inverse sends a tuple to the finite sum of basis vectors times its coordinates.
The subfield inclusion and multiplication are continuous. The basis identities show both
composites are identities, giving the displayed homeomorphism.
3. On continuous functions, postcompose with these coordinates and use the same finite
sum for the inverse. Both operations commute with precomposition along maps of profinite
sets and are additive. Thus they are inverse morphisms of abelian sheaves.
4. The actions are pointwise multiplication, componentwise on tuples. The ordinary tensor
universal property and `def-weil-pbc-sheafification` descend these actions to the sheafified
tensor of `sk-def-sfb-sheaf-tensor`; its strong monoidality gives the module axioms of
`sk-def-sfb-module-objects`. These are the existing regular and restricted regular modules.
5. E-linearity of the coordinates and of the basis sum makes both maps action-compatible
on pure tensors. Additivity and uniqueness of sheafification extend this compatibility to
the sheaf tensors. The sectionwise inverse identities then give the internal module iso.
-/
theorem exists_condensedSubfieldBasisIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    [Algebra E F] [IsScalarTower E F (PadicAlgCl ℓ)]
    (n : ℕ) (b : Module.Basis (Fin n) E F) :
    ∃ c : F ≃ₜ (Fin n → E),
      (∀ (s : F) (i : Fin n), c s i = b.coord i s) ∧
      (∀ a : Fin n → E, c.symm a = ∑ i, algebraMap E F (a i) * b i) ∧
      ∃ (hι : Continuous (algebraMap E F))
        (e : (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (continuousMapRingSheafMap (algebraMap E F) hι))).obj
              (Mod.regular (continuousMapRingObj F)) ≅
                Mod.finiteFree (continuousMapRingObj E) n),
        (∀ (S : Profinite.{u}) (i : Fin n) (f : C(S, F)) (x : S),
          (((e.hom ≫ biproduct.π (fun _ : Fin n ↦
            Mod.regular (continuousMapRingObj E)) i).hom.hom.app (op S)
              (ULift.up f)).down x) = b.coord i (f x)) ∧
        (∀ (S : Profinite.{u}) (f : Fin n → C(S, E)) (x : S),
          ((e.inv.hom.hom.app (op S)
            (∑ i, (biproduct.ι (fun _ : Fin n ↦
              Mod.regular (continuousMapRingObj E)) i).hom.hom.app (op S)
                (ULift.up (f i)))).down x) =
                  ∑ i, algebraMap E F (f i x) * b i) := by
  classical
  have hι : Continuous (algebraMap E F) := by
    apply continuous_induced_rng.mpr
    change Continuous ((algebraMap F (PadicAlgCl ℓ)) ∘ algebraMap E F)
    convert (continuous_subtype_val : Continuous (algebraMap E (PadicAlgCl ℓ))) using 1
    ext a
    exact (IsScalarTower.algebraMap_apply E F (PadicAlgCl ℓ) a).symm
  have : IsScalarTower ℚ_[ℓ] E F := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply (algebraMap F (PadicAlgCl ℓ)).injective
    simp only [← IsScalarTower.algebraMap_apply]
  have hc (i : Fin n) : Continuous (b.coord i) :=
    (b.coord i |>.restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  let c : F ≃ₜ (Fin n → E) :=
    { b.equivFun with
      continuous_toFun := continuous_pi hc
      continuous_invFun := by
        change Continuous b.equivFun.symm
        have heq : (b.equivFun.symm : (Fin n → E) → F) =
            fun a ↦ ∑ i, algebraMap E F (a i) * b i := by
          funext a
          simpa only [Algebra.smul_def] using b.equivFun_symm_apply a
        rw [heq]
        exact continuous_finsetSum _ fun i _ ↦
          (hι.comp (continuous_apply i)).mul continuous_const }
  let φ := coefficientMap.{u} (algebraMap E F) hι
  let M := (Mod.comap φ).obj (Mod.regular (continuousMapRingObj F))
  let R := Mod.regular (continuousMapRingObj.{u} E)
  let q (i : Fin n) : M ⟶ R :=
    Mod.homMk (continuousAddHom (b.coord i).toAddMonoidHom (hc i)) (by
      change (MonoidalCategory.whiskerRight φ (continuousMapRingObj F) ≫
        (MonObj.mul (X := continuousMapRingObj F))) ≫ _ =
          _ ≫ (MonObj.mul (X := continuousMapRingObj E))
      simpa only [coefficientMap_self, MonoidalCategory.id_whiskerRight, Category.id_comp,
        Category.assoc] using
        continuousLinearAction E F E hι continuous_id (b.coord i) (hc i))
  have hv (i : Fin n) : Continuous (LinearMap.toSpanSingleton E F (b i)) := by
    have heq : (LinearMap.toSpanSingleton E F (b i) : E → F) =
        fun a ↦ algebraMap E F a * b i := by
      funext a
      exact Algebra.smul_def a (b i)
    rw [heq]
    exact hι.mul continuous_const
  let v (i : Fin n) : R ⟶ M :=
    Mod.homMk (continuousAddHom (LinearMap.toSpanSingleton E F (b i)).toAddMonoidHom
      (hv i)) (by
      change (MonObj.mul (X := continuousMapRingObj E)) ≫ _ =
        _ ≫ MonoidalCategory.whiskerRight φ (continuousMapRingObj F) ≫
          (MonObj.mul (X := continuousMapRingObj F))
      simpa only [coefficientMap_self, MonoidalCategory.id_whiskerRight, Category.id_comp,
        Category.assoc] using
        continuousLinearAction E E F continuous_id hι
          (LinearMap.toSpanSingleton E F (b i)) (hv i))
  let e : M ≅ Mod.finiteFree (continuousMapRingObj E) n :=
    { hom := biproduct.lift q
      inv := biproduct.desc v
      hom_inv_id := by
        rw [biproduct.lift_desc]
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        ext S a
        rw [module_sum_app]
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        rw [sum_down_apply]
        change (∑ i, b.coord i (a.down x) • b i) = a.down x
        exact b.sum_repr (a.down x)
      inv_hom_id := by
        apply biproduct.hom_ext'
        intro i
        apply biproduct.hom_ext
        intro j
        simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π,
          Category.id_comp]
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        ext S a
        by_cases h : i = j
        · subst j
          simp only [biproduct.ι_π_self]
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change b.coord i (a.down x • b i) = a.down x
          simp
        · simp only [biproduct.ι_π_ne _ h]
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change b.coord j (a.down x • b i) = 0
          simp [h] }
  refine ⟨c, (fun s i ↦ rfl), ?_, hι, e, ?_, ?_⟩
  · intro a
    change b.equivFun.symm a = _
    simpa only [Algebra.smul_def] using b.equivFun_symm_apply a
  · intro S i f x
    change (((biproduct.lift q ≫ biproduct.π (fun _ : Fin n ↦ R) i).hom.hom.app
      (op S) (ULift.up f)).down x) = _
    rw [biproduct.lift_π]
    rfl
  · intro S f x
    change (((biproduct.desc v).hom.hom.app (op S)
      (∑ i, (biproduct.ι (fun _ : Fin n ↦ R) i).hom.hom.app (op S)
        (ULift.up (f i)))).down x) = _
    have hval (i : Fin n) :
        (biproduct.desc v).hom.hom.app (op S)
          ((biproduct.ι (fun _ : Fin n ↦ R) i).hom.hom.app (op S) (ULift.up (f i))) =
            (v i).hom.hom.app (op S) (ULift.up (f i)) := by
      change ((biproduct.ι (fun _ : Fin n ↦ R) i ≫ biproduct.desc v).hom.hom.app
        (op S) (ULift.up (f i))) = _
      rw [biproduct.ι_desc]
    rw [map_sum, sum_down_apply]
    simp_rw [hval]
    change (∑ i, f i x • b i) = _
    simp only [Algebra.smul_def]

end Profinite
