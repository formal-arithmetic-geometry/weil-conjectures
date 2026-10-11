/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Point.DiscreteModule
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.PointCount

/-!
# Étale sheaves on the spectrum of a field and discrete Galois modules

Let `K` be a field and `Ω` a separable closure of `K`, with absolute Galois group
`G = Gal(Ω/K)` carrying the Krull topology. The geometric point `Spec Ω ⟶ Spec K` is a point of
the small étale site of `Spec K`, and `G` acts on its fibre functor
`X ↦ Hom_K(Spec Ω, X)` by precomposition with `Spec σ`.

We show that this is a Galois point in the sense of
`CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint`: hence the geometric fibre functor is
an equivalence between abelian étale sheaves on `Spec K` and discrete `G`-modules, and
`Hⁿ(Spec K_ét, F) ≃ Hⁿ(G, F_Ω)`.

The proof goes through the étale `K`-schemes `Spec E` for finite subextensions `E` of `Ω/K`
with their canonical geometric point `x_E` (`AlgebraicGeometry.Scheme.galoisPointFiberSpec`):

* the fibre at `Spec E` is a single `G`-orbit, as every `K`-embedding `E → Ω` extends to an
  automorphism of `Ω`, and the stabiliser of `x_E` is the open subgroup `Gal(Ω/E)`;
* every element of the fibre of an étale `K`-scheme `X` comes from some `(Spec E, x_E)`, as the
  residue fields of `X` are finite over `K`.

## Main definitions and statements

- `AlgebraicGeometry.Scheme.galoisPoint`: the geometric point of `Spec K` given by `Ω`.
- `AlgebraicGeometry.Scheme.galoisPointAct`: the action of `Gal(Ω/K)` on its fibre functor.
- `AlgebraicGeometry.Scheme.isGaloisPoint_galoisPoint`: this is a Galois point.
- `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteModule`: the equivalence of categories
  between abelian étale sheaves on `Spec K` and discrete `Gal(Ω/K)`-modules.
- `AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`: `Hⁿ(Spec K_ét, F) ≃ Hⁿ(Gal(Ω/K), F_Ω)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The geometric point `Spec Ω ⟶ Spec K` given by a field extension `Ω` of `K`. -/
noncomputable def specAlgebraMap : Spec (.of Ω) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))

variable {K Ω} in
/-- The automorphism `Spec σ` of the geometric point `Spec Ω ⟶ Spec K`, for `σ ∈ Gal(Ω/K)`. -/
noncomputable def galoisOverHom (σ : Gal(Ω/K)) :
    Over.mk (specAlgebraMap K Ω) ⟶ Over.mk (specAlgebraMap K Ω) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (by
    dsimp only [specAlgebraMap, Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x)

@[simp]
lemma galoisOverHom_left (σ : Gal(Ω/K)) :
    (galoisOverHom σ).left = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) :=
  rfl

lemma galoisOverHom_one : galoisOverHom (1 : Gal(Ω/K)) = 𝟙 _ := by
  ext : 1
  exact Spec.map_id _

lemma galoisOverHom_mul (σ τ : Gal(Ω/K)) :
    galoisOverHom (σ * τ) = galoisOverHom σ ≫ galoisOverHom τ := by
  ext : 1
  simp only [galoisOverHom_left, Over.comp_left, ← Spec.map_comp]
  rfl

variable [IsSepClosed Ω]

/-- The geometric point of the small étale site of `Spec K` given by a separably closed
extension `Ω` of `K`, with fibre functor `X ↦ Hom_K(Spec Ω, X)` valued in `Type (u + 1)`. -/
noncomputable def galoisPoint : (Spec (.of K)).smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1}

lemma galoisPoint_fiber_obj (X : (Spec (.of K)).Etale) :
    (galoisPoint K Ω).fiber.obj X =
      ULift.{u + 1} (Over.mk (specAlgebraMap K Ω) ⟶ (Etale.forget _).obj X) :=
  rfl

@[simp]
lemma galoisPoint_fiber_map_down {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y)
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPoint K Ω).fiber.map f x).down = x.down ≫ (Etale.forget _).map f :=
  rfl

/-- The action of `σ ∈ Gal(Ω/K)` on the fibre functor of `galoisPoint K Ω`, by precomposition
with `Spec σ`. -/
noncomputable def galoisPointActHom (σ : Gal(Ω/K)) :
    (galoisPoint K Ω).fiber ⟶ (galoisPoint K Ω).fiber where
  app X := TypeCat.ofHom fun x ↦ ULift.up (galoisOverHom σ ≫ x.down)
  naturality X Y f := by
    ext x
    exact ULift.ext _ _ (Category.assoc _ _ _).symm

@[simp]
lemma galoisPointActHom_app_down (σ : Gal(Ω/K)) {X : (Spec (.of K)).Etale}
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPointActHom K Ω σ).app X x).down = galoisOverHom σ ≫ x.down :=
  rfl

/-- The action of `Gal(Ω/K)` on the fibre functor of `galoisPoint K Ω`. -/
noncomputable def galoisPointAct : Gal(Ω/K) →* End (galoisPoint K Ω).fiber where
  toFun := galoisPointActHom K Ω
  map_one' := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    ext x
    refine ULift.ext _ _ ?_
    change galoisOverHom 1 ≫ x.down = x.down
    rw [galoisOverHom_one, Category.id_comp]
  map_mul' σ τ := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    ext x
    refine ULift.ext _ _ ?_
    change galoisOverHom (σ * τ) ≫ x.down = galoisOverHom σ ≫ galoisOverHom τ ≫ x.down
    rw [galoisOverHom_mul, Category.assoc]

@[simp]
lemma galoisPointAct_app_down (σ : Gal(Ω/K)) {X : (Spec (.of K)).Etale}
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPointAct K Ω σ).app X x).down = galoisOverHom σ ≫ x.down :=
  rfl

/-- The fibre functor of `galoisPoint K Ω` reflects isomorphisms of abelian étale sheaves. -/
lemma isIso_of_isIso_galoisPoint_sheafFiber_map
    {F F' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ F')
    (hf : IsIso ((galoisPoint K Ω).sheafFiber.map f)) : IsIso f := by
  have h := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of K)) (ι := PUnit.{u + 1}) (Ω := fun _ ↦ Ω) (fun _ ↦ specAlgebraMap K Ω) (by
      refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨PUnit.unit, default, ?_⟩
      exact Subsingleton.elim _ _)
  refine ((h.jointlyReflectIsomorphisms AddCommGrpCat.{u + 1}).isIso_iff f).2 ?_
  rintro ⟨-, ⟨⟨⟩⟩⟩
  exact hf

variable [Algebra.IsSeparable K Ω]

section finite

variable (E : IntermediateField K Ω) [FiniteDimensional K E]

instance etale_specAlgebraMap_intermediateField : Etale (specAlgebraMap K E) :=
  have : Algebra.Etale K E := .of_finite_of_isSeparable
  HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 this)

/-- The étale `K`-scheme `Spec E` for a finite subextension `E` of `Ω / K`. -/
noncomputable abbrev etaleSpec : (Spec (.of K)).Etale :=
  Etale.mk (specAlgebraMap K E)

/-- The canonical geometric point `x_E : Spec Ω ⟶ Spec E` of `Spec E`, as an element of the
fibre of `galoisPoint K Ω`. -/
noncomputable def galoisPointFiberSpec : (galoisPoint K Ω).fiber.obj (etaleSpec K Ω E) :=
  ULift.up (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) (by
    dsimp only [specAlgebraMap, Over.mk_hom, Etale.forget_mk]
    rw [← Spec.map_comp]
    rfl))

@[simp]
lemma galoisPointFiberSpec_down_left :
    (galoisPointFiberSpec K Ω E).down.left = Spec.map (CommRingCat.ofHom (algebraMap E Ω)) :=
  rfl

variable {K Ω E} in
/-- The stabiliser of `x_E` is the fixing subgroup `Gal(Ω/E)` of `E`. -/
lemma galoisPointAct_galoisPointFiberSpec_eq_iff (σ : Gal(Ω/K)) :
    (galoisPointAct K Ω σ).app _ (galoisPointFiberSpec K Ω E) = galoisPointFiberSpec K Ω E ↔
      σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) := congrArg (fun y ↦ y.down.left) h
    rw [← Spec.map_comp, Spec.map_inj] at h'
    exact congr($(h').hom ⟨x, hx⟩)
  · intro h
    refine ULift.ext _ _ (Over.OverMorphism.ext ?_)
    change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap E Ω))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact h x.1 x.2

variable {K Ω E} in
/-- The fibre of `galoisPoint K Ω` at `Spec E` is the orbit of `x_E`: every `K`-embedding
`E → Ω` extends to an automorphism of `Ω`. -/
lemma exists_galoisPointAct_galoisPointFiberSpec_eq
    (y : (galoisPoint K Ω).fiber.obj (etaleSpec K Ω E)) :
    ∃ σ : Gal(Ω/K), (galoisPointAct K Ω σ).app _ (galoisPointFiberSpec K Ω E) = y := by
  have : IsSepClosure K Ω := ⟨‹_›, ‹_›⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, Spec.map ψ = y.down.left := ⟨_, Spec.map_preimage y.down.left⟩
  have hw : CommRingCat.ofHom (algebraMap K E) ≫ ψ = CommRingCat.ofHom (algebraMap K Ω) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ]
    exact Over.w y.down
  let φ : E →ₐ[K] Ω :=
    { ψ.hom with commutes' r := congr($(hw).hom r) }
  let τ := φ.liftNormal Ω
  let σ : Gal(Ω/K) := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  refine ⟨σ, ULift.ext _ _ (Over.OverMorphism.ext ?_)⟩
  change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E Ω)) = y.down.left
  rw [← Spec.map_comp, ← hψ]
  congr 1
  ext x
  exact (φ.liftNormal_commutes Ω x).trans rfl

end finite

end AlgebraicGeometry.Scheme
