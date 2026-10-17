/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import WeilConjectures.Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.RingTheory.EtaleAlgebraLift

/-!
# Lifting ind-étale algebras along a closed immersion

Let `A` be a ring and `C̄` an `A`-algebra. The category `N_A(C̄)` has as objects the
factorizations `A ⟶ B ⟶ C̄` with `B` étale (of finite presentation) over `A`, and as morphisms
the compatible `A`-algebra maps; its colimit

`H_A(C̄) = colim_{N_A(C̄)} B`

comes with an `A`-algebra map to `C̄` (blueprint `def-exc-ind-etale-closed-lift`). When `C̄` is an
ind-étale algebra over `A ⧸ I`, `H_A(C̄)` is an ind-étale `A`-algebra lifting `C̄`: the reduction
`H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` is an isomorphism (blueprint `lem-exc-closed-lift-reduction`). This is
the ring-theoretic input to lifting pro-étale coverings of a closed subscheme
(`lem-exc-closed-cover-extension`).

## Implementation notes

The objects of `N_A(C̄)` are taken to be the quotients `A[x₁, …, xₙ] ⧸ J` that are étale over
`A`, so that `N_A(C̄)` is a small category (`Algebra.ClosedLift.Index`); every étale algebra of
finite presentation is isomorphic to such a quotient, so this is a skeleton-like small model of
the blueprint's indexing category, with the same colimit.

The two facts about this construction that belong to the subsection
`sk-prop-sf-open-closed-triangle` of the blueprint, that `N_A(C̄)` is filtered
(`lem-exc-closed-lift-filtered`) and the reduction isomorphism (`lem-exc-closed-lift-reduction`),
are stated here for use downstream.

## Main definitions

- `Algebra.ClosedLift.Index`: the indexing category `N_A(C̄)`.
- `Algebra.ClosedLift`: the `A`-algebra `H_A(C̄)`.
- `Algebra.ClosedLift.toAlgHom`: its map `H_A(C̄) ⟶ C̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

variable (A : Type u) [CommRing A] (C : Type u) [CommRing C] [Algebra A C]

namespace ClosedLift

/-- The objects of the indexing category `N_A(C̄)` of blueprint `def-exc-ind-etale-closed-lift`:
an étale `A`-algebra, presented as a quotient `A[x₁, …, xₙ] ⧸ J`, together with an `A`-algebra
map to `C̄`. -/
structure Index where
  /-- The number of variables of the presentation. -/
  n : ℕ
  /-- The ideal of relations of the presentation. -/
  rel : Ideal (MvPolynomial (Fin n) A)
  etale : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ rel)
  /-- The map to `C̄`. -/
  toC : (MvPolynomial (Fin n) A ⧸ rel) →ₐ[A] C

variable {A C}

/-- The étale `A`-algebra underlying an object of `N_A(C̄)`. -/
abbrev Index.alg (X : Index A C) : Type u := MvPolynomial (Fin X.n) A ⧸ X.rel

instance (X : Index A C) : Algebra.Etale A X.alg := X.etale

/-- The morphisms of `N_A(C̄)`: the `A`-algebra maps compatible with the maps to `C̄`. -/
@[ext]
structure Index.Hom (X Y : Index A C) where
  /-- The underlying `A`-algebra map. -/
  hom : X.alg →ₐ[A] Y.alg
  comp_toC : Y.toC.comp hom = X.toC

noncomputable instance : SmallCategory (Index A C) where
  Hom := Index.Hom
  id X := ⟨AlgHom.id A _, rfl⟩
  comp f g := ⟨g.hom.comp f.hom, by rw [← AlgHom.comp_assoc, g.comp_toC, f.comp_toC]⟩

@[simp]
lemma Index.id_hom (X : Index A C) : Index.Hom.hom (𝟙 X) = AlgHom.id A _ := rfl

@[simp]
lemma Index.comp_hom {X Y Z : Index A C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Index.Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl

variable (A C)

/-- The diagram `N_A(C̄) ⥤ CommAlgCat A` sending a factorization `A ⟶ B ⟶ C̄` to `B`. -/
noncomputable def diagram : Index A C ⥤ CommAlgCat.{u} A where
  obj X := CommAlgCat.of A X.alg
  map f := CommAlgCat.ofHom f.hom

/-- The cocone over `ClosedLift.diagram A C` with point `C̄`, given by the maps to `C̄`. -/
noncomputable def coconeC : Cocone (diagram A C) where
  pt := CommAlgCat.of A C
  ι :=
    { app X := CommAlgCat.ofHom X.toC
      naturality X Y f := by
        ext x
        simp only [diagram, Functor.const_obj_map]
        exact DFunLike.congr_fun f.comp_toC x }

end ClosedLift

/-- Blueprint `def-exc-ind-etale-closed-lift`: for an `A`-algebra `C̄`, the `A`-algebra
`H_A(C̄) = colim_{N_A(C̄)} B`, the colimit of the étale `A`-algebras `B` with an `A`-algebra map
to `C̄`. -/
def ClosedLift : Type u :=
  (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A)

noncomputable instance : CommRing (ClosedLift A C) :=
  inferInstanceAs (CommRing (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

noncomputable instance : Algebra A (ClosedLift A C) :=
  inferInstanceAs (Algebra A (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

namespace ClosedLift

/-- The map `H_A(C̄) ⟶ C̄` of blueprint `def-exc-ind-etale-closed-lift`, induced by the maps
`B ⟶ C̄` of the objects of `N_A(C̄)`. -/
noncomputable def toAlgHom : ClosedLift A C →ₐ[A] C :=
  (colimit.desc (diagram A C) (coconeC A C)).hom

/-- The colimit presentation of `H_A(C̄)` by the étale algebras of `N_A(C̄)`. -/
noncomputable def colimitPresentation :
    ColimitPresentation (Index A C) (CommAlgCat.of A (ClosedLift A C)) where
  diag := diagram A C
  ι := (colimit.cocone (diagram A C)).ι
  isColimit := colimit.isColimit (diagram A C)

section OfEtale

variable {A C}

/-- An étale `A`-algebra `B` with an `A`-algebra map `f : B → C̄`, as an object of `N_A(C̄)`: `B`
is replaced by an isomorphic quotient of a polynomial ring (`Index.ofEtaleEquiv`). -/
noncomputable def Index.ofEtale (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (f : B →ₐ[A] C) : Index A C :=
  let h := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).1 inferInstance
  have e : (MvPolynomial (Fin h.choose) A ⧸ RingHom.ker h.choose_spec.choose) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective h.choose_spec.choose_spec
  { n := h.choose
    rel := RingHom.ker h.choose_spec.choose
    etale := Algebra.Etale.of_equiv e.symm
    toC := f.comp (Ideal.quotientKerAlgEquivOfSurjective h.choose_spec.choose_spec).toAlgHom }

/-- The identification of the algebra underlying `Index.ofEtale B f` with `B`. -/
noncomputable def Index.ofEtaleEquiv (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (f : B →ₐ[A] C) : (Index.ofEtale B f).alg ≃ₐ[A] B :=
  Ideal.quotientKerAlgEquivOfSurjective
    ((Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).1
      inferInstance).choose_spec.choose_spec

lemma Index.ofEtale_toC (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (f : B →ₐ[A] C) : (Index.ofEtale B f).toC = f.comp (Index.ofEtaleEquiv B f).toAlgHom :=
  rfl

lemma Index.ofEtale_toC_apply (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (f : B →ₐ[A] C) (x : (Index.ofEtale B f).alg) :
    (Index.ofEtale B f).toC x = f (Index.ofEtaleEquiv B f x) :=
  rfl

/-- A morphism `X ⟶ Index.ofEtale B f` of `N_A(C̄)`, given by an `A`-algebra map `X.alg → B`
compatible with the maps to `C̄`. -/
noncomputable def Index.homOfEtale {X : Index A C} (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (f : B →ₐ[A] C) (φ : X.alg →ₐ[A] B) (hφ : f.comp φ = X.toC) :
    X ⟶ Index.ofEtale B f :=
  ⟨(Index.ofEtaleEquiv B f).symm.toAlgHom.comp φ, by
    ext x
    simpa [Index.ofEtale_toC] using DFunLike.congr_fun hφ x⟩

lemma Index.homOfEtale_hom {X : Index A C} (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (f : B →ₐ[A] C) (φ : X.alg →ₐ[A] B) (hφ : f.comp φ = X.toC) :
    (Index.homOfEtale B f φ hφ).hom = (Index.ofEtaleEquiv B f).symm.toAlgHom.comp φ :=
  rfl

end OfEtale

/-- Blueprint `lem-exc-closed-lift-filtered` (subsection `sk-prop-sf-open-closed-triangle`): the
indexing category `N_A(C̄)` of `def-exc-ind-etale-closed-lift` is filtered.

The base `A` is an object. Two objects `B`, `B'` have the common successor `B ⊗_A B'`. Two
parallel arrows `f, g : B ⇉ B'` are coequalized by `B' ⧸ K B'`, where `K` is the kernel of the
multiplication `B ⊗_A B → B` and `B ⊗_A B` acts on `B'` through `(f, g)`: this is the base change
`B' ⊗_{B ⊗_A B} B` of the étale map `B ⊗_A B → B`, hence étale over `A`. -/
instance isFiltered_index : IsFiltered (Index A C) := by
  have hne : Nonempty (Index A C) :=
    ⟨Index.ofEtale A (Algebra.ofId A C)⟩
  refine { nonempty := hne, cocone_objs := ?_, cocone_maps := ?_ }
  · intro X Y
    let T := TensorProduct A X.alg Y.alg
    let φ : T →ₐ[A] C := Algebra.TensorProduct.lift X.toC Y.toC (fun _ _ ↦ .all _ _)
    refine ⟨Index.ofEtale T φ,
      Index.homOfEtale T φ Algebra.TensorProduct.includeLeft ?_,
      Index.homOfEtale T φ Algebra.TensorProduct.includeRight ?_, trivial⟩
    · exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
    · exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  · intro X Y f g
    let S := TensorProduct A X.alg X.alg
    let m : S →ₐ[A] X.alg := Algebra.TensorProduct.lmul' A
    let k : S →ₐ[A] Y.alg := Algebra.TensorProduct.lift f.hom g.hom (fun _ _ ↦ .all _ _)
    let : Algebra S Y.alg := k.toRingHom.toAlgebra
    let : Algebra S X.alg := m.toRingHom.toAlgebra
    have : IsScalarTower A S X.alg := IsScalarTower.of_algebraMap_eq fun a ↦ (m.commutes a).symm
    have : IsScalarTower A S Y.alg := IsScalarTower.of_algebraMap_eq fun a ↦ (k.commutes a).symm
    have : Algebra.Etale S X.alg := Algebra.Etale.of_restrictScalars A S X.alg
    have hm : Function.Surjective (Algebra.ofId S X.alg) := fun x ↦ ⟨x ⊗ₜ 1, by
      change Algebra.TensorProduct.lmul' A (x ⊗ₜ[A] (1 : X.alg)) = x
      simp⟩
    let K : Ideal S := RingHom.ker (Algebra.ofId S X.alg)
    have : Algebra.Etale S (S ⧸ K) :=
      Algebra.Etale.of_equiv (Ideal.quotientKerAlgEquivOfSurjective hm).symm
    let J : Ideal Y.alg := K.map (algebraMap S Y.alg)
    have : Algebra.Etale Y.alg (Y.alg ⧸ J) :=
      Algebra.Etale.of_equiv (R := Y.alg) (A := TensorProduct S Y.alg (S ⧸ K)) (B := Y.alg ⧸ J)
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Y.alg K).symm
    have : Algebra.Etale A (Y.alg ⧸ J) := Algebra.Etale.comp A Y.alg _
    have h1 : (Y.toC.comp k) = X.toC.comp m := by
      ext x
      · simpa [k, m] using DFunLike.congr_fun f.comp_toC x
      · simpa [k, m] using DFunLike.congr_fun g.comp_toC x
    have hJ : J ≤ RingHom.ker (Y.toC : Y.alg →+* C) := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      have := DFunLike.congr_fun h1 s
      simp only [AlgHom.comp_apply] at this
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      change Y.toC (k s) = 0
      rw [this]
      have hs' : m s = 0 := hs
      rw [hs', map_zero]
    let ψ : (Y.alg ⧸ J) →ₐ[A] C := Ideal.Quotient.liftₐ J Y.toC (fun y hy ↦ hJ hy)
    refine ⟨Index.ofEtale (Y.alg ⧸ J) ψ,
      Index.homOfEtale _ ψ (Ideal.Quotient.mkₐ A J) (by ext; rfl), ?_⟩
    apply Index.Hom.ext
    simp only [Index.comp_hom]
    ext x
    simp only [Index.homOfEtale, AlgHom.comp_apply]
    congr 1
    change Ideal.Quotient.mk J (f.hom x) = Ideal.Quotient.mk J (g.hom x)
    rw [Ideal.Quotient.eq]
    have : f.hom x - g.hom x = k (x ⊗ₜ 1 - 1 ⊗ₜ x) := by
      simp only [map_sub, k]
      erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      simp
    rw [this]
    refine Ideal.mem_map_of_mem _ ?_
    change m (x ⊗ₜ 1 - 1 ⊗ₜ x) = 0
    simp only [map_sub, m]
    erw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
    simp


/-- `H_A(C̄)` is ind-étale over `A`: it is the filtered colimit of the étale algebras of
`N_A(C̄)`. -/
instance indEtale : Algebra.IndEtale A (ClosedLift A C) :=
  ⟨⟨Index A C, inferInstance, inferInstance, colimitPresentation A C,
    fun X ↦ inferInstanceAs (Algebra.Etale A X.alg)⟩⟩

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- The map `H_A(C̄) ⟶ C̄` kills `I H_A(C̄)` when `C̄` is an `A ⧸ I`-algebra. -/
lemma map_le_ker_toAlgHom :
    I.map (algebraMap A (ClosedLift A C)) ≤ RingHom.ker (toAlgHom A C : ClosedLift A C →+* C) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- The reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of blueprint `def-exc-ind-etale-closed-lift`. -/
noncomputable def reduction :
    ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C)) →+* C :=
  Ideal.Quotient.lift _ (toAlgHom A C : ClosedLift A C →+* C) (map_le_ker_toAlgHom A C I)


section Lift

variable {A C}

/-- The structure map `B ⟶ H_A(C̄)` of an object `A ⟶ B ⟶ C̄` of `N_A(C̄)`. -/
noncomputable def ι (X : Index A C) : X.alg →ₐ[A] ClosedLift A C :=
  (colimit.ι (diagram A C) X).hom

lemma ι_hom {X Y : Index A C} (f : X ⟶ Y) (x : X.alg) : ι Y (f.hom x) = ι X x :=
  congrArg (fun g ↦ CommAlgCat.Hom.hom g x) (colimit.w (diagram A C) f)

@[simp]
lemma toAlgHom_ι (X : Index A C) (x : X.alg) : toAlgHom A C (ι X x) = X.toC x :=
  congrArg (fun g ↦ CommAlgCat.Hom.hom g x) (colimit.ι_desc (coconeC A C) X)

/-- Every element of `H_A(C̄)` comes from a stage of the filtered colimit. -/
lemma exists_ι_eq (x : ClosedLift A C) : ∃ (X : Index A C) (b : X.alg), ι X b = x := by
  obtain ⟨X, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat.{u} A)) (colimit.isColimit (diagram A C))) x
  exact ⟨X, b, hb⟩

/-- Blueprint `lem-exc-closed-lift-units` (subsection `sk-prop-sf-open-closed-triangle`): an element
of `H_A(C̄)` is invertible if its image in `C̄` is invertible.

Represent the element by `b` in a stage `B`; the localization `B_b`, with its map to `C̄`, is
another stage, in which `b` becomes invertible. -/
theorem isUnit_of_isUnit_toAlgHom {x : ClosedLift A C} (hx : IsUnit (toAlgHom A C x)) :
    IsUnit x := by
  obtain ⟨X, b, rfl⟩ := exists_ι_eq x
  rw [toAlgHom_ι] at hx
  let L := Localization.Away b
  have hu : ∀ y : Submonoid.powers b, IsUnit (X.toC y) := by
    rintro ⟨y, n, rfl⟩
    simpa using hx.pow n
  let g : L →ₐ[A] C := IsLocalization.liftAlgHom (M := Submonoid.powers b) hu
  have hg : g.comp (IsScalarTower.toAlgHom A X.alg L) = X.toC := by
    ext y
    simp [g, IsLocalization.liftAlgHom]
  let f := Index.homOfEtale L g (IsScalarTower.toAlgHom A X.alg L) hg
  rw [← ι_hom f, Index.homOfEtale_hom]
  exact ((IsLocalization.Away.algebraMap_isUnit b).map
    (Index.ofEtaleEquiv L g).symm).map _

end Lift

/-- The map `H_A(C̄) ⟶ C̄` is surjective when `C̄` is ind-étale over `A ⧸ I`: every étale
`A ⧸ I`-algebra lifts to an étale `A`-algebra (`Algebra.exists_etale_coefficientLift`), which is an
object of `N_A(C̄)`. -/
theorem surjective_toAlgHom [Algebra.IndEtale (A ⧸ I) C] :
    Function.Surjective (toAlgHom A C) := by
  intro c
  obtain ⟨κ, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A ⧸ I) (S := C)
  obtain ⟨i, d, hd⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat.{u} (A ⧸ I))) P.isColimit) c
  let D := P.diag.obj i
  have : Algebra.Etale (A ⧸ I) D := hP i
  obtain ⟨m, Pr, L, hL1, hL2, e, he⟩ := Algebra.exists_etale_coefficientLift I D
  let g0 : L.LiftRing →+* C :=
    (P.ι.app i).hom.toRingHom.comp (e.toRingHom.comp (Ideal.Quotient.mk _))
  have hg0 : ∀ a : A, g0 (algebraMap A L.LiftRing a) = algebraMap A C a := by
    intro a
    have h1 : L.reduction (algebraMap A L.LiftRing a) =
        algebraMap (A ⧸ I) D (Ideal.Quotient.mk I a) := by
      rw [← Ideal.Quotient.mk_algebraMap]
      simp [SquareJacobianPresentation.CoefficientLift.reduction,
        SquareJacobianPresentation.CoefficientLift.polynomialReduction, MvPolynomial.algebraMap_eq]
    change (P.ι.app i).hom (e (Ideal.Quotient.mk _ (algebraMap A L.LiftRing a))) = _
    rw [he, h1, AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C,
      Ideal.Quotient.algebraMap_eq]
    rfl
  let g : L.LiftRing →ₐ[A] C := { g0 with commutes' := hg0 }
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm d)
  refine ⟨ι (Index.ofEtale L.LiftRing g) ((Index.ofEtaleEquiv _ g).symm b), ?_⟩
  rw [toAlgHom_ι, Index.ofEtale_toC_apply, AlgEquiv.apply_symm_apply]
  change (P.ι.app i).hom (e (Ideal.Quotient.mk _ b)) = c
  rw [hb, RingEquiv.apply_symm_apply]
  exact hd

/-- An element of `H_A(C̄)` with vanishing image in `C̄` lies in `I H_A(C̄)`, for `C̄` ind-étale
over `A ⧸ I`.

Represent it by `b` in a stage `B`. The map `B ⧸ I B ⟶ C̄` factors through an étale stage `D̄` of
`C̄` killing `b`; `D̄` is étale, hence flat, over `B ⧸ I B`, so the relation `b • 1 = 0` in `D̄` is
trivial: `1 = ∑ aⱼ yⱼ` with `b aⱼ = 0` in `B ⧸ I B`. Lifting the `yⱼ` to `H_A(C̄)` gives an element
`w = ∑ aⱼ zⱼ` mapping to `1` in `C̄`, hence a unit (`isUnit_of_isUnit_toAlgHom`), and
`b w ∈ I H_A(C̄)`. -/
theorem mem_map_of_toAlgHom_eq_zero [Algebra.IndEtale (A ⧸ I) C] {x : ClosedLift A C}
    (hx : toAlgHom A C x = 0) : x ∈ I.map (algebraMap A (ClosedLift A C)) := by
  obtain ⟨X, b, rfl⟩ := exists_ι_eq x
  rw [toAlgHom_ι] at hx
  obtain ⟨κ, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A ⧸ I) (S := C)
  let J : Ideal X.alg := I.map (algebraMap A X.alg)
  let Bb := X.alg ⧸ J
  have : Algebra.Etale (A ⧸ I) Bb :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor X.alg I).symm
  have hJ : J ≤ RingHom.ker (X.toC : X.alg →+* C) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  let φ : Bb →ₐ[A ⧸ I] C :=
    (Ideal.Quotient.liftₐ J X.toC (fun y hy ↦ hJ hy)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hφ : ∀ y, φ (Ideal.Quotient.mk J y) = X.toC y := fun _ ↦ rfl
  have hfp : IsFinitelyPresentable.{u} (CommAlgCat.of (A ⧸ I) Bb) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable (A ⧸ I) _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨i, p, hp⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit P.isColimit (CommAlgCat.ofHom φ)
  have hpb : (P.ι.app i).hom (p.hom (Ideal.Quotient.mk J b)) = (P.ι.app i).hom 0 := by
    rw [map_zero]
    have := congrArg (fun g ↦ CommAlgCat.Hom.hom g (Ideal.Quotient.mk J b)) hp
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_ofHom] at this
    exact this.trans ((hφ b).trans hx)
  obtain ⟨k, f₁, f₂, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff (P.diag ⋙ forget _)
    (isColimitOfPreserves (forget (CommAlgCat.{u} (A ⧸ I))) P.isColimit)).1 hpb
  let D := P.diag.obj k
  have : Algebra.Etale (A ⧸ I) D := hP k
  let ψ : Bb →ₐ[A ⧸ I] D := (P.diag.map f₁).hom.comp p.hom
  have hψb : ψ (Ideal.Quotient.mk J b) = 0 := by
    have : (P.diag.map f₂).hom (0 : P.diag.obj i) = 0 := map_zero _
    exact hk.trans this
  have hψ : ∀ y, (P.ι.app k).hom (ψ y) = φ y := by
    intro y
    have h1 := congrArg (fun g ↦ CommAlgCat.Hom.hom g y) hp
    have h2 := congrArg (fun g ↦ CommAlgCat.Hom.hom g (p.hom y)) (P.w f₁)
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_ofHom] at h1 h2
    exact h2.trans h1
  let : Algebra Bb D := ψ.toRingHom.toAlgebra
  have : IsScalarTower (A ⧸ I) Bb D :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  have : Algebra.Etale Bb D := Algebra.Etale.of_restrictScalars (A ⧸ I) Bb D
  have hrel : ∑ _u : Unit, (Ideal.Quotient.mk J b : Bb) • (1 : D) = 0 := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one]
    exact hψb
  obtain ⟨n, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose z hz using fun j ↦ surjective_toAlgHom A C I ((P.ι.app k).hom (y j))
  choose a' ha' using fun j ↦ Ideal.Quotient.mk_surjective (a () j)
  let w : ClosedLift A C := ∑ j, ι X (a' j) * z j
  have hw : toAlgHom A C w = 1 := by
    have h1 := congrArg (P.ι.app k).hom (hy ())
    simp only [map_one, map_sum, Algebra.smul_def, map_mul] at h1
    rw [h1]
    simp only [w, map_sum, map_mul, toAlgHom_ι, hz]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← ha' j]
    congr 1
    exact ((hψ _).trans (hφ _)).symm
  have hwu : IsUnit w := isUnit_of_isUnit_toAlgHom (hw ▸ isUnit_one)
  refine (Ideal.mul_unit_mem_iff_mem _ hwu).1 ?_
  simp only [w, Finset.mul_sum, ← mul_assoc, ← map_mul]
  refine Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_right _ _ ?_
  have hj : b * a' j ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ha']
    simpa using ha j
  have := Ideal.mem_map_of_mem (ι X : X.alg →+* ClosedLift A C) hj
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

/-- Blueprint `lem-exc-closed-lift-reduction` (subsection `sk-prop-sf-open-closed-triangle`): for
an ind-étale `A ⧸ I`-algebra `C̄`, the reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of the lift
`H_A(C̄)` of `def-exc-ind-etale-closed-lift` is an isomorphism. -/
theorem bijective_reduction [Algebra.IndEtale (A ⧸ I) C] :
    Function.Bijective (reduction A C I) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_map_of_toAlgHom_eq_zero A C I hx)
  · obtain ⟨x, hx⟩ := surjective_toAlgHom A C I c
    exact ⟨Ideal.Quotient.mk _ x, hx⟩

end ClosedLift

end Algebra
