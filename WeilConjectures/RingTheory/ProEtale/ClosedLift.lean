/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.Mathlib.RingTheory.Unramified.Basic
public import WeilConjectures.RingTheory.ProEtale.EtaleLift

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
finite presentation is isomorphic to such a quotient (`Algebra.ClosedLift.Index.ofEtale`), so
this is a skeleton-like small model of the blueprint's indexing category, with the same colimit.

The injectivity of the reduction is proved by lifting, rather than by the flatness argument of
the blueprint: an element `b` of a stage `B` vanishing in `C̄` already vanishes in an étale
`B ⧸ IB`-algebra `C̄'` mapping to `C̄`; lifting `C̄'` to an étale `B`-algebra `B'` with
`B' ⧸ IB' ≅ C̄'` (`Algebra.Etale.exists_lift`) shows that `b ∈ IB'`.

## Main definitions and results

- `Algebra.ClosedLift.Index`: the indexing category `N_A(C̄)`.
- `Algebra.ClosedLift`: the `A`-algebra `H_A(C̄)`.
- `Algebra.ClosedLift.toAlgHom`: its map `H_A(C̄) ⟶ C̄`.
- `Algebra.ClosedLift.isFiltered_index`: `N_A(C̄)` is filtered (`lem-exc-closed-lift-filtered`).
- `Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom`: units of `H_A(C̄)`
  (`lem-exc-closed-lift-units`).
- `Algebra.ClosedLift.bijective_reduction`: the reduction isomorphism
  (`lem-exc-closed-lift-reduction`).
- `Algebra.ClosedLift.homEquiv`: `Hom_A(D, H_A(C̄)) ≃ Hom_{A/I}(D ⧸ ID, C̄)` for ind-étale `D`
  (`lem-exc-closed-lift-adjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

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

namespace Index

section presentation

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]

/-- The number of variables of a chosen presentation of a finitely presented algebra. -/
noncomputable def presN : ℕ := (Algebra.FinitePresentation.out (R := A) (A := B)).choose

/-- A chosen surjection from a polynomial ring onto a finitely presented algebra. -/
noncomputable def presMap : MvPolynomial (Fin (presN A B)) A →ₐ[A] B :=
  (Algebra.FinitePresentation.out (R := A) (A := B)).choose_spec.choose

lemma presMap_surjective : Function.Surjective (presMap A B) :=
  (Algebra.FinitePresentation.out (R := A) (A := B)).choose_spec.choose_spec.1

/-- The isomorphism of `B` with the quotient of a polynomial ring given by `presMap A B`. -/
noncomputable def presEquiv :
    (MvPolynomial (Fin (presN A B)) A ⧸ RingHom.ker (presMap A B)) ≃ₐ[A] B :=
  Ideal.quotientKerAlgEquivOfSurjective (presMap_surjective A B)

end presentation

section ofEtale

variable (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B] (g : B →ₐ[A] C)

/-- An étale `A`-algebra `B` with an `A`-algebra map `g : B → C`, transported to an object of
the small model `Index A C`. -/
noncomputable def ofEtale : Index A C where
  n := presN A B
  rel := RingHom.ker (presMap A B)
  etale := Algebra.Etale.of_equiv (presEquiv A B).symm
  toC := g.comp (presEquiv A B).toAlgHom

/-- The isomorphism of the underlying algebra of `ofEtale B g` with `B`. -/
noncomputable def ofEtaleEquiv : (ofEtale B g).alg ≃ₐ[A] B := presEquiv A B

lemma ofEtale_toC : (ofEtale B g).toC = g.comp (ofEtaleEquiv B g).toAlgHom := rfl

variable {B g}

/-- A morphism to `ofEtale B g`, given by a compatible algebra map to `B`. -/
noncomputable def toOfEtale {X : Index A C} (φ : X.alg →ₐ[A] B) (hφ : g.comp φ = X.toC) :
    X ⟶ ofEtale B g :=
  ⟨((ofEtaleEquiv B g).symm : B →ₐ[A] (ofEtale B g).alg).comp φ, by
    rw [ofEtale_toC, ← hφ]
    ext x
    simp⟩

lemma toOfEtale_hom {X : Index A C} (φ : X.alg →ₐ[A] B) (hφ : g.comp φ = X.toC) :
    (toOfEtale φ hφ).hom = ((ofEtaleEquiv B g).symm : B →ₐ[A] (ofEtale B g).alg).comp φ :=
  rfl

/-- A morphism from `ofEtale B g`, given by a compatible algebra map from `B`. -/
noncomputable def fromOfEtale {Y : Index A C} (ψ : B →ₐ[A] Y.alg) (hψ : Y.toC.comp ψ = g) :
    ofEtale B g ⟶ Y :=
  ⟨ψ.comp (ofEtaleEquiv B g).toAlgHom, by rw [← AlgHom.comp_assoc, hψ, ofEtale_toC]⟩

end ofEtale

end Index

open Index

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

open Index

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

/-- Blueprint `lem-exc-closed-lift-filtered` (subsection `sk-prop-sf-open-closed-triangle`): the
indexing category `N_A(C̄)` of `def-exc-ind-etale-closed-lift` is filtered. -/
instance isFiltered_index : IsFiltered (Index A C) where
  nonempty := ⟨ofEtale A (Algebra.ofId A C)⟩
  cocone_objs X Y := by
    have : Algebra.Etale A (X.alg ⊗[A] Y.alg) := Algebra.Etale.comp A X.alg _
    let g : X.alg ⊗[A] Y.alg →ₐ[A] C :=
      Algebra.TensorProduct.lift X.toC Y.toC fun _ _ ↦ .all _ _
    exact ⟨ofEtale _ g, toOfEtale Algebra.TensorProduct.includeLeft (by ext; simp [g]),
      toOfEtale Algebra.TensorProduct.includeRight (by ext; simp [g]), trivial⟩
  cocone_maps X Y f g := by
    obtain ⟨e, he, hker⟩ :=
      Algebra.FormallyUnramified.exists_isIdempotentElem_ker_lmul' A X.alg
    let φ : X.alg ⊗[A] X.alg →ₐ[A] Y.alg :=
      Algebra.TensorProduct.lift f.hom g.hom fun _ _ ↦ .all _ _
    have hφ (x : X.alg ⊗[A] X.alg) :
        Y.toC (φ x) = X.toC (Algebra.TensorProduct.lmul' A x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [φ, Algebra.TensorProduct.lift_tmul, map_mul,
          Algebra.TensorProduct.lmul'_apply_tmul]
        rw [← AlgHom.comp_apply Y.toC f.hom, ← AlgHom.comp_apply Y.toC g.hom, f.comp_toC,
          g.comp_toC]
      | add x y hx hy => simp [hx, hy]
    let Q := Y.alg ⧸ Ideal.span {φ e}
    have : IsLocalization.Away (1 - φ e) Q :=
      IsLocalization.away_of_isIdempotentElem (he.map φ).one_sub
        (by rw [sub_sub_cancel, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
        Ideal.Quotient.mk_surjective
    have : Algebra.Etale Y.alg Q := .of_isLocalizationAway (1 - φ e)
    have : Algebra.Etale A Q := .comp A Y.alg Q
    let toC' : Q →ₐ[A] C := Ideal.Quotient.liftₐ _ Y.toC fun x hx ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      have he0 : e ∈ RingHom.ker (Algebra.TensorProduct.lmul' A : _ →ₐ[A] X.alg) :=
        hker ▸ Ideal.mem_span_singleton_self e
      rw [map_mul, hφ, RingHom.mem_ker.mp he0, map_zero, mul_zero]
    refine ⟨ofEtale Q toC', toOfEtale (Ideal.Quotient.mkₐ A _) (by ext; rfl), ?_⟩
    apply Index.Hom.ext
    ext x
    simp only [Index.comp_hom, toOfEtale_hom, AlgHom.comp_apply]
    congr 1
    refine Ideal.Quotient.eq.mpr ?_
    have hmem : x ⊗ₜ[A] (1 : X.alg) - 1 ⊗ₜ[A] x ∈ Ideal.span {e} := by
      rw [← hker, RingHom.mem_ker]
      simp
    have := Ideal.mem_map_of_mem φ hmem
    rwa [Ideal.map_span, Set.image_singleton, map_sub, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul] at this

/-- `H_A(C̄)` is ind-étale over `A`: it is the filtered colimit of the étale algebras of
`N_A(C̄)`. -/
instance indEtale : Algebra.IndEtale A (ClosedLift A C) :=
  ⟨⟨Index A C, inferInstance, inferInstance, colimitPresentation A C,
    fun X ↦ inferInstanceAs (Algebra.Etale A X.alg)⟩⟩

section

variable {A C}

variable (A C) in
/-- The canonical map from a stage of `N_A(C̄)` to `H_A(C̄)`. -/
noncomputable def ι (X : Index A C) : X.alg →ₐ[A] ClosedLift A C :=
  ((colimitPresentation A C).ι.app X).hom

lemma toAlgHom_comp_ι (X : Index A C) : (toAlgHom A C).comp (ι A C X) = X.toC :=
  congrArg CommAlgCat.Hom.hom (colimit.ι_desc (coconeC A C) X)

lemma toAlgHom_ι (X : Index A C) (b : X.alg) : toAlgHom A C (ι A C X b) = X.toC b :=
  DFunLike.congr_fun (toAlgHom_comp_ι X) b

lemma ι_comp {X Y : Index A C} (f : X ⟶ Y) : (ι A C Y).comp f.hom = ι A C X :=
  congrArg CommAlgCat.Hom.hom (colimit.w (diagram A C) f)

lemma ι_hom_apply {X Y : Index A C} (f : X ⟶ Y) (b : X.alg) : ι A C Y (f.hom b) = ι A C X b :=
  DFunLike.congr_fun (ι_comp f) b

lemma exists_ι_eq (x : ClosedLift A C) : ∃ (X : Index A C) (b : X.alg), ι A C X b = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat.{u} A)) (colimitPresentation A C).isColimit) x

/-- Blueprint `lem-exc-closed-lift-units`: an element of `H_A(C̄)` is invertible if its image in
`C̄` is invertible. -/
theorem isUnit_of_isUnit_toAlgHom {x : ClosedLift A C} (hx : IsUnit (toAlgHom A C x)) :
    IsUnit x := by
  obtain ⟨X, b, rfl⟩ := exists_ι_eq x
  rw [toAlgHom_ι] at hx
  let g : Localization.Away b →ₐ[A] C :=
    IsLocalization.liftAlgHom (M := Submonoid.powers b) (f := X.toC) <| by
      rintro ⟨_, n, rfl⟩
      simpa using hx.pow n
  let h : X ⟶ ofEtale (Localization.Away b) g :=
    toOfEtale (IsScalarTower.toAlgHom A X.alg _) (AlgHom.ext fun y ↦ IsLocalization.lift_eq _ _)
  rw [← ι_hom_apply h, toOfEtale_hom, AlgHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit b).map _).map _

/-- A map from an étale `A`-algebra `D` to `H_A(C̄)` is the canonical map from the object of
`N_A(C̄)` defined by its composite with `H_A(C̄) → C̄`. -/
lemma eq_ι_comp_of_etale (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (φ : D →ₐ[A] ClosedLift A C) :
    φ = (ι A C (ofEtale D ((toAlgHom A C).comp φ))).comp
      ((ofEtaleEquiv D ((toAlgHom A C).comp φ)).symm : D →ₐ[A] _) := by
  have : IsFinitelyPresentable.{u} (CommAlgCat.of A D) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable A _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨X, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimitPresentation A C).isColimit (CommAlgCat.ofHom φ)
  have hφ : (ι A C X).comp p.hom = φ := congrArg CommAlgCat.Hom.hom hp
  let k : ofEtale D ((toAlgHom A C).comp φ) ⟶ X :=
    fromOfEtale p.hom (by rw [← toAlgHom_comp_ι, AlgHom.comp_assoc, hφ])
  rw [← ι_comp k]
  ext d
  simp [k, fromOfEtale, ← hφ]

lemma bijective_comp_toAlgHom_of_etale (D : Type u) [CommRing D] [Algebra A D]
    [Algebra.Etale A D] :
    Function.Bijective fun φ : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp φ := by
  refine ⟨fun φ ψ h ↦ ?_, fun g ↦ ⟨(ι A C (ofEtale D g)).comp
    ((ofEtaleEquiv D g).symm : D →ₐ[A] _), ?_⟩⟩
  · rw [eq_ι_comp_of_etale D φ, eq_ι_comp_of_etale D ψ]
    exact congrArg (fun g ↦ (ι A C (ofEtale D g)).comp ((ofEtaleEquiv D g).symm : D →ₐ[A] _)) h
  · dsimp only
    rw [← AlgHom.comp_assoc, toAlgHom_comp_ι, ofEtale_toC]
    ext d
    simp

/-- Blueprint `lem-exc-closed-lift-adjunction` (first form): for an ind-étale `A`-algebra `D`,
composition with `H_A(C̄) → C̄` is a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_A(D, C̄)`. -/
theorem bijective_comp_toAlgHom (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    Function.Bijective fun φ : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp φ := by
  obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D)
  have inj (i : J) {φ ψ : P.diag.obj i →ₐ[A] ClosedLift A C}
      (h : (toAlgHom A C).comp φ = (toAlgHom A C).comp ψ) : φ = ψ :=
    have := hP i
    (bijective_comp_toAlgHom_of_etale (P.diag.obj i)).1 h
  refine ⟨fun φ ψ h ↦ ?_, fun g ↦ ?_⟩
  · refine congrArg CommAlgCat.Hom.hom (P.isColimit.hom_ext (f := CommAlgCat.ofHom φ)
      (f' := CommAlgCat.ofHom ψ) fun i ↦ CommAlgCat.hom_ext (inj i ?_))
    simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, ← AlgHom.comp_assoc]
    exact congrArg (·.comp (P.ι.app i).hom) h
  · choose lift hlift using fun i ↦
      have := hP i
      (bijective_comp_toAlgHom_of_etale (P.diag.obj i)).2 (g.comp (P.ι.app i).hom)
    let c : Cocone P.diag :=
      { pt := CommAlgCat.of A (ClosedLift A C)
        ι :=
          { app i := CommAlgCat.ofHom (lift i)
            naturality i j u := by
              refine CommAlgCat.hom_ext (inj i ?_)
              have hw := congrArg CommAlgCat.Hom.hom (P.ι.naturality u)
              simp only [Functor.const_obj_map, CommAlgCat.hom_comp] at hw
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, ← AlgHom.comp_assoc, hlift]
              rw [AlgHom.comp_assoc, hw]
              rfl } }
    refine ⟨(P.isColimit.desc c).hom, congrArg CommAlgCat.Hom.hom
      (P.isColimit.hom_ext (f := P.isColimit.desc c ≫ CommAlgCat.ofHom (toAlgHom A C))
        (f' := CommAlgCat.ofHom g) fun i ↦ ?_)⟩
    rw [IsColimit.fac_assoc]
    exact CommAlgCat.hom_ext (hlift i)

end

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

section

variable {A C}

lemma map_algebraMap_le_ker {B : Type u} [CommRing B] [Algebra A B] (f : B →ₐ[A] C) :
    I.map (algebraMap A B) ≤ RingHom.ker f := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
    IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- For an `A ⧸ I`-algebra `C̄`, `Hom_A(D, C̄) ≃ Hom_{A/I}(D / ID, C̄)`. -/
noncomputable def quotientHomEquiv (D : Type u) [CommRing D] [Algebra A D] :
    (D →ₐ[A] C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) where
  toFun g := AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Ideal.Quotient.liftₐ _ g fun _ ha ↦ map_algebraMap_le_ker I g ha)
  invFun h := (h.restrictScalars A).comp (Ideal.Quotient.mkₐ A _)
  left_inv g := rfl
  right_inv h := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

variable (A C) in
/-- Blueprint `lem-exc-closed-lift-adjunction`: for an ind-étale `A`-algebra `D`, reduction
induces a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_{A/I}(D / ID, C̄)`, natural in `D`
(`homEquiv_comp_mk`). -/
noncomputable def homEquiv (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) :=
  (Equiv.ofBijective _ (bijective_comp_toAlgHom D)).trans (quotientHomEquiv I D)

lemma homEquiv_mk (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D]
    (φ : D →ₐ[A] ClosedLift A C) (d : D) :
    homEquiv A C I D φ (Ideal.Quotient.mk _ d) = toAlgHom A C (φ d) :=
  rfl

lemma homEquiv_comp_mk {D D' : Type u} [CommRing D] [Algebra A D] [Algebra.IndEtale A D]
    [CommRing D'] [Algebra A D'] [Algebra.IndEtale A D'] (ψ : D' →ₐ[A] D)
    (φ : D →ₐ[A] ClosedLift A C) (d : D') :
    homEquiv A C I D' (φ.comp ψ) (Ideal.Quotient.mk _ d) =
      homEquiv A C I D φ (Ideal.Quotient.mk _ (ψ d)) :=
  rfl

/-- Every element of an étale `A ⧸ I`-algebra mapping to `C̄` comes from an object of
`N_A(C̄)`, using the lifting of étale algebras (`lem-exc-etale-algebra-lift`). -/
lemma exists_toC_eq (B : Type u) [CommRing B] [Algebra (A ⧸ I) B] [Algebra.Etale (A ⧸ I) B]
    (t : B →ₐ[A ⧸ I] C) (c : B) : ∃ (X : Index A C) (b : X.alg), X.toC b = t c := by
  let : Algebra A B := Algebra.compHom B (Ideal.Quotient.mk I)
  have : IsScalarTower A (A ⧸ I) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨T, _, _, _, f, hf, -⟩ := Algebra.Etale.exists_lift I B
  obtain ⟨y, rfl⟩ := hf c
  let g : T →ₐ[A] C := (t.restrictScalars A).comp f
  exact ⟨ofEtale T g, (ofEtaleEquiv T g).symm y, by simp [ofEtale_toC, g]⟩

/-- An element of a stage of `N_A(C̄)` that vanishes in `C̄` maps into `I H_A(C̄)`. -/
lemma ι_mem_map_of_toC_eq_zero [Algebra.IndEtale (A ⧸ I) C] (X : Index A C) (b : X.alg)
    (hb : X.toC b = 0) : ι A C X b ∈ I.map (algebraMap A (ClosedLift A C)) := by
  obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A ⧸ I) (S := C)
  have hcolim := isColimitOfPreserves (forget (CommAlgCat.{u} (A ⧸ I))) P.isColimit
  let JB := I.map (algebraMap A X.alg)
  have : Algebra.Etale (A ⧸ I) (X.alg ⧸ JB) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor X.alg I).symm
  let tbar : X.alg ⧸ JB →ₐ[A ⧸ I] C := quotientHomEquiv I X.alg X.toC
  have : IsFinitelyPresentable.{u} (CommAlgCat.of (A ⧸ I) (X.alg ⧸ JB)) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable _ _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit P.isColimit
    (CommAlgCat.ofHom tbar)
  have hp' : (P.ι.app i).hom (p.hom (Ideal.Quotient.mk JB b)) = 0 :=
    (congrArg (fun φ ↦ φ.hom (Ideal.Quotient.mk JB b)) hp).trans hb
  obtain ⟨k, u, hu⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcolim
    (p.hom (Ideal.Quotient.mk JB b)) (0 : P.diag.obj i)).mp
      (hp'.trans (map_zero (P.ι.app i).hom).symm)
  let q : X.alg ⧸ JB →ₐ[A ⧸ I] P.diag.obj k := (p ≫ P.diag.map u).hom
  have hq : q (Ideal.Quotient.mk JB b) = 0 := hu.trans (map_zero (P.diag.map u).hom)
  have hqι : (P.ι.app k).hom.comp q = tbar := by
    have hw := P.ι.naturality u
    simp only [Functor.const_obj_map] at hw
    exact congrArg CommAlgCat.Hom.hom ((Category.assoc _ _ _).trans
      ((congrArg (p ≫ ·) hw).trans hp))
  let : Algebra (X.alg ⧸ JB) (P.diag.obj k) := q.toRingHom.toAlgebra
  have : IsScalarTower (A ⧸ I) (X.alg ⧸ JB) (P.diag.obj k) :=
    IsScalarTower.of_algebraMap_eq' q.comp_algebraMap.symm
  have := hP k
  have : Algebra.Etale (X.alg ⧸ JB) (P.diag.obj k) := .of_restrictScalars (A ⧸ I) _ _
  let : Algebra X.alg (P.diag.obj k) := Algebra.compHom _ (Ideal.Quotient.mk JB)
  have : IsScalarTower X.alg (X.alg ⧸ JB) (P.diag.obj k) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨T, _, _, _, f, -, hker⟩ := Algebra.Etale.exists_lift JB (P.diag.obj k)
  let : Algebra A T := Algebra.compHom T (algebraMap A X.alg)
  have : IsScalarTower A X.alg T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale A T := .comp A X.alg T
  have key (y : X.alg) : (P.ι.app k).hom (f (algebraMap X.alg T y)) = X.toC y := by
    rw [f.commutes]
    exact DFunLike.congr_fun hqι (Ideal.Quotient.mk JB y)
  let g : T →ₐ[A] C :=
    { toRingHom := (P.ι.app k).hom.toRingHom.comp f.toRingHom
      commutes' a := by
        rw [IsScalarTower.algebraMap_apply A X.alg T]
        exact (key _).trans (X.toC.commutes a) }
  let h : X ⟶ ofEtale T g := toOfEtale (IsScalarTower.toAlgHom A X.alg T) (AlgHom.ext key)
  rw [← ι_hom_apply h, toOfEtale_hom, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  have hb' : algebraMap X.alg T b ∈ I.map (algebraMap A T) := by
    have hmem : algebraMap X.alg T b ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, f.commutes]
      exact hq
    rwa [hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hmem
  have := Ideal.mem_map_of_mem
    (((ι A C (ofEtale T g)).comp ((ofEtaleEquiv T g).symm : T →ₐ[A] _)) :
      T →+* ClosedLift A C) hb'
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

end

/-- Blueprint `lem-exc-closed-lift-reduction` (subsection `sk-prop-sf-open-closed-triangle`): for
an ind-étale `A ⧸ I`-algebra `C̄`, the reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of the lift
`H_A(C̄)` of `def-exc-ind-etale-closed-lift` is an isomorphism. -/
theorem bijective_reduction [Algebra.IndEtale (A ⧸ I) C] :
    Function.Bijective (reduction A C I) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨X, b, rfl⟩ := exists_ι_eq x
    rw [reduction, Ideal.Quotient.lift_mk, RingHom.coe_coe, toAlgHom_ι] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (ι_mem_map_of_toC_eq_zero I X b hz)
  · obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A ⧸ I) (S := C)
    obtain ⟨i, c, hc⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget (CommAlgCat.{u} (A ⧸ I))) P.isColimit) c
    have := hP i
    obtain ⟨X, b, hb⟩ := exists_toC_eq (C := C) I (P.diag.obj i)
      ((P.ι.app i).hom : P.diag.obj i →ₐ[A ⧸ I] C) c
    refine ⟨Ideal.Quotient.mk _ (ι A C X b), ?_⟩
    rw [reduction, Ideal.Quotient.lift_mk, RingHom.coe_coe, toAlgHom_ι, hb]
    exact hc

end ClosedLift

end Algebra
