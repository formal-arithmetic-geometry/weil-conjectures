module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-! # Exact tensor equivalences on unbounded complexes

Source: Stacks Project, Tags 06YN and 06XZ (the acyclic total-tensor test),
Tags 05RN, 0112, 011G and 014E (homotopies, shifts and cones).
(blueprint: lem-trf-exact-tensor-equivalence-kflat-homotopy)
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits HomologicalComplex

set_option autoImplicit false

namespace CategoryTheory

private theorem map_acyclic_iff
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (e : A ≌ B) [e.functor.Additive]
    (X : CochainComplex A ℤ) :
    ((e.functor.mapHomologicalComplex (.up ℤ)).obj X).Acyclic ↔ X.Acyclic := by
  apply forall_congr'
  intro n
  exact ShortComplex.exact_map_iff_of_faithful (X.sc n) e.functor

private theorem acyclic_iso
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {X Y : CochainComplex A ℤ} (i : X ≅ Y) (h : X.Acyclic) : Y.Acyclic := by
  intro n
  exact (h n).of_iso i

private theorem tensor_test_iff
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
    [TA.Additive] [∀ X : A, (TA.obj X).Additive]
    [TB.Additive] [∀ Y : B, (TB.obj Y).Additive]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (t : Functor.uncurry.obj TA.map₂CochainComplex ⋙
        e.functor.mapHomologicalComplex (.up ℤ) ≅
      (e.functor.mapHomologicalComplex (.up ℤ)).prod
          (e.functor.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TB.map₂CochainComplex)
    (P : CochainComplex A ℤ) :
    (∀ X : CochainComplex B ℤ, X.Acyclic →
      (mapBifunctor X ((e.functor.mapHomologicalComplex (.up ℤ)).obj P) TB (.up ℤ)).Acyclic) ↔
    (∀ X : CochainComplex A ℤ, X.Acyclic →
      (mapBifunctor X P TA (.up ℤ)).Acyclic) := by
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  constructor
  · intro h X hX
    apply (map_acyclic_iff e _).1
    exact acyclic_iso (t.app (X, P)).symm
      (h _ ((map_acyclic_iff e X).2 hX))
  · intro h X hX
    let ec := e.mapHomologicalComplex (.up ℤ)
    have hi := (map_acyclic_iff e.symm X).2 hX
    have ha := (map_acyclic_iff e _).2 (h (ec.inverse.obj X) hi)
    have hb := acyclic_iso (t.app (ec.inverse.obj X, P)) ha
    exact acyclic_iso
      ((Functor.uncurry.obj TB.map₂CochainComplex).mapIso
        (Iso.prod (ec.counitIso.app X) (Iso.refl (ec.functor.obj P)))) hb

private theorem homology_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (e : A ≌ B) [e.functor.Additive] (n : ℤ) :
    Nonempty (homologyFunctor A (.up ℤ) n ⋙ e.functor ≅
      e.functor.mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor B (.up ℤ) n) := by
  exact ⟨(NatIso.ofComponents (fun X ↦ (X.sc n).mapHomologyIso e.functor)
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor A (.up ℤ) n).map f) e.functor)).symm⟩

/-- An additive exact tensor equivalence transports all the unbounded cochain constructions.
Source: Stacks Project, Tags 06YN and 06XZ (K-flatness), 05RN and 0112 (homotopies),
011G (signed shifts), and 014E (mapping cones).
(blueprint: lem-trf-exact-tensor-equivalence-kflat-homotopy)

The complex equivalence is `e.mapHomologicalComplex (.up ℤ)`, whose unit and counit
are obtained by applying the given unit and counit termwise. The K-flat and resolution
clauses below spell out the right-factor acyclic test, without assuming a tensor unit,
associativity or symmetry. Both tensor hypotheses are natural isomorphisms of bifunctors
with values in the category of entire complexes. Exactness need not be supplied again:
equivalences preserve kernels and cokernels.

Proof:
1. Apply the functors termwise. Naturality makes the unit and counit chain maps;
   the triangle identities hold in each degree.
2. Additivity preserves the finite biproduct diagrams. Preservation of kernels and
   cokernels therefore gives exactness in the finite-limit and finite-colimit sense
   of `def-sp-abelian`.
3. Apply `lem-weil-pbc-exact-functor-complex-cohomology` and invert its natural
   homology comparison to obtain the two cohomology isomorphisms below.
4. Full faithfulness reflects zero objects and invertible maps. The comparisons in
   step 3 thus preserve and reflect acyclicity and quasi-isomorphisms, using
   `def-weil-abstract-derived-category`.
5. Tensor functoriality makes the acyclic total-tensor test invariant under chain
   isomorphism; acyclicity is invariant under such isomorphisms as well.
6. For acyclic Y in B, apply I to Y and the acyclic test for P, then use the E tensor
   comparison and the counit to identify the result with Tot(Y tensor E(P)). For
   reflection, apply E to Tot(X tensor P), use its comparison and then reflection
   of acyclicity. Exchange E and I for the other direction. No symmetry is used.
7. A K-flat resolution is a quasi-isomorphism with K-flat domain. Combine steps 4
   and 6; these are the tests of `def-pc-kflat-complex` and
   `def-pc-module-kflat-complex`, with no degreewise-flatness assumption.
8. Apply an additive functor to u-v=dh+hd to map homotopies. For reflection lift
   each component by fullness and reflect its equation by faithfulness.
9. Pass to homotopy classes. The termwise unit and counit descend to natural
   isomorphisms and still satisfy both triangle identities.
10. Additivity preserves the sign in the shifted differential. Identity components
    give the natural shift comparison, which also descends to homotopy classes.
11. The canonical biproduct comparison conjugates the cone differential to its
    usual block matrix. Composing with its inclusions and projections gives the
    equations below; the same comparison carries the negative projection of the
    cone triangle to the corresponding negative projection after the shift
    comparison. Quotienting gives the same cone comparison in the homotopy category.
12. All degrees and all acyclic tests range over unbounded integer-indexed
    complexes. No exactness of countable coproducts is needed. -/
theorem exactTensorEquivalence_kFlat_homotopy
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
    [TA.Additive] [∀ X : A, (TA.obj X).Additive]
    [TB.Additive] [∀ Y : B, (TB.obj Y).Additive]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (_tensorE : Functor.uncurry.obj TA.map₂CochainComplex ⋙
        e.functor.mapHomologicalComplex (.up ℤ) ≅
      (e.functor.mapHomologicalComplex (.up ℤ)).prod
          (e.functor.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TB.map₂CochainComplex)
    (_tensorI : Functor.uncurry.obj TB.map₂CochainComplex ⋙
        e.inverse.mapHomologicalComplex (.up ℤ) ≅
      (e.inverse.mapHomologicalComplex (.up ℤ)).prod
          (e.inverse.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA.map₂CochainComplex) :
    (∀ n : ℤ, Nonempty
      (homologyFunctor A (.up ℤ) n ⋙ e.functor ≅
        e.functor.mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor B (.up ℤ) n)) ∧
    (∀ X : CochainComplex A ℤ,
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj X).Acyclic ↔ X.Acyclic) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map f) ↔ QuasiIso f) ∧
    (∀ P : CochainComplex A ℤ,
      (∀ X : CochainComplex B ℤ, X.Acyclic →
        (mapBifunctor X ((e.functor.mapHomologicalComplex (.up ℤ)).obj P) TB (.up ℤ)).Acyclic) ↔
      (∀ X : CochainComplex A ℤ, X.Acyclic →
        (mapBifunctor X P TA (.up ℤ)).Acyclic)) ∧
    (∀ (P X : CochainComplex A ℤ) (q : P ⟶ X),
      (QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map q) ∧
        ∀ Y : CochainComplex B ℤ, Y.Acyclic →
          (mapBifunctor Y ((e.functor.mapHomologicalComplex (.up ℤ)).obj P) TB (.up ℤ)).Acyclic) ↔
      (QuasiIso q ∧ ∀ Y : CochainComplex A ℤ, Y.Acyclic →
        (mapBifunctor Y P TA (.up ℤ)).Acyclic)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y),
      Nonempty (Homotopy ((e.functor.mapHomologicalComplex (.up ℤ)).map f)
        ((e.functor.mapHomologicalComplex (.up ℤ)).map g)) ↔
        Nonempty (Homotopy f g)) ∧
    (∀ r : ℤ, ∃ s : shiftFunctor (CochainComplex A ℤ) r ⋙
        e.functor.mapHomologicalComplex (.up ℤ) ≅
      e.functor.mapHomologicalComplex (.up ℤ) ⋙ shiftFunctor (CochainComplex B ℤ) r,
      ∀ (X : CochainComplex A ℤ) (n : ℤ), (s.hom.app X).f n = 𝟙 _) ∧
    (∀ r : ℤ, Nonempty
      (shiftFunctor (HomotopyCategory A (.up ℤ)) r ⋙
          e.functor.mapHomotopyCategory (.up ℤ) ≅
        e.functor.mapHomotopyCategory (.up ℤ) ⋙
          shiftFunctor (HomotopyCategory B (.up ℤ)) r)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      (e.functor.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr f) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.functor).hom =
        CochainComplex.mappingCone.inr ((e.functor.mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (n : ℤ),
      (CochainComplex.mappingCone.mapHomologicalComplexIso f e.functor).hom.f n ≫
          (CochainComplex.mappingCone.fst
            ((e.functor.mapHomologicalComplex (.up ℤ)).map f)).1.v n (n + 1) rfl =
        e.functor.map ((CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl)) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      (e.functor.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          ((e.functor.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app X =
        (CochainComplex.mappingCone.mapHomologicalComplexIso f e.functor).hom ≫
          (CochainComplex.mappingCone.triangle
            ((e.functor.mapHomologicalComplex (.up ℤ)).map f)).mor₃) ∧
    (∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
      ∃ c : (e.functor.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingCone.triangleh f) ≅
        CochainComplex.mappingCone.triangleh ((e.functor.mapHomologicalComplex (.up ℤ)).map f),
      c.hom.hom₁ = 𝟙 _ ∧ c.hom.hom₂ = 𝟙 _ ∧
        c.hom.hom₃ = (HomotopyCategory.quotient B (.up ℤ)).map
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.functor).hom) ∧
    (∀ n : ℤ, Nonempty
      (homologyFunctor B (.up ℤ) n ⋙ e.inverse ≅
        e.inverse.mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor A (.up ℤ) n)) ∧
    (∀ X : CochainComplex B ℤ,
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj X).Acyclic ↔ X.Acyclic) ∧
    (∀ (X Y : CochainComplex B ℤ) (f : X ⟶ Y),
      QuasiIso ((e.inverse.mapHomologicalComplex (.up ℤ)).map f) ↔ QuasiIso f) ∧
    (∀ P : CochainComplex B ℤ,
      (∀ X : CochainComplex A ℤ, X.Acyclic →
        (mapBifunctor X ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P) TA (.up ℤ)).Acyclic) ↔
      (∀ X : CochainComplex B ℤ, X.Acyclic →
        (mapBifunctor X P TB (.up ℤ)).Acyclic)) ∧
    (∀ (P X : CochainComplex B ℤ) (q : P ⟶ X),
      (QuasiIso ((e.inverse.mapHomologicalComplex (.up ℤ)).map q) ∧
        ∀ Y : CochainComplex A ℤ, Y.Acyclic →
          (mapBifunctor Y ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P) TA (.up ℤ)).Acyclic) ↔
      (QuasiIso q ∧ ∀ Y : CochainComplex B ℤ, Y.Acyclic →
        (mapBifunctor Y P TB (.up ℤ)).Acyclic)) ∧
    (∀ (X Y : CochainComplex B ℤ) (f g : X ⟶ Y),
      Nonempty (Homotopy ((e.inverse.mapHomologicalComplex (.up ℤ)).map f)
        ((e.inverse.mapHomologicalComplex (.up ℤ)).map g)) ↔
        Nonempty (Homotopy f g)) ∧
    (∀ r : ℤ, ∃ s : shiftFunctor (CochainComplex B ℤ) r ⋙
        e.inverse.mapHomologicalComplex (.up ℤ) ≅
      e.inverse.mapHomologicalComplex (.up ℤ) ⋙ shiftFunctor (CochainComplex A ℤ) r,
      ∀ (X : CochainComplex B ℤ) (n : ℤ), (s.hom.app X).f n = 𝟙 _) ∧
    (∀ r : ℤ, Nonempty
      (shiftFunctor (HomotopyCategory B (.up ℤ)) r ⋙
          e.inverse.mapHomotopyCategory (.up ℤ) ≅
        e.inverse.mapHomotopyCategory (.up ℤ) ⋙
          shiftFunctor (HomotopyCategory A (.up ℤ)) r)) ∧
    (∀ (X Y : CochainComplex B ℤ) (f : X ⟶ Y),
      (e.inverse.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr f) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.inverse).hom =
        CochainComplex.mappingCone.inr ((e.inverse.mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ (X Y : CochainComplex B ℤ) (f : X ⟶ Y) (n : ℤ),
      (CochainComplex.mappingCone.mapHomologicalComplexIso f e.inverse).hom.f n ≫
          (CochainComplex.mappingCone.fst
            ((e.inverse.mapHomologicalComplex (.up ℤ)).map f)).1.v n (n + 1) rfl =
        e.inverse.map ((CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl)) ∧
    (∀ (X Y : CochainComplex B ℤ) (f : X ⟶ Y),
      (e.inverse.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          ((e.inverse.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app X =
        (CochainComplex.mappingCone.mapHomologicalComplexIso f e.inverse).hom ≫
          (CochainComplex.mappingCone.triangle
            ((e.inverse.mapHomologicalComplex (.up ℤ)).map f)).mor₃) ∧
    (∀ (X Y : CochainComplex B ℤ) (f : X ⟶ Y),
      ∃ c : (e.inverse.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingCone.triangleh f) ≅
        CochainComplex.mappingCone.triangleh ((e.inverse.mapHomologicalComplex (.up ℤ)).map f),
      c.hom.hom₁ = 𝟙 _ ∧ c.hom.hom₂ = 𝟙 _ ∧
        c.hom.hom₃ = (HomotopyCategory.quotient A (.up ℤ)).map
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.inverse).hom) ∧
    (∃ η : 𝟭 (HomotopyCategory A (.up ℤ)) ≅
        e.functor.mapHomotopyCategory (.up ℤ) ⋙ e.inverse.mapHomotopyCategory (.up ℤ),
      ∃ ε : e.inverse.mapHomotopyCategory (.up ℤ) ⋙
          e.functor.mapHomotopyCategory (.up ℤ) ≅ 𝟭 (HomotopyCategory B (.up ℤ)),
      (∀ X : CochainComplex A ℤ,
        η.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj X) =
          (HomotopyCategory.quotient A (.up ℤ)).map
            ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app X)) ∧
      (∀ Y : CochainComplex B ℤ,
        ε.hom.app ((HomotopyCategory.quotient B (.up ℤ)).obj Y) =
          (HomotopyCategory.quotient B (.up ℤ)).map
            ((e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app Y)) ∧
      (∀ X : HomotopyCategory A (.up ℤ),
        (e.functor.mapHomotopyCategory (.up ℤ)).map (η.hom.app X) ≫
          ε.hom.app ((e.functor.mapHomotopyCategory (.up ℤ)).obj X) = 𝟙 _) ∧
      (∀ Y : HomotopyCategory B (.up ℤ),
        η.hom.app ((e.inverse.mapHomotopyCategory (.up ℤ)).obj Y) ≫
          (e.inverse.mapHomotopyCategory (.up ℤ)).map (ε.hom.app Y) = 𝟙 _)) := by
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  have : e.symm.inverse.Additive := inferInstanceAs e.functor.Additive
  refine ⟨homology_comparison e, map_acyclic_iff e, ?_, tensor_test_iff TA TB e _tensorE,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, homology_comparison e.symm,
    map_acyclic_iff e.symm, ?_, tensor_test_iff TB TA e.symm _tensorI,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f
    exact quasiIso_map_iff_of_preservesHomology f e.functor
  · intro P X q
    exact and_congr (quasiIso_map_iff_of_preservesHomology q e.functor)
      (tensor_test_iff TA TB e _tensorE P)
  · intro X Y f g
    exact ⟨fun ⟨h⟩ ↦ ⟨e.functor.preimageHomotopy h⟩,
      fun ⟨h⟩ ↦ ⟨e.functor.mapHomotopy h⟩⟩
  · intro r
    exact ⟨(e.functor.mapHomologicalComplex (.up ℤ)).commShiftIso r, fun _ _ ↦ rfl⟩
  · intro r
    exact ⟨(e.functor.mapHomotopyCategory (.up ℤ)).commShiftIso r⟩
  · intro X Y f
    exact CochainComplex.mappingCone.map_inr f e.functor
  · intro X Y f n
    dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso]
    simp only [Hom.isoOfComponents_hom_f,
      CochainComplex.mappingCone.mapHomologicalComplexXIso,
      CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
      Preadditive.add_comp, Category.assoc,
      CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inr_f_fst_v,
      comp_zero, add_zero]
    exact Category.comp_id _
  · intro X Y f
    exact CochainComplex.mappingCone.map_δ f e.functor
  · intro X Y f
    refine ⟨CochainComplex.mappingCone.mapTrianglehIso f e.functor, ?_, ?_, ?_⟩
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ : (e.functor.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient A (.up ℤ)).obj X) ⟶ _)
      simp only [Category.id_comp]
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ : (e.functor.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient A (.up ℤ)).obj Y) ⟶ _)
      simp only [Category.id_comp]
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (HomotopyCategory.quotient B (.up ℤ)).map
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.functor).hom) = _
      simp only [Category.id_comp]
  · intro X Y f
    exact quasiIso_map_iff_of_preservesHomology f e.inverse
  · intro P X q
    exact and_congr (quasiIso_map_iff_of_preservesHomology q e.inverse)
      (tensor_test_iff TB TA e.symm _tensorI P)
  · intro X Y f g
    exact ⟨fun ⟨h⟩ ↦ ⟨e.inverse.preimageHomotopy h⟩,
      fun ⟨h⟩ ↦ ⟨e.inverse.mapHomotopy h⟩⟩
  · intro r
    exact ⟨(e.inverse.mapHomologicalComplex (.up ℤ)).commShiftIso r, fun _ _ ↦ rfl⟩
  · intro r
    exact ⟨(e.inverse.mapHomotopyCategory (.up ℤ)).commShiftIso r⟩
  · intro X Y f
    exact CochainComplex.mappingCone.map_inr f e.inverse
  · intro X Y f n
    dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso]
    simp only [Hom.isoOfComponents_hom_f,
      CochainComplex.mappingCone.mapHomologicalComplexXIso,
      CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
      Preadditive.add_comp, Category.assoc,
      CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inr_f_fst_v,
      comp_zero, add_zero]
    exact Category.comp_id _
  · intro X Y f
    exact CochainComplex.mappingCone.map_δ f e.inverse
  · intro X Y f
    refine ⟨CochainComplex.mappingCone.mapTrianglehIso f e.inverse, ?_, ?_, ?_⟩
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ : (e.inverse.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient B (.up ℤ)).obj X) ⟶ _)
      simp only [Category.id_comp]
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ : (e.inverse.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient B (.up ℤ)).obj Y) ⟶ _)
      simp only [Category.id_comp]
    · change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (HomotopyCategory.quotient A (.up ℤ)).map
          (CochainComplex.mappingCone.mapHomologicalComplexIso f e.inverse).hom) = _
      simp only [Category.id_comp]
  · let ec := e.mapHomologicalComplex (.up ℤ)
    let QA := HomotopyCategory.quotient A (.up ℤ)
    let QB := HomotopyCategory.quotient B (.up ℤ)
    let η : 𝟭 (HomotopyCategory A (.up ℤ)) ≅
        e.functor.mapHomotopyCategory (.up ℤ) ⋙ e.inverse.mapHomotopyCategory (.up ℤ) :=
      NatIso.ofComponents (fun X ↦ QA.mapIso (ec.unitIso.app X.as)) (by
        rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
        change QA.map f ≫ QA.map (ec.unitIso.hom.app Y) =
          QA.map (ec.unitIso.hom.app X) ≫ QA.map (ec.inverse.map (ec.functor.map f))
        rw [← QA.map_comp, ← QA.map_comp]
        congr 1
        simpa only [Functor.id_map, Functor.comp_map] using ec.unitIso.hom.naturality f)
    let ε : e.inverse.mapHomotopyCategory (.up ℤ) ⋙
        e.functor.mapHomotopyCategory (.up ℤ) ≅ 𝟭 (HomotopyCategory B (.up ℤ)) :=
      NatIso.ofComponents (fun Y ↦ QB.mapIso (ec.counitIso.app Y.as)) (by
        rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
        change QB.map (ec.functor.map (ec.inverse.map f)) ≫ QB.map (ec.counitIso.hom.app Y) =
          QB.map (ec.counitIso.hom.app X) ≫ QB.map f
        rw [← QB.map_comp, ← QB.map_comp]
        congr 1
        simpa only [Functor.id_map, Functor.comp_map] using ec.counitIso.hom.naturality f)
    refine ⟨η, ε, fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_⟩
    · rintro ⟨X⟩
      change QB.map (ec.functor.map (ec.unitIso.hom.app X)) ≫
        QB.map (ec.counitIso.hom.app (ec.functor.obj X)) = 𝟙 _
      rw [← QB.map_comp]
      have ht : ec.functor.map (ec.unitIso.hom.app X) ≫
          ec.counitIso.hom.app (ec.functor.obj X) = 𝟙 _ := ec.functor_unit_comp X
      rw [ht]
      exact QB.map_id _
    · rintro ⟨Y⟩
      change QA.map (ec.unitIso.hom.app (ec.inverse.obj Y)) ≫
        QA.map (ec.inverse.map (ec.counitIso.hom.app Y)) = 𝟙 _
      rw [← QA.map_comp]
      have ht : ec.unitIso.hom.app (ec.inverse.obj Y) ≫
          ec.inverse.map (ec.counitIso.hom.app Y) = 𝟙 _ := ec.unit_inverse_comp Y
      rw [ht]
      exact QA.map_id _

end CategoryTheory
