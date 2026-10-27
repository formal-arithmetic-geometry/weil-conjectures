module

public import WeilConjectures.CategoryTheory.Abelian.RightDerivedInjectiveBoundary
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Right-derived comparison of injective cone-quotient triangles

Source: Stacks Project, Derived Categories, Tags 014Z, 0152 and 05TH; definition-cone.
(blueprint: lem-pur-derived-injective-cone-comparison).

The cone, quotient and negative projection are Mathlib's actual constructions.
The comparison maps are inverse derived units, with the quotient factorization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

variable [HasDerivedCategory.{w₁} A]

/-- The canonical SES triangle in D⁺, with the negative-cone-projection boundary
lifted through the full faithful inclusion in D.

Source: Stacks Project, Derived Categories, Tags 014Z and 0152.
(blueprint: lem-pur-derived-injective-cone-comparison). -/
noncomputable def boundedBelowRowTriangle (H : ShortComplex (CochainComplex.Plus A))
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact) :
    Triangle (DerivedCategory.Plus A) :=
  Triangle.mk (DerivedCategory.Plus.Q.map H.f) (DerivedCategory.Plus.Q.map H.g)
    (boundedBelowSESBoundary H hH)

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives A]

private lemma comparison_naturality
    (T : A ⥤ B) [T.Additive] (K L : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (K.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (f : K ⟶ L) :
    (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map f) ≫ boundedBelowInjectiveComparison T L =
      boundedBelowInjectiveComparison T K ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
  let q := HomotopyCategory.Plus.quotient A
  have hn := T.rightDerivedFunctorPlusUnit.naturality (q.map f)
  have hi : (DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus).map (q.map f) ≫
      inv (T.rightDerivedFunctorPlusUnit.app (q.obj L)) =
      inv (T.rightDerivedFunctorPlusUnit.app (q.obj K)) ≫
        (T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map f) := by
    apply (cancel_epi (T.rightDerivedFunctorPlusUnit.app (q.obj K))).1
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, IsIso.hom_inv_id_assoc]
  have hi' := congrArg (fun k ↦ DerivedCategory.Plus.ι.map k ≫
    (DerivedCategory.quotientCompQhIso B).hom.app
      ((T.mapHomologicalComplex (.up ℤ)).obj L.obj)) hi
  simp only [Functor.map_comp, Category.assoc] at hi'
  have hq := (DerivedCategory.quotientCompQhIso B).hom.naturality
    ((T.mapHomologicalComplex (.up ℤ)).map f.hom)
  have hq' : DerivedCategory.Plus.ι.map
      ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map f)) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((T.mapHomologicalComplex (.up ℤ)).obj L.obj) =
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((T.mapHomologicalComplex (.up ℤ)).obj K.obj) ≫
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := hq
  rw [hq'] at hi'
  simp only [boundedBelowInjectiveComparison, DerivedCategory.Plus.Q,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  convert hi' using 1 <;> rfl

private noncomputable def row_triangle_iso
    (H : ShortComplex (CochainComplex.Plus A))
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact) :
    DerivedCategory.Plus.ι.mapTriangle.obj (boundedBelowRowTriangle H hH) ≅
      DerivedCategory.triangleOfSES hH := by
  refine Triangle.isoMk _ _ ((DerivedCategory.quotientCompQhIso A).app H.X₁.obj)
    ((DerivedCategory.quotientCompQhIso A).app H.X₂.obj)
    ((DerivedCategory.quotientCompQhIso A).app H.X₃.obj) ?_ ?_ ?_
  · exact (DerivedCategory.quotientCompQhIso A).hom.naturality H.f.hom
  · exact (DerivedCategory.quotientCompQhIso A).hom.naturality H.g.hom
  · change (DerivedCategory.Plus.ι.map (boundedBelowSESBoundary H hH) ≫ _) ≫ _ = _
    unfold boundedBelowSESBoundary
    rw [Functor.map_preimage]
    change ((_ ≫ DerivedCategory.triangleOfSESδ hH ≫
      ((DerivedCategory.quotientCompQhIso A).inv.app H.X₁.obj)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        (DerivedCategory.Plus.Q.obj H.X₁)) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Plus.Q.obj H.X₁)) ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app H.X₁.obj)⟦(1 : ℤ)⟧' = _
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.comp_id]
    rfl

omit [EnoughInjectives A] in
private lemma boundary_naturality
    (H H' : ShortComplex (CochainComplex.Plus A))
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hH' : (H'.map (CochainComplex.plus A).ι).ShortExact) (φ : H ⟶ H') :
    boundedBelowSESBoundary H hH ≫ (DerivedCategory.Plus.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.Q.map φ.τ₃ ≫ boundedBelowSESBoundary H' hH' := by
  let I := DerivedCategory.Plus.ι (C := A)
  let e := DerivedCategory.quotientCompQhIso A
  have hd (J : ShortComplex (CochainComplex.Plus A))
      (hJ : (J.map (CochainComplex.plus A).ι).ShortExact) :
      I.map (boundedBelowSESBoundary J hJ) ≫
        (I.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Plus.Q.obj J.X₁) ≫
        (e.hom.app J.X₁.obj)⟦(1 : ℤ)⟧' =
      e.hom.app J.X₃.obj ≫ DerivedCategory.triangleOfSESδ hJ := by
    have h := (row_triangle_iso J hJ).hom.comm₃
    change (_ ≫ _) ≫ _ = _ at h
    exact (Category.assoc _ _ _).symm.trans h
  have hn₁ : I.map (DerivedCategory.Plus.Q.map φ.τ₁) ≫ e.hom.app H'.X₁.obj =
      e.hom.app H.X₁.obj ≫ DerivedCategory.Q.map φ.τ₁.hom :=
    e.hom.naturality φ.τ₁.hom
  have hn₃ : I.map (DerivedCategory.Plus.Q.map φ.τ₃) ≫ e.hom.app H'.X₃.obj =
      e.hom.app H.X₃.obj ≫ DerivedCategory.Q.map φ.τ₃.hom :=
    e.hom.naturality φ.τ₃.hom
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso (1 : ℤ)).hom.app
    (DerivedCategory.Plus.Q.obj H'.X₁) ≫ (e.hom.app H'.X₁.obj)⟦(1 : ℤ)⟧')).1
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp, hn₁, Functor.map_comp]
  rw [reassoc_of% (hd H hH), hd H' hH', reassoc_of% hn₃]
  congr 1
  exact DerivedCategory.triangleOfSESδ_naturality hH hH'
    ((CochainComplex.plus A).ι.mapShortComplex.map φ)

/-- Inverse units identify the whole derived image of the row triangle with the
triangle of the termwise image; all three components are prescribed.
The target is written through the full faithful inclusion D⁺(B) → D(B).

Source: Stacks Project, Derived Categories, Tags 014Z, 0152 and 05TH.
(blueprint: lem-pur-derived-injective-cone-comparison).

Proof: Step 3 applies lem-pc-cone-short-exact-quasi-iso to the row and its image.
Localize their cone triangles and replace the cone vertex by the quotient;
the last arrow is negative projection after inverse quotient. Step 4 uses
lem-weil-pbc-right-derived-plus-injective: the units on E,F,G are invertible,
and their naturality proves the first two triangle squares. Step 5 applies
lem-sc-p1-right-derived-injective-boundary to obtain the last square, including
the canonical shift comparison of RT. These squares give a triangle morphism
with invertible components, hence the displayed triangle isomorphism. The
source triangle is distinguished by its cone presentation, and its derived
image is therefore distinguished, as is the triangle of the image row.
-/
theorem rightDerived_injectiveRow_triangleComparison
    (T : A ⥤ B) [T.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hTH : ((H.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact) :
    (boundedBelowRowTriangle H hH ∈ distTriang (DerivedCategory.Plus A)) ∧
    ((T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      (boundedBelowRowTriangle H hH) ∈ distTriang (DerivedCategory B)) ∧
    ∃ e : (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
        (boundedBelowRowTriangle H hH) ≅ DerivedCategory.triangleOfSES hTH,
      e.hom.hom₁ = boundedBelowInjectiveComparison T H.X₁ ∧
      e.hom.hom₂ = boundedBelowInjectiveComparison T H.X₂ ∧
      e.hom.hom₃ = boundedBelowInjectiveComparison T H.X₃ := by
  have hdist : boundedBelowRowTriangle H hH ∈ distTriang (DerivedCategory.Plus A) := by
    apply (DerivedCategory.Plus.ι.map_distinguished_iff _).1
    exact (distinguished_iff_of_iso (row_triangle_iso H hH)).2
      (DerivedCategory.triangleOfSES_distinguished hH)
  refine ⟨hdist, (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map_distinguished
    _ hdist, ?_⟩
  have hi (K : CochainComplex.Plus A) [∀ n : ℤ, Injective (K.obj.X n)] :
      IsIso (boundedBelowInjectiveComparison T K) := by
    dsimp [boundedBelowInjectiveComparison]
    infer_instance
  let e := Triangle.isoMk
    ((T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      (boundedBelowRowTriangle H hH)) (DerivedCategory.triangleOfSES hTH)
    (asIso (boundedBelowInjectiveComparison T H.X₁))
    (asIso (boundedBelowInjectiveComparison T H.X₂))
    (asIso (boundedBelowInjectiveComparison T H.X₃))
    (comparison_naturality T _ _ H.f) (comparison_naturality T _ _ H.g)
    (by
      change ((_ ≫ _) ≫ _) = _
      rw [Category.assoc]
      exact rightDerived_injectiveComplex_boundary T H hH hTH)
  exact ⟨e, rfl, rfl, rfl⟩

set_option linter.unusedSectionVars false in
/-- The canonical additive cone comparison preserves inclusion, negative
projection (with its shift comparison), and quotient. The two quotients are
quasi-isomorphisms, and the cone is bounded below and termwise injective.

Source: Stacks Project, Derived Categories, definition-cone, Tags 014Z and 05TH.
(blueprint: lem-pur-derived-injective-cone-comparison).

Proof: Step 2 uses the canonical additive biproduct comparison in each degree.
Its differential has matrix ((T d_F,T u),(0,-T d_E)), and its inclusion,
negative-projection and quotient identities follow on the two summands.
Step 3 applies lem-pc-cone-short-exact-quasi-iso to both short exact rows.
For Step 1 choose a common strict lower bound N; the cone vanishes below N-1.
Each cone term is a biproduct of two injectives: extend maps along a mono
componentwise and pair the extensions. No preservation of injectives is used.
-/
theorem rightDerived_injectiveRow_coneComparison
    (T : A ⥤ B) [T.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    (_hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (_hTH : ((H.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact) :
    CochainComplex.plus A (CochainComplex.mappingCone H.f.hom) ∧
    (∀ n : ℤ, Injective ((CochainComplex.mappingCone H.f.hom).X n)) ∧
    QuasiIso (CochainComplex.mappingCone.descShortComplex
      (H.map (CochainComplex.plus A).ι)) ∧
    QuasiIso (CochainComplex.mappingCone.descShortComplex
      ((H.map (CochainComplex.plus A).ι).map (T.mapHomologicalComplex (.up ℤ)))) ∧
    (T.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr H.f.hom) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso H.f.hom T).hom =
      CochainComplex.mappingCone.inr ((T.mapHomologicalComplex (.up ℤ)).map H.f.hom) ∧
    (T.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.triangle H.f.hom).mor₃ ≫
        ((T.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app H.X₁.obj =
      (CochainComplex.mappingCone.mapHomologicalComplexIso H.f.hom T).hom ≫
        (CochainComplex.mappingCone.triangle
          ((T.mapHomologicalComplex (.up ℤ)).map H.f.hom)).mor₃ ∧
    (CochainComplex.mappingCone.mapHomologicalComplexIso H.f.hom T).hom ≫
        CochainComplex.mappingCone.descShortComplex
          ((H.map (CochainComplex.plus A).ι).map (T.mapHomologicalComplex (.up ℤ))) =
      (T.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex (H.map (CochainComplex.plus A).ι)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n₁, _⟩ := H.X₁.property
    obtain ⟨n₂, _⟩ := H.X₂.property
    exact ⟨min (n₁ - 1) n₂,
      CochainComplex.isStrictlyGE_mappingCone H.f.hom n₁ n₂ _ (by omega) (by omega)⟩
  · intro n
    refine Injective.mk fun g f _ ↦ ?_
    obtain ⟨a, ha⟩ := Injective.factors
      (g ≫ (CochainComplex.mappingCone.fst H.f.hom).1.v n (n + 1) rfl) f
    obtain ⟨b, hb⟩ := Injective.factors
      (g ≫ (CochainComplex.mappingCone.snd H.f.hom).v n n (by omega)) f
    refine ⟨a ≫ (CochainComplex.mappingCone.inl H.f.hom).v (n + 1) n (by omega) +
      b ≫ (CochainComplex.mappingCone.inr H.f.hom).f n, ?_⟩
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ha, hb]
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      CochainComplex.mappingCone.id_X H.f.hom n (n + 1) rfl, Category.comp_id]
  · exact CochainComplex.mappingCone.quasiIso_descShortComplex _hH
  · exact CochainComplex.mappingCone.quasiIso_descShortComplex _hTH
  · exact CochainComplex.mappingCone.map_inr _ T
  · exact CochainComplex.mappingCone.map_δ _ T
  · exact CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex T
      (H.map (CochainComplex.plus A).ι)

/-- The derived image of the cone quotient is the image-row quotient under the
canonical cone isomorphism and the invertible right-derived unit at the cone.

Source: Stacks Project, Derived Categories, Tags 014Z, 0152 and 05TH.
(blueprint: lem-pur-derived-injective-cone-comparison).

Proof: Step 1 makes the explicit cone bounded below and termwise injective.
Its derived unit is invertible by lem-weil-pbc-right-derived-plus-injective.
Naturality of that unit at q, followed by the quotient-factorization isomorphism,
identifies RT(Qq) with Q(Tq). Step 2 gives Tq = q_T chi, so substitute this
identity (Step 4). The image-row boundary is definitionally inverse Qq_T followed
by the negative projection, with the localization shift comparison (Step 3).
The existential proof hP only bundles the fixed, explicit cone; it chooses no data.
-/
theorem rightDerived_injectiveRow_coneQuotient
    (T : A ⥤ B) [T.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    (_hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (_hTH : ((H.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact) :
    ∃ hP : CochainComplex.plus A (CochainComplex.mappingCone H.f.hom),
      IsIso (T.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj ⟨CochainComplex.mappingCone H.f.hom, hP⟩)) ∧
      (DerivedCategory.quotientCompQhIso B).inv.app
          ((T.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone H.f.hom)) ≫
        DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj
            ⟨CochainComplex.mappingCone H.f.hom, hP⟩)) ≫
        (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          (DerivedCategory.Plus.Q.map (ObjectProperty.homMk
            (CochainComplex.mappingCone.descShortComplex (H.map (CochainComplex.plus A).ι)) :
              (⟨CochainComplex.mappingCone H.f.hom, hP⟩ : CochainComplex.Plus A) ⟶ H.X₃)) ≫
        boundedBelowInjectiveComparison T H.X₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.mapHomologicalComplexIso H.f.hom T).hom ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
          ((H.map (CochainComplex.plus A).ι).map (T.mapHomologicalComplex (.up ℤ)))) := by
  obtain ⟨hP, hI, _⟩ := rightDerived_injectiveRow_coneComparison T H _hH _hTH
  let P : CochainComplex.Plus A := ⟨CochainComplex.mappingCone H.f.hom, hP⟩
  let q : P ⟶ H.X₃ := ObjectProperty.homMk
    (CochainComplex.mappingCone.descShortComplex (H.map (CochainComplex.plus A).ι))
  refine ⟨hP, inferInstance, ?_⟩
  have hn := comparison_naturality T P H.X₃ q
  change (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient A).obj P)) ≫
      (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map q) ≫ boundedBelowInjectiveComparison T H.X₃ = _
  rw [hn]
  unfold boundedBelowInjectiveComparison
  simp only [Functor.map_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  change (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    (DerivedCategory.quotientCompQhIso B).hom.app _ ≫
    DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map q.hom) = _
  rw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp]
  congr 1
  exact (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex T
    (H.map (CochainComplex.plus A).ι)).symm

/-- The inverse-unit triangle comparison and the strict cone construction are
natural in row morphisms. The cone map is diagonal on the two summands, and
commutes with quotient and negative projection.

Source: Stacks Project, Derived Categories, Tag 0152 and lemma-functorial-cone.
(blueprint: lem-pur-derived-injective-cone-comparison).

Proof: Step 6 forms the strict cone map (b,a) ↦ (f b,e a). The square for the
first row arrow makes it a chain map. Its biproduct components prove the
quotient and negative-projection squares, and the naturality of the additive
cone comparison. Localize and invert the quasi-isomorphic quotient maps to
obtain naturality of both SES boundaries. Naturality of the derived unit at
e,f,g gives the last three displayed equations. They assert naturality of the
three prescribed components of the triangle isomorphism in the preceding
statement; a triangle morphism is determined by its three components.
-/
theorem rightDerived_injectiveRow_naturality
    (T : A ⥤ B) [T.Additive] (H H' : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₃.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hH' : (H'.map (CochainComplex.plus A).ι).ShortExact)
    (hTH : ((H.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact)
    (hTH' : ((H'.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact)
    (φ : H ⟶ H') :
    (∀ n : ℤ, (CochainComplex.mappingCone.inr H.f.hom).f n ≫
        (CochainComplex.mappingCone.map H.f.hom H'.f.hom
          φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)).f n =
      φ.τ₂.hom.f n ≫ (CochainComplex.mappingCone.inr H'.f.hom).f n) ∧
    (∀ n : ℤ, (CochainComplex.mappingCone.inl H.f.hom).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone.map H.f.hom H'.f.hom
          φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)).f n =
      φ.τ₁.hom.f (n + 1) ≫
        (CochainComplex.mappingCone.inl H'.f.hom).v (n + 1) n (by omega)) ∧
    (CochainComplex.mappingCone.map H.f.hom H'.f.hom
      φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)) ≫
        CochainComplex.mappingCone.descShortComplex (H'.map (CochainComplex.plus A).ι) =
      (CochainComplex.mappingCone.descShortComplex (H.map (CochainComplex.plus A).ι)) ≫ φ.τ₃.hom ∧
    (CochainComplex.mappingCone.map H.f.hom H'.f.hom
      φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)) ≫
        (CochainComplex.mappingCone.triangle H'.f.hom).mor₃ =
      (CochainComplex.mappingCone.triangle H.f.hom).mor₃ ≫ φ.τ₁.hom⟦(1 : ℤ)⟧' ∧
    (T.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.map H.f.hom H'.f.hom
      φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso H'.f.hom T).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso H.f.hom T).hom ≫
        CochainComplex.mappingCone.map
          ((T.mapHomologicalComplex (.up ℤ)).map H.f.hom)
          ((T.mapHomologicalComplex (.up ℤ)).map H'.f.hom)
          ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₁.hom)
          ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₂.hom)
          ((T.mapHomologicalComplex (.up ℤ)).mapShortComplex.map
            ((CochainComplex.plus A).ι.mapShortComplex.map φ)).comm₁₂.symm ∧
    boundedBelowSESBoundary H hH ≫ (DerivedCategory.Plus.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.Q.map φ.τ₃ ≫ boundedBelowSESBoundary H' hH' ∧
    DerivedCategory.triangleOfSESδ hTH ≫
        (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₁.hom))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₃.hom) ≫
        DerivedCategory.triangleOfSESδ hTH' ∧
    (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map φ.τ₁) ≫ boundedBelowInjectiveComparison T H'.X₁ =
      boundedBelowInjectiveComparison T H.X₁ ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₁.hom) ∧
    (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map φ.τ₂) ≫ boundedBelowInjectiveComparison T H'.X₂ =
      boundedBelowInjectiveComparison T H.X₂ ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₂.hom) ∧
    (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map φ.τ₃) ≫ boundedBelowInjectiveComparison T H'.X₃ =
      boundedBelowInjectiveComparison T H.X₃ ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map φ.τ₃.hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, boundary_naturality H H' hH hH' φ,
    DerivedCategory.triangleOfSESδ_naturality hTH hTH'
      ((T.mapHomologicalComplex (.up ℤ)).mapShortComplex.map
        ((CochainComplex.plus A).ι.mapShortComplex.map φ)),
    comparison_naturality T _ _ φ.τ₁, comparison_naturality T _ _ φ.τ₂,
    comparison_naturality T _ _ φ.τ₃⟩
  · intro n
    simp [CochainComplex.mappingCone.map]
  · intro n
    simp [CochainComplex.mappingCone.map]
  · exact CochainComplex.mappingCone.map_descShortComplex _ _
      ((CochainComplex.plus A).ι.mapShortComplex.map φ)
  · exact (CochainComplex.mappingCone.triangleMap H.f.hom H'.f.hom
      φ.τ₁.hom φ.τ₂.hom (congrArg (fun k ↦ k.hom) φ.comm₁₂.symm)).comm₃.symm
  · ext n
    dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso]
    simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq _ T n (n + 1) rfl,
      CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom]
    simp [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl,
      Preadditive.comp_add, Preadditive.add_comp]
    simp only [← T.map_comp_assoc,
      CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inr_f_fst_v,
      CochainComplex.mappingCone.inl_v_snd_v, CochainComplex.mappingCone.inr_f_snd_v,
      T.map_id, T.map_zero, Category.id_comp,
      zero_comp, comp_zero, add_zero, zero_add]

/-- Naturality as an equality of triangle morphisms for the prescribed comparison
isomorphisms, in addition to the explicit cone and component equations above.

Source: Stacks Project, Derived Categories, Tag 0152, naturality of the SES triangle.
(blueprint: lem-pur-derived-injective-cone-comparison).

Proof: Step 6 localizes the strict diagonal cone map and inverts the quotient
quasi-isomorphisms, giving the unique source triangle morphism with components
Qe,Qf,Qg. The first two squares are the row equations; the third is boundary
naturality. Each comparison component is the inverse derived unit, so its
naturality at e,f,g identifies the three components of the displayed composites.
Triangle morphisms are determined by their components, proving the equality.
-/
theorem rightDerived_injectiveRow_triangleNaturality
    (T : A ⥤ B) [T.Additive] (H H' : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H'.X₃.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hH' : (H'.map (CochainComplex.plus A).ι).ShortExact)
    (hTH : ((H.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact)
    (hTH' : ((H'.map (CochainComplex.plus A).ι).map
      (T.mapHomologicalComplex (.up ℤ))).ShortExact)
    (φ : H ⟶ H')
    (e : (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      (boundedBelowRowTriangle H hH) ≅ DerivedCategory.triangleOfSES hTH)
    (e' : (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      (boundedBelowRowTriangle H' hH') ≅ DerivedCategory.triangleOfSES hTH')
    (_he₁ : e.hom.hom₁ = boundedBelowInjectiveComparison T H.X₁)
    (_he₂ : e.hom.hom₂ = boundedBelowInjectiveComparison T H.X₂)
    (_he₃ : e.hom.hom₃ = boundedBelowInjectiveComparison T H.X₃)
    (_he'₁ : e'.hom.hom₁ = boundedBelowInjectiveComparison T H'.X₁)
    (_he'₂ : e'.hom.hom₂ = boundedBelowInjectiveComparison T H'.X₂)
    (_he'₃ : e'.hom.hom₃ = boundedBelowInjectiveComparison T H'.X₃) :
    ∃ ψ : boundedBelowRowTriangle H hH ⟶ boundedBelowRowTriangle H' hH',
      ψ.hom₁ = DerivedCategory.Plus.Q.map φ.τ₁ ∧
      ψ.hom₂ = DerivedCategory.Plus.Q.map φ.τ₂ ∧
      ψ.hom₃ = DerivedCategory.Plus.Q.map φ.τ₃ ∧
      (T.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.map ψ ≫ e'.hom =
        e.hom ≫ DerivedCategory.triangleOfSES.map hTH hTH'
          ((T.mapHomologicalComplex (.up ℤ)).mapShortComplex.map
            ((CochainComplex.plus A).ι.mapShortComplex.map φ)) := by
  let ψ : boundedBelowRowTriangle H hH ⟶ boundedBelowRowTriangle H' hH' :=
    { hom₁ := DerivedCategory.Plus.Q.map φ.τ₁
      hom₂ := DerivedCategory.Plus.Q.map φ.τ₂
      hom₃ := DerivedCategory.Plus.Q.map φ.τ₃
      comm₁ := by
        change DerivedCategory.Plus.Q.map H.f ≫ DerivedCategory.Plus.Q.map φ.τ₂ =
          DerivedCategory.Plus.Q.map φ.τ₁ ≫ DerivedCategory.Plus.Q.map H'.f
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
      comm₂ := by
        change DerivedCategory.Plus.Q.map H.g ≫ DerivedCategory.Plus.Q.map φ.τ₃ =
          DerivedCategory.Plus.Q.map φ.τ₂ ≫ DerivedCategory.Plus.Q.map H'.g
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]
      comm₃ := boundary_naturality H H' hH hH' φ }
  refine ⟨ψ, rfl, rfl, rfl, ?_⟩
  ext
  · simp only [comp_hom₁, Functor.mapTriangle_map_hom₁,
      DerivedCategory.triangleOfSES.map_hom₁, _he₁, _he'₁]
    exact comparison_naturality T _ _ φ.τ₁
  · simp only [comp_hom₂, Functor.mapTriangle_map_hom₂,
      DerivedCategory.triangleOfSES.map_hom₂, _he₂, _he'₂]
    exact comparison_naturality T _ _ φ.τ₂
  · simp only [comp_hom₃, Functor.mapTriangle_map_hom₃,
      DerivedCategory.triangleOfSES.map_hom₃, _he₃, _he'₃]
    exact comparison_naturality T _ _ φ.τ₃

end CategoryTheory
