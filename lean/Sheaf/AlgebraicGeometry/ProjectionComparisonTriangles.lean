/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProjectionComparisonExact

/-! # Shifts and triangles for the projection comparison locus

Source: Stacks Project, Tag 08EU, proof, together with Tags 08DT and 08DZ.
(blueprint: lem-sc-projection-comparison-triangles).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The isomorphism locus of the pullback-adjunction projection mate is closed
under shifts and third triangle objects.
No assertion that it contains perfect objects or every object is made here.
Source: Stacks Project, Tag 08EU, proof, using Tags 08DT and 08DZ.
(blueprint: lem-sc-projection-comparison-triangles).

Proof: write F = Lf* and R = Rf_*. The canonical component p_K is the
adjunct of the inverse tensorator followed by F(K) tensor the counit. Counit
and tensorator naturality make p natural in K. Choose K-flat representatives
for tensor and pullback and K-injective representatives for direct image;
these constructions preserve mapping-cone triangles. On complexes, the tensor
shift comparison sends a homogeneous tensor to the tensor in shifted degree,
with the Koszul sign required by the total differential. The inverse tensorator
and counit commute with these comparisons, so taking adjuncts gives an equality
identifying p at K[n] with the shift of p at K, conjugated by comparison
isomorphisms. For the monoidal structure supplied in the statement, transport
the pullback shift comparison using K[n] = K tensor the shifted unit and its
tensorator. Tensorator associativity and unit coherence give the same equality;
no compatibility of the supplied tensorator with a separately fixed shift
comparison is assumed. Hence invertibility passes to shifts and objects
isomorphic to them. Apply the two exact composite functors and this comparison
to a distinguished triangle to obtain a morphism of distinguished triangles.
Transport its first two components along the vertex isomorphisms. They are
invertible, so the triangle two-out-of-three theorem makes the third component
invertible; transport it to C. This includes n = 0, the zero object and the
contractible triangles. This lemma supplies only the shift and cone steps;
the perfect-object, retract and coproduct steps are proved separately. -/
theorem projectionComparison_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedQCohCategory Z) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      IsIso ((a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj
          ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C) := by
  obtain ⟨s, t, hs, ht, hη⟩ := projectionComparison_exact f a E
  let := s
  let := t
  let := hs
  let := ht
  let η := projectionComparisonNatTrans f a E.obj
  let : NatTrans.CommShift η ℤ := hη
  have transport (X X' : schemeDerivedCategory Y) (e : X ≅ X')
      (h : IsIso (η.app X')) : IsIso (η.app X) := by
    let := h
    have he : η.app X =
        (tensorRight ((schemeDerivedDirectImage f).obj E.obj)).map e.hom ≫
          η.app X' ≫
          ((derivedPullback f ⋙ tensorRight E.obj) ⋙
            schemeDerivedDirectImage f).map e.inv := by
      rw [η.naturality_assoc, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
    rw [he]
    infer_instance
  change (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), IsIso (η.app A.obj) →
    ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) →
      IsIso (η.app B.obj)) ∧ _
  constructor
  · intro A n hA B ⟨e⟩
    apply transport _ _ e
    let := hA
    rw [NatTrans.app_shift η n A.obj]
    infer_instance
  · intro A B hA hB T hT ⟨eA⟩ ⟨eB⟩ C ⟨eC⟩
    change IsIso (η.app C.obj)
    change IsIso (η.app A.obj) at hA
    change IsIso (η.app B.obj) at hB
    let S := tensorRight ((schemeDerivedDirectImage f).obj E.obj)
    let R := (derivedPullback f ⋙ tensorRight E.obj) ⋙ schemeDerivedDirectImage f
    let φ : S.mapTriangle.obj T ⟶ R.mapTriangle.obj T :=
      { hom₁ := η.app T.obj₁
        hom₂ := η.app T.obj₂
        hom₃ := η.app T.obj₃
        comm₁ := η.naturality T.mor₁
        comm₂ := η.naturality T.mor₂
        comm₃ := by
          change (S.map T.mor₃ ≫ (S.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
              (η.app T.obj₁)⟦(1 : ℤ)⟧' =
            η.app T.obj₃ ≫ R.map T.mor₃ ≫ (R.commShiftIso (1 : ℤ)).hom.app T.obj₁
          rw [Category.assoc, NatTrans.shift_app_comm,
            ← Category.assoc, η.naturality, Category.assoc] }
    have h₁ : IsIso φ.hom₁ := transport _ _ eA hA
    have h₂ : IsIso φ.hom₂ := transport _ _ eB hB
    have h₃ : IsIso (η.app T.obj₃) :=
      Pretriangulated.isIso₃_of_isIso₁₂ φ
        (S.map_distinguished T hT) (R.map_distinguished T hT) h₁ h₂
    exact transport _ _ eC.symm h₃

end AlgebraicGeometry
