/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData
import WeilConjectures.AlgebraicGeometry.SfNormalizedRationalClosedComparison
import WeilConjectures.AlgebraicGeometry.SfNormalizedRecollementTriangles
import WeilConjectures.AlgebraicGeometry.AutomorphismConstructibleStageEquivalence

/-! # Frobenius squares for normalized rational recollement maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w w₁
open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem closed_mate_square
    {C : Type w} [Category.{w₁} C] {B : Type v} [Category B]
    {L : C ⥤ B} {R : B ⥤ C} (adj : L ⊣ R)
    (G : C ⥤ C) (H : B ⥤ B) (d : L ⋙ H ≅ G ⋙ L)
    (c : R ⋙ G ≅ H ⋙ R)
    (hc : c.hom = (mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.inv)).natTrans)
    (K : C) (theta : G.obj K ≅ K) :
    ∃ e : G.obj (R.obj (L.obj K)) ≅ R.obj (L.obj K),
      G.map (adj.unit.app K) ≫ e.hom = theta.hom ≫ adj.unit.app K := by
  let e := c.app (L.obj K) ≪≫ R.mapIso (d.app K) ≪≫ R.mapIso (L.mapIso theta)
  refine ⟨e, ?_⟩
  have hm := unit_mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.inv) K
  change G.map (adj.unit.app K) ≫
    ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.inv)).natTrans).app (L.obj K) =
      adj.unit.app (G.obj K) ≫ R.map (d.inv.app K) at hm
  rw [← hc] at hm
  change G.map (adj.unit.app K) ≫
    (c.hom.app (L.obj K) ≫ R.map (d.hom.app K) ≫ R.map (L.map theta.hom)) = _
  rw [← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc, ← R.map_comp, Iso.inv_hom_id_app_assoc]
  exact (adj.unit.naturality theta.hom).symm

private theorem normalized_closed_square
    {C : Type w} [Category.{w₁} C] (G : C ⥤ C)
    (P S : C ⥤ C) (eta : 𝟭 C ⟶ P) (etaS : 𝟭 C ⟶ S)
    (e : P ≅ S) (he : ∀ K, eta.app K ≫ e.hom.app K = etaS.app K)
    (K : C) (theta : G.obj K ≅ K)
    (c : G.obj (S.obj K) ≅ S.obj K)
    (hc : G.map (etaS.app K) ≫ c.hom = theta.hom ≫ etaS.app K) :
    ∃ c' : G.obj (P.obj K) ≅ P.obj K,
      G.map (eta.app K) ≫ c'.hom = theta.hom ≫ eta.app K := by
  refine ⟨G.mapIso (e.app K) ≪≫ c ≪≫ (e.app K).symm, ?_⟩
  change G.map (eta.app K) ≫
    (G.map (e.hom.app K) ≫ c.hom ≫ e.inv.app K) = _
  rw [← Category.assoc, ← Category.assoc, ← G.map_comp, he K, hc, Category.assoc,
    ← he K]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem open_square_of_closed_square
    {C : Type w} [Category.{w₁} C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T T' : Triangle C) (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (e₂ : T.obj₂ ≅ T'.obj₂) (e₃ : T.obj₃ ≅ T'.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂) :
    ∃ e₁ : T.obj₁ ≅ T'.obj₁, T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁ := by
  let eR := Pretriangulated.isoTriangleOfIso₁₂ T.rotate T'.rotate
    (Pretriangulated.rot_of_distTriang _ hT) (Pretriangulated.rot_of_distTriang _ hT')
    e₂ e₃ h
  let e : T ≅ T' := (Pretriangulated.rotCompInvRot.app T) ≪≫
    (Pretriangulated.invRotate C).mapIso eR ≪≫ (Pretriangulated.rotCompInvRot.app T').symm
  refine ⟨Triangle.π₁.mapIso e, ?_⟩
  have he₂ : e.hom.hom₂ = e₂.hom := by
    simp only [Functor.comp_obj, Functor.id_obj, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, triangleCategory_comp,
      TriangleMorphism.comp_hom₂, rotCompInvRot_hom_app_hom₂, invRotate_map_hom₂,
      isoTriangleOfIso₁₂_hom_hom₁, rotCompInvRot_inv_app_hom₂, Category.id_comp, e, eR]
    exact Category.comp_id e₂.hom
  simpa only [Functor.mapIso_hom, Triangle.π₁, he₂] using e.hom.comm₁

/-- The open counit and closed unit admit the induced outer Frobenius isomorphisms.
This asserts only the first two squares; it assumes no localization triangle and
asserts neither uniqueness nor equivariance of a connecting arrow.
Source: blueprint localization proof, Weil-structures paragraph, exchange mate equations
(blueprint: lem-sf-normalized-rational-recollement-weil-squares).
Proof: identify the normalized closed term and its unit with the actual rational
proper adjunction. The published proper exchange is the invertible mate of the inverse
pullback square. Its unit equation, followed by the pullback square and the image of
the middle Weil isomorphism, gives the closed square. Conjugate by the normalized
closed comparison. The independently proved normalized localization triangle and
exactness of Frobenius then give two distinguished triangles. Rotate them: the middle
Weil isomorphism and the closed isomorphism commute with the first arrow. Complete
them to an isomorphism of triangles and apply inverse rotation. Its first component
is the open isomorphism, and its first square is the asserted open counit equation.
This applies also to empty complements and zero objects -/
theorem sfNormalizedRationalRecollement_weil_squares
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∀ K : CategoryTheory.Endofunctor.IsoAlgebra (sfWeilFrobeniusPullback D l hl X₀ E),
      ∃ ac : ((sfWeilFrobeniusPullback D l hl X₀ E).obj (Q.openTerm.obj K.carrier) ≅
          Q.openTerm.obj K.carrier) ×
        ((sfWeilFrobeniusPullback D l hl X₀ E).obj (Q.closedTerm.obj K.carrier) ≅
          Q.closedTerm.obj K.carrier),
        (sfWeilFrobeniusPullback D l hl X₀ E).map (Q.counit.app K.carrier) ≫ K.str.hom =
          ac.1.hom ≫ Q.counit.app K.carrier ∧
        (sfWeilFrobeniusPullback D l hl X₀ E).map (Q.unit.app K.carrier) ≫ ac.2.hom =
          K.str.hom ≫ Q.unit.app K.carrier := by
  let : Fact (l ≠ D.p) := ⟨hl⟩
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let : IsSeparated (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  obtain ⟨_, _, _, _, _, _, _, ⟨s, hs⟩, _, _⟩ :=
    automorphismConstructibleStage_integral_rational D l E
      (D.geometricFiber X₀) (D.geometricFrobenius X₀)
  let G := sfWeilFrobeniusPullback D l hl X₀ E
  let : G.CommShift ℤ := s
  let : G.IsTriangulated := hs
  obtain ⟨e, he⟩ := sfNormalizedRationalRecollement_closed_comparison
    l E D hl X₀ Z₀ i₀ i _hi P Q _hP _hQ
  obtain ⟨ht, _⟩ := sfNormalizedRationalRecollement_triangle_orthogonality
    l E i (sfRecollementGeometricNoetherian D X₀) P Q _hP _hQ
  intro K
  obtain ⟨c, hc⟩ := closed_mate_square (fieldWeilProperAdj D l hl E i₀) G
    (sfWeilFrobeniusPullback D l hl Z₀ E) (fieldWeilPullSquare D l hl E i₀)
    (fieldWeilProperExchange D l hl E i₀) rfl K.carrier K.str
  obtain ⟨c', hc'⟩ := normalized_closed_square G Q.closedTerm _ Q.unit
    (fieldWeilProperAdj D l hl E i₀).unit e he K.carrier K.str c hc
  obtain ⟨δ, hδ⟩ := ht K.carrier
  obtain ⟨a, ha⟩ := open_square_of_closed_square
    (G.mapTriangle.obj (Triangle.mk (Q.counit.app K.carrier) (Q.unit.app K.carrier) δ))
    (Triangle.mk (Q.counit.app K.carrier) (Q.unit.app K.carrier) δ)
    (G.map_distinguished _ hδ) hδ K.str c' hc'
  exact ⟨(a, c'), ha, hc'⟩

end WeilConjectures
