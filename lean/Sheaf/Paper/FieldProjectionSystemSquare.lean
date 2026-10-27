module

public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FieldProjectionSystemData
import Sheaf.Paper.FieldProjectionTensorConstruction
import Sheaf.Paper.FieldProjectionProperSquare
import Sheaf.Paper.FieldProjectionOpenSquare

/-! # The scalar projection square on whole coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), projection square
(blueprint: lem-sp-field-projection-system-square).

The comparison is the recorded proper/open word. The tensor comparisons below are
fixed on signed K-flat representatives, before evaluation. No cartesian coefficient
square or faithfulness of derived evaluation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

attribute [local irreducible] coefficientMap HasDerivedCategory.standard
attribute [local irreducible] leftProjection leftProper leftOpen projectionTarget comparison proper

private theorem factor_with_symmetry
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : B ⥤ C) (J : A ⥤ B)
    {a b : C} {c d : B} {e f g : A} (s : a ⟶ b) (q : b ⟶ R.obj c)
    (v : c ≅ d) (w : c ⟶ J.obj e) (z : e ⟶ f) (y : f ⟶ g) :
    s ≫ (q ≫ R.map (w ≫ J.map z)) ≫ (J ⋙ R).map y =
      (s ≫ q ≫ R.map v.hom) ≫ R.map (v.inv ≫ w ≫ J.map (z ≫ y)) := by
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
  simp only [← R.map_comp, ← J.map_comp, Iso.hom_inv_id_assoc]

private theorem projection_factorization (t : ProjectionTensorComparisons P D)
    (E : Index P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :
    leftProjection P D t E c K W =
      leftProper P D t E c.g K
          ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
            ((D.operations E).openOp c.i)).obj W) ≫
        (SpTowerShriek.push P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry c.g)).map (leftOpen P D t E c K W) := by
  unfold leftProjection leftProper leftOpen SpTowerShriek.projection
  exact factor_with_symmetry
    (SpTowerShriek.push P.coefficients.l E.val (D.base E)
      ((D.operations E).geometry c.g))
    (SpTowerShriek.openD P.coefficients.l E.val (D.base E)
      ((D.operations E).openOp c.i)) _ _
    ((t.symmetry E c.Z).app _) _ _ _

private theorem counit_projection_naturality
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U)
    {E E' : B} (Q : A) (v : E ⟶ E') :
    T.map (Prod.mkHom (R.map v) (𝟙 Q)) ≫
        adj.homEquiv _ _ (t.app (R.obj E', Q) ≫
          U.map (Prod.mkHom (adj.counit.app E') (𝟙 (F.obj Q)))) =
      adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
          U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) ≫
        R.map (U.map (Prod.mkHom v (𝟙 (F.obj Q)))) := by
  apply adj.homEquiv_naturality_left_square
  have hn := t.naturality (Prod.mkHom (R.map v) (𝟙 Q))
  dsimp at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext
  · exact adj.counit.naturality v
  · simp

private theorem symmetric_projection_naturality
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U)
    (s : T ≅ CategoryTheory.Prod.swap _ _ ⋙ T) (z : U ≅ CategoryTheory.Prod.swap _ _ ⋙ U)
    {E E' : B} (Q : A) (v : E ⟶ E') :
    T.map (Prod.mkHom (𝟙 Q) (R.map v)) ≫
        (s.hom.app (Q, R.obj E') ≫
          adj.homEquiv _ _ (t.app (R.obj E', Q) ≫
            U.map (Prod.mkHom (adj.counit.app E') (𝟙 (F.obj Q)))) ≫
          R.map (z.hom.app (E', F.obj Q))) =
      (s.hom.app (Q, R.obj E) ≫
          adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
            U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) ≫
          R.map (z.hom.app (E, F.obj Q))) ≫
        R.map (U.map (Prod.mkHom (𝟙 (F.obj Q)) v)) := by
  have hs := s.hom.naturality (Prod.mkHom (𝟙 Q) (R.map v))
  have hz := z.hom.naturality (Prod.mkHom v (𝟙 (F.obj Q)))
  have hp := counit_projection_naturality adj T U t Q v
  dsimp only [Functor.comp_map, CategoryTheory.Prod.swap_map] at hs hz
  dsimp only [Functor.comp_obj, CategoryTheory.Prod.swap_obj, Functor.id_obj] at hp ⊢
  rw [← Category.assoc, ← Category.assoc, hs]
  simp only [Category.assoc]
  rw [reassoc_of% hp]
  rw [← R.map_comp, hz, R.map_comp]

private theorem proper_projection_naturality (t : ProjectionTensorComparisons P D)
    (E : Index P) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    {M N : SpTowerShriek.D P.coefficients.l E.val Z} (v : M ⟶ N) :
    (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Y).map
        (Prod.mkHom (𝟙 K) ((SpTowerShriek.push P.coefficients.l E.val
          (D.base E) ((D.operations E).geometry g)).map v)) ≫
        leftProper P D t E g K N =
      leftProper P D t E g K M ≫
        (SpTowerShriek.push P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry g)).map
            ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Z).map
              (Prod.mkHom (𝟙 _) v)) := by
  unfold leftProper
  exact symmetric_projection_naturality
    (SpTowerShriek.adjunction P.coefficients.l E.val (D.base E)
      ((D.operations E).geometry g))
    (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Y)
    (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Z)
    (((D.operations E).geometry g).tensorPullback).hom
    (t.symmetry E Y) (t.symmetry E Z) K v

private theorem tensor_map_comp_right
    {A B : Type*} [Category A] [Category B] (T : A × A ⥤ B)
    (K : A) {M N L : A} (a : M ⟶ N) (b : N ⟶ L) :
    T.map (Prod.mkHom (𝟙 K) (a ≫ b)) =
      T.map (Prod.mkHom (𝟙 K) a) ≫ T.map (Prod.mkHom (𝟙 K) b) := by
  rw [← T.map_comp]
  congr 1
  ext <;> simp

private theorem paste_projection_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (CA : A ⥤ C) (CB : B ⥤ D) (QA : B ⥤ A) (QB : D ⥤ C)
    (e : QA ⋙ CA ⟶ CB ⋙ QB)
    {a : A} {b c : B} {d d' r r' : D} {s s' s'' : C}
    (p : a ⟶ QA.obj b) (o : b ⟶ c) (beta : CB.obj c ⟶ r)
    (target : r ⟶ r') (mu : CB.obj b ⟶ d) (v : d ⟶ d') (o' : d' ⟶ r')
    (muY : CA.obj a ⟶ s) (u : s ⟶ s') (vY : s' ⟶ s'')
    (p' : s' ⟶ QB.obj d) (p'' : s'' ⟶ QB.obj d')
    (hp : CA.map p ≫ e.app b ≫ QB.map mu = muY ≫ u ≫ p')
    (ho : CB.map o ≫ beta ≫ target = mu ≫ v ≫ o')
    (hn : vY ≫ p'' = p' ≫ QB.map v) :
    CA.map (p ≫ QA.map o) ≫ e.app c ≫ QB.map beta ≫ QB.map target =
      muY ≫ u ≫ vY ≫ p'' ≫ QB.map o' := by
  have he := e.naturality o
  dsimp only [Functor.comp_map] at he
  simp only [CA.map_comp, Category.assoc]
  rw [reassoc_of% he]
  simp only [← QB.map_comp]
  rw [ho, QB.map_comp, QB.map_comp]
  rw [reassoc_of% hp]
  rw [reassoc_of% hn]

private theorem inverted_square {A : Type*} [Category A] {B : Type*} [Category B]
    (C : A ⥤ B) {a b : A} {c d : B} (p : a ⟶ b) (q : c ⟶ d)
    [IsIso p] [IsIso q] (r : C.obj b ⟶ d) (s : C.obj a ⟶ c)
    (h : C.map p ≫ r = s ≫ q) : r ≫ inv q = C.map (inv p) ≫ s := by
  apply (cancel_epi (C.map p)).mp
  simp only [← Category.assoc, ← C.map_comp, IsIso.hom_inv_id,
    C.map_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The projection square holds on whole systems, with its canonical corner maps.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-sp-field-projection-system-square).

Proof: Choose the common compactification j,p. Write the unsymmetrized projection
as Rp_*(gamma_A) q_A and b as Rp_*(beta) e. The proper square is the counit-defined
ringed exchange/tensor coherence (lem-weil-pbc-ringed-exchange-tensor-coherence),
applied to the identity coefficient morphisms and p, without cartesianness.
For the open square restrict both words to the open. The open-unit normalizations
make their restrictions the canonical scalar tensor and pullback comparisons
(lem-sf-open-tensor-normalization). On flat-term K-flat representatives both are
(m tensor x) tensor b mapped to (m tensor b) tensor (x tensor 1); full faithfulness
on the open image proves equality before evaluation. Paste the proper and open
squares using naturality of e at gamma and of q_B at beta. Precompose with the
source symmetry and apply proper image of the target symmetry. The signed total
models give the same sign (-1)^(ab) on both routes and coefficients have degree zero.
This gives precisely ProjectionSystemSquare. All constructions occur on the sequence
site (lem-coef-semilinear-derived-sections), not after level evaluation.
On the two-input finite-Tor etale-origin domain, scalar extension keeps Tor bounds,
constructibility and origin witnesses (det-sp-scalar-extension-functor). The tower
shriek-level theorem makes both projections invertible. Composing this very equality
with their inverses gives the inverted square; no equality is inferred from evaluations. -/
theorem field_projection_system_square
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f) :
    ∃ t : ProjectionTensorComparisons P D,
      ∀ (E F : Index P) (h : E ≤ F)
        (K : SpTowerShriek.D P.coefficients.l E.val Y)
        (W : SpTowerShriek.D P.coefficients.l E.val X),
        normalized P D E Y K → normalized P D E X W →
        ProjectionSystemSquare P D t h c K W ∧
          ∀ (hA : IsIso (leftProjection P D t E c K W))
            (hB : IsIso (leftProjection P D t F c ((D.scalars E F h Y).T.obj K)
              ((D.scalars E F h X).T.obj W))),
            @InvertedProjectionSystemSquare.{u} P D t E F h X Y f c K W hA hB := by
  obtain ⟨t⟩ := field_projection_tensor_construction P D
  refine ⟨t, ?_⟩
  intro E F h K W _hK _hW
  have hp := field_projection_proper_square P D t E F h c.g K
    ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
      ((D.operations E).openOp c.i)).obj W)
  have ho := field_projection_open_square P D t E F h c K W
  have hs : ProjectionSystemSquare P D t h c K W := by
    have hn := proper_projection_naturality P D t F c.g
      ((D.scalars E F h Y).T.obj K) ((D.openIso E F h c.i).hom.app W)
    have pasted := paste_projection_factors
      (D.scalars E F h Y).T (D.scalars E F h c.Z).T
      (SpTowerShriek.push P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry c.g))
      (SpTowerShriek.push P.coefficients.l F.val (D.base F)
        ((D.operations F).geometry c.g))
      (proper P D h c.g)
      (leftProper P D t E c.g K _)
      (leftOpen P D t E c K W)
      ((D.openIso E F h c.i).hom.app _)
      ((SpTowerShriek.openD P.coefficients.l F.val (D.base F)
        ((D.operations F).openOp c.i)).map (projectionTarget P D t h f K W).hom)
      (projectionTarget P D t h c.g K _).hom
      ((SpTowerShriek.tensor P.coefficients.l F.val (D.base F) c.Z).map
        (Prod.mkHom (𝟙 _) ((D.openIso E F h c.i).hom.app W)))
      (leftOpen P D t F c ((D.scalars E F h Y).T.obj K)
        ((D.scalars E F h X).T.obj W))
      ((t.scalar E F h Y).hom.app _)
      ((SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
        (Prod.mkHom (𝟙 _) ((proper P D h c.g).app _)))
      ((SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
        (Prod.mkHom (𝟙 _)
          ((SpTowerShriek.push P.coefficients.l F.val (D.base F)
            ((D.operations F).geometry c.g)).map ((D.openIso E F h c.i).hom.app W))))
      (leftProper P D t F c.g ((D.scalars E F h Y).T.obj K) _)
      (leftProper P D t F c.g ((D.scalars E F h Y).T.obj K) _)
      hp ho hn
    unfold ProjectionSystemSquare
    simp only [projection_factorization, comparison, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
    simp only [Functor.map_comp, tensor_map_comp_right, Category.assoc] at pasted ⊢
    simpa only [Functor.comp_obj, CategoryTheory.Prod.swap_obj, Functor.id_obj]
      using pasted
  refine ⟨hs, ?_⟩
  intro hA hB
  have := hA
  have := hB
  have he := inverted_square (D.scalars E F h Y).T
    (leftProjection P D t E c K W)
    (leftProjection P D t F c ((D.scalars E F h Y).T.obj K)
      ((D.scalars E F h X).T.obj W))
    ((comparison P D h c).app _ ≫
      (SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).map
        (projectionTarget P D t h f K W).hom)
    ((t.scalar E F h Y).hom.app _ ≫
      (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
        (Prod.mkHom (𝟙 _) ((comparison P D h c).app W)))
    (by simpa only [ProjectionSystemSquare, Functor.comp_obj,
      CategoryTheory.Prod.swap_obj, Functor.id_obj, Category.assoc] using hs)
  simpa only [InvertedProjectionSystemSquare, Functor.comp_obj,
    CategoryTheory.Prod.swap_obj, Functor.id_obj, Category.assoc] using he

end AlgebraicGeometry.ProEtale.FieldShriekSystem
