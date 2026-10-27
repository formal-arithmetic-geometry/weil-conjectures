module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Free
public import Mathlib.Data.PNat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Transformations through specified exact-functor realizations

Source: Stacks Project, Tag 04VG, and Mathlib's natural-transformation localization
universal property, `CategoryTheory.Localization.Predicate`, `liftNatTrans_app` and
`natTrans_ext`. The degreewise and iterated-factor refinements are the agent argument
in the DAG. (blueprint: lem-trf-exact-evaluation-transformation-descent)

`FreeMagma (Option ℕ+)` supplies parenthesized words: `of none` is the empty word,
`of (some r)` is H_r, and `mul P R` means first P, then R. Evaluation words have G
outermost. The two expression types specify precisely the finite pastings in the node;
their interpretations retain the given derived realizations and compositors.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uM vM wM uB vB wB

open CategoryTheory Limits

namespace CategoryTheory.ExactEvaluationDescent

variable {M : Type uM} [Category.{vM} M] [Abelian M] [HasDerivedCategory.{wM} M]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (G : M ⥤ B) [G.Additive]
  (H : ℕ+ → M ⥤ M) [∀ r, (H r).Additive]
  (V : DerivedCategory M ⥤ DerivedCategory B)
  (Q : ℕ+ → DerivedCategory M ⥤ DerivedCategory M)
  (v : DerivedCategory.Q ⋙ V ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (e : ∀ r, DerivedCategory.Q ⋙ Q r ≅
    (H r).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

/-- Interpret a fixed word of the H_r termwise, including the empty word.
Source: Tag 04VG, DAG proof step 4.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def chainWord : FreeMagma (Option ℕ+) → CochainComplex M ℤ ⥤ CochainComplex M ℤ
  | .of none => 𝟭 _
  | .of (some r) => (H r).mapHomologicalComplex (.up ℤ)
  | .mul P R => chainWord P ⋙ chainWord R

/-- Interpret the same word using the specified Q_r, rather than chosen standard lifts.
Source: Tag 04VG, DAG proof step 4.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def derivedWord : FreeMagma (Option ℕ+) → DerivedCategory M ⥤ DerivedCategory M
  | .of none => 𝟭 _
  | .of (some r) => Q r
  | .mul P R => derivedWord P ⋙ derivedWord R

/-- Recursively specified factorization a_FE = D(F)(a_E) followed by a_F at C(E).
Source: Tag 04VG, DAG proof steps 2 and 4.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def wordFactors (P : FreeMagma (Option ℕ+)) :
    DerivedCategory.Q ⋙ derivedWord Q P ≅ chainWord H P ⋙ DerivedCategory.Q :=
  match P with
  | .of none => (Functor.rightUnitor _).trans (Functor.leftUnitor _).symm
  | .of (some r) => e r
  | .mul P R =>
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (wordFactors P) (derivedWord Q R) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (chainWord H P) (wordFactors R) ≪≫
        (Functor.associator _ _ _).symm

/-- The evaluation factorization; at the one-letter word it is exactly w_r.
Source: Tag 04VG, DAG proof steps 2 and 4.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def evaluationFactors (P : FreeMagma (Option ℕ+)) :
    DerivedCategory.Q ⋙ (derivedWord Q P ⋙ V) ≅
      (chainWord H P ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (wordFactors H Q e P) V ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (chainWord H P) v ≪≫
    (Functor.associator _ _ _).symm

/-- The degreewise alpha map, with the canonical termwise-composition comparison.
Source: Tag 04VG, DAG proof step 1; Mathlib `mapHomologicalComplexCompIso`.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def alphaChain (r : ℕ+) (α : G ⟶ H r ⋙ G) :
    G.mapHomologicalComplex (.up ℤ) ⟶
      (H r).mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex α (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H r ⋙ G)) (.up ℤ)).inv

/-- The actual localization construction of alpha^D; alpha is never inverted.
Source: Tag 04VG and `Localization.liftNatTrans`, DAG proof step 3.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def transformation (r : ℕ+) (α : G ⟶ H r ⋙ G) : V ⟶ Q r ⋙ V :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso M (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) V := ⟨v⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso M (.up ℤ))
      (((H r).mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q) (Q r ⋙ V) := ⟨evaluationFactors G H V Q v e (.of (some r))⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso M (.up ℤ)) _ _ V (Q r ⋙ V)
    (Functor.whiskerRight (alphaChain G H r α) DerivedCategory.Q)

variable (T : ∀ m : ℕ+, H m ⋙ H 1 ≅ H (m + 1))
  (t : ∀ m : ℕ+, Q m ⋙ Q 1 ≅ Q (m + 1))

/-- Finite endomorphism pastings using precisely the specified compositors, their inverses,
identities, composition, and functor images, with structural reassociation and unit maps.
Words use the existing `FreeMagma` type.
Source: Tag 04VG, DAG proof steps 4--6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
inductive EndExpression : FreeMagma (Option ℕ+) → FreeMagma (Option ℕ+) → Type
  | compositor (m : ℕ+) :
      EndExpression (.mul (.of (some m)) (.of (some 1))) (.of (some (m + 1)))
  | compositorInv (m : ℕ+) :
      EndExpression (.of (some (m + 1))) (.mul (.of (some m)) (.of (some 1)))
  | id (P : FreeMagma (Option ℕ+)) : EndExpression P P
  | comp {P R S : FreeMagma (Option ℕ+)} :
      EndExpression P R → EndExpression R S → EndExpression P S
  | input (W : FreeMagma (Option ℕ+)) {P R : FreeMagma (Option ℕ+)} :
      EndExpression P R → EndExpression (.mul W P) (.mul W R)
  | output {P R : FreeMagma (Option ℕ+)} : EndExpression P R →
      (W : FreeMagma (Option ℕ+)) → EndExpression (.mul P W) (.mul R W)
  | assoc (P R S : FreeMagma (Option ℕ+)) :
      EndExpression (.mul (.mul P R) S) (.mul P (.mul R S))
  | assocInv (P R S : FreeMagma (Option ℕ+)) :
      EndExpression (.mul P (.mul R S)) (.mul (.mul P R) S)
  | leftUnit (P : FreeMagma (Option ℕ+)) : EndExpression (.mul (.of none) P) P
  | leftUnitInv (P : FreeMagma (Option ℕ+)) : EndExpression P (.mul (.of none) P)
  | rightUnit (P : FreeMagma (Option ℕ+)) : EndExpression (.mul P (.of none)) P
  | rightUnitInv (P : FreeMagma (Option ℕ+)) : EndExpression P (.mul P (.of none))

/-- Interpret an endomorphism pasting as an actual chain transformation.
Source: Tag 04VG, DAG proof steps 1 and 6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EndExpression.chain {P R : FreeMagma (Option ℕ+)} :
    EndExpression P R → (chainWord H P ⟶ chainWord H R)
  | .compositor m => (Functor.mapHomologicalComplexCompIso (T m) (.up ℤ)).hom
  | .compositorInv m => (Functor.mapHomologicalComplexCompIso (T m) (.up ℤ)).inv
  | .id _ => 𝟙 _
  | .comp a b => a.chain ≫ b.chain
  | .input W a => Functor.whiskerLeft (chainWord H W) (a.chain)
  | .output a W => Functor.whiskerRight (a.chain) (chainWord H W)
  | .assoc P R S =>
      (Functor.associator (chainWord H P) (chainWord H R) (chainWord H S)).hom
  | .assocInv P R S =>
      (Functor.associator (chainWord H P) (chainWord H R) (chainWord H S)).inv
  | .leftUnit P => (Functor.leftUnitor (chainWord H P)).hom
  | .leftUnitInv P => (Functor.leftUnitor (chainWord H P)).inv
  | .rightUnit P => (Functor.rightUnitor (chainWord H P)).hom
  | .rightUnitInv P => (Functor.rightUnitor (chainWord H P)).inv

/-- Interpret an endomorphism pasting using the supplied t_m.
Source: Tag 04VG, DAG proof steps 5 and 6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EndExpression.derived {P R : FreeMagma (Option ℕ+)} :
    EndExpression P R → (derivedWord Q P ⟶ derivedWord Q R)
  | .compositor m => (t m).hom
  | .compositorInv m => (t m).inv
  | .id _ => 𝟙 _
  | .comp a b => a.derived ≫ b.derived
  | .input W a => Functor.whiskerLeft (derivedWord Q W) (a.derived)
  | .output a W => Functor.whiskerRight (a.derived) (derivedWord Q W)
  | .assoc P R S =>
      (Functor.associator (derivedWord Q P) (derivedWord Q R) (derivedWord Q S)).hom
  | .assocInv P R S =>
      (Functor.associator (derivedWord Q P) (derivedWord Q R) (derivedWord Q S)).inv
  | .leftUnit P => (Functor.leftUnitor (derivedWord Q P)).hom
  | .leftUnitInv P => (Functor.leftUnitor (derivedWord Q P)).inv
  | .rightUnit P => (Functor.rightUnitor (derivedWord Q P)).hom
  | .rightUnitInv P => (Functor.rightUnitor (derivedWord Q P)).inv

/-- Finite evaluation pastings generated by arbitrary alpha, with endomorphism pastings
sent through G, and with identities, composition, and all well-typed input functor images.
Source: Tag 04VG, DAG proof steps 4--6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
inductive EvaluationExpression : FreeMagma (Option ℕ+) → FreeMagma (Option ℕ+) →
    Type (max uM vM uB vB)
  | alpha (r : ℕ+) (α : G ⟶ H r ⋙ G) :
      EvaluationExpression (.of none) (.of (some r))
  | id (P : FreeMagma (Option ℕ+)) : EvaluationExpression P P
  | comp {P R S : FreeMagma (Option ℕ+)} :
      EvaluationExpression P R → EvaluationExpression R S → EvaluationExpression P S
  | input (W : FreeMagma (Option ℕ+)) {P R : FreeMagma (Option ℕ+)} :
      EvaluationExpression P R → EvaluationExpression (.mul W P) (.mul W R)
  | evaluation {P R : FreeMagma (Option ℕ+)} : EndExpression P R → EvaluationExpression P R

/-- Interpret an evaluation pasting on complexes, using Mathlib's degreewise maps.
Source: Tag 04VG, DAG proof steps 1 and 6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EvaluationExpression.chain {P R : FreeMagma (Option ℕ+)} :
    EvaluationExpression G H P R →
      (chainWord H P ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
        chainWord H R ⋙ G.mapHomologicalComplex (.up ℤ))
  | .alpha r α => alphaChain G H r α
  | .id _ => 𝟙 _
  | .comp a b => a.chain ≫ b.chain
  | .input W a => Functor.whiskerLeft (chainWord H W) (a.chain)
  | .evaluation a => Functor.whiskerRight (a.chain H T) (G.mapHomologicalComplex (.up ℤ))

/-- Interpret evaluation pastings with alpha^D and the supplied compositors.
Source: Tag 04VG, DAG proof steps 3, 5 and 6.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EvaluationExpression.derived {P R : FreeMagma (Option ℕ+)} :
    EvaluationExpression G H P R → (derivedWord Q P ⋙ V ⟶ derivedWord Q R ⋙ V)
  | .alpha r α => transformation G H V Q v e r α
  | .id _ => 𝟙 _
  | .comp a b => a.derived ≫ b.derived
  | .input W a => Functor.whiskerLeft (derivedWord Q W) (a.derived)
  | .evaluation a => Functor.whiskerRight (a.derived Q t) V

/-- Every word preserves a Q_r-stable full subcategory.
Source: Tag 04VG, DAG proof step 7.
(blueprint: lem-trf-exact-evaluation-transformation-descent)
Proof: Induct on the parenthesized word. The empty word preserves the property by
identity; a letter uses hS; for a product apply the induction hypotheses successively. -/
theorem word_preserves (S : ObjectProperty (DerivedCategory M))
    (hS : ∀ r X, S X → S ((Q r).obj X)) (P : FreeMagma (Option ℕ+)) :
    ∀ X, S X → S ((derivedWord Q P).obj X) := by
  induction P using FreeMagma.rec with
  | of x => cases x with
    | none => exact fun _ h => h
    | some r => exact hS r
  | mul P R hP hR => exact fun X h => hR _ (hP X h)

/-- The actual restriction of a derived word to any stable full subcategory.
Source: Tag 04VG, DAG proof step 7; Mathlib `ObjectProperty.lift`.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def restrictedWord (S : ObjectProperty (DerivedCategory M))
    (hS : ∀ r X, S X → S ((Q r).obj X)) (P : FreeMagma (Option ℕ+)) :
    S.FullSubcategory ⥤ S.FullSubcategory :=
  S.lift (S.ι ⋙ derivedWord Q P) (fun X => word_preserves Q S hS P X.obj X.property)

/-- Restrict an endomorphism pasting; fullness retains its actual component arrows.
Source: Tag 04VG, DAG proof step 7.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EndExpression.restrict (S : ObjectProperty (DerivedCategory M))
    (hS : ∀ r X, S X → S ((Q r).obj X)) {P R : FreeMagma (Option ℕ+)}
    (a : EndExpression P R) : restrictedWord Q S hS P ⟶ restrictedWord Q S hS R where
  app X := ObjectProperty.homMk ((a.derived Q t).app X.obj)
  naturality _ _ f := ObjectProperty.hom_ext S ((a.derived Q t).naturality f.hom)

/-- Restriction of an evaluation pasting is precomposition with the inclusion; its
codomain remains D(B), with no stability condition on V.
Source: Tag 04VG, DAG proof step 7.
(blueprint: lem-trf-exact-evaluation-transformation-descent) -/
def EvaluationExpression.restrict (S : ObjectProperty (DerivedCategory M))
    {P R : FreeMagma (Option ℕ+)} (a : EvaluationExpression G H P R) :
    S.ι ⋙ (derivedWord Q P ⋙ V) ⟶ S.ι ⋙ (derivedWord Q R ⋙ V) :=
  Functor.whiskerLeft S.ι (a.derived G H V Q v e t)

/-- Descent through fixed exact-functor realizations, including preservation of every
finite well-typed chain-map pasting equation and restriction to full subcategories.

Source: Stacks Project, Tag 04VG, together with the natural-transformation enhancement
in Mathlib `Localization.liftNatTrans`, `liftNatTrans_app`, and `natTrans_ext`.
(blueprint: lem-trf-exact-evaluation-transformation-descent)

Proof:
1. Naturality of alpha at each differential is the chain-map equation; at each component
   of a chain map it gives naturality of `NatTrans.mapHomologicalComplex`.
2. `lem-weil-pbc-exact-functor-derived-factorization` says G and H_r preserve
   quasi-isomorphisms.
   Their words do too. Composing v with V(e_r) gives the specified natural factor w_r.
3. Apply clause (2) of `lem-weil-pbc-localization-universal-property`,
   with source factor v and target factor w_r. Its formula is exactly the conjugation
   below; full faithfulness gives uniqueness. Naturality is for every derived arrow.
   For an inverse localized quasi-isomorphism multiply its naturality square by the
   inverses of the functor images; alpha itself need not be invertible.
4. For words, recursively compose the factors. Identity pastings give identities and
   composition cancels the middle inverse factor. This gives conjugation for composites.
5. Input whiskering uses naturality of the descended transformation at the input word
   factor; output whiskering uses naturality of the output word factor at the chain map.
   The compositor hypothesis identifies t_m with the conjugate of C(T_m); inversion
   supplies the inverse-compositor case.
6. Induction on expressions, using steps 3--5, gives both normalization formulas.
   Equal chain maps give equal conjugates on every QK. The equality-detection clause
   of `lem-weil-pbc-localization-universal-property` gives equality of transformations.
7. Stability restricts every Q-word. Fullness retains components with endpoints in S;
   ambient naturality handles every arrow in S. Precomposition and faithful inclusion
   preserve the established equalities. No representative is required to lie in S.
-/
theorem exact_evaluation_transformation_descent
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [∀ r, PreservesFiniteLimits (H r)] [∀ r, PreservesFiniteColimits (H r)]
    [V.CommShift ℤ] [V.IsTriangulated]
    [∀ r, (Q r).CommShift ℤ] [∀ r, (Q r).IsTriangulated] :
    (∀ (r : ℕ+) (α : G ⟶ H r ⋙ G) (K : CochainComplex M ℤ) (i : ℤ),
      ((alphaChain G H r α).app K).f i = α.app (K.X i)) ∧
    (∀ (r : ℕ+) (α : G ⟶ H r ⋙ G),
      ∃! δ : V ⟶ Q r ⋙ V, ∀ K : CochainComplex M ℤ,
        δ.app (DerivedCategory.Q.obj K) = v.hom.app K ≫
          DerivedCategory.Q.map ((alphaChain G H r α).app K) ≫
          (evaluationFactors G H V Q v e (.of (some r))).inv.app K) ∧
    (∀ {F F' : DerivedCategory M ⥤ DerivedCategory B} (a b : F ⟶ F'),
      (∀ K : CochainComplex M ℤ, a.app (DerivedCategory.Q.obj K) =
        b.app (DerivedCategory.Q.obj K)) ↔ a = b) ∧
    (∀ {F F' : DerivedCategory M ⥤ DerivedCategory M} (a b : F ⟶ F'),
      (∀ K : CochainComplex M ℤ, a.app (DerivedCategory.Q.obj K) =
        b.app (DerivedCategory.Q.obj K)) ↔ a = b) ∧
    (∀ (T : ∀ m : ℕ+, H m ⋙ H 1 ≅ H (m + 1))
      (t : ∀ m : ℕ+, Q m ⋙ Q 1 ≅ Q (m + 1)),
      (∀ (m : ℕ+) (K : CochainComplex M ℤ),
        (t m).hom.app (DerivedCategory.Q.obj K) ≫ (e (m + 1)).hom.app K =
          (Q 1).map ((e m).hom.app K) ≫
          (e 1).hom.app (((H m).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (T m) (.up ℤ)).hom.app K)) →
      (∀ {P R : FreeMagma (Option ℕ+)} (a : EndExpression P R)
        (K : CochainComplex M ℤ),
        (a.derived Q t).app (DerivedCategory.Q.obj K) =
          (wordFactors H Q e P).hom.app K ≫ DerivedCategory.Q.map ((a.chain H T).app K) ≫
          (wordFactors H Q e R).inv.app K) ∧
      (∀ {P R : FreeMagma (Option ℕ+)} (a : EvaluationExpression G H P R)
        (K : CochainComplex M ℤ),
        (a.derived G H V Q v e t).app (DerivedCategory.Q.obj K) =
          (evaluationFactors G H V Q v e P).hom.app K ≫
          DerivedCategory.Q.map ((a.chain G H T).app K) ≫
          (evaluationFactors G H V Q v e R).inv.app K) ∧
      (∀ {P R : FreeMagma (Option ℕ+)} (a b : EndExpression P R),
        (∀ K : CochainComplex M ℤ, (a.chain H T).app K = (b.chain H T).app K) →
          a.derived Q t = b.derived Q t) ∧
      (∀ {P R : FreeMagma (Option ℕ+)} (a b : EvaluationExpression G H P R),
        (∀ K : CochainComplex M ℤ, (a.chain G H T).app K = (b.chain G H T).app K) →
          a.derived G H V Q v e t = b.derived G H V Q v e t) ∧
      (∀ (S : ObjectProperty (DerivedCategory M))
        (hS : ∀ r X, S X → S ((Q r).obj X)),
        (∀ {P R : FreeMagma (Option ℕ+)} (a b : EndExpression P R),
          (∀ K : CochainComplex M ℤ, (a.chain H T).app K = (b.chain H T).app K) →
            a.restrict Q t S hS = b.restrict Q t S hS) ∧
        (∀ {P R : FreeMagma (Option ℕ+)} (a b : EvaluationExpression G H P R),
          (∀ K : CochainComplex M ℤ, (a.chain G H T).app K = (b.chain G H T).app K) →
            a.restrict G H V Q v e t S = b.restrict G H V Q v e t S))) := by
  have hextB {F F' : DerivedCategory M ⥤ DerivedCategory B} (a b : F ⟶ F') :
      (∀ K : CochainComplex M ℤ, a.app (DerivedCategory.Q.obj K) =
        b.app (DerivedCategory.Q.obj K)) ↔ a = b :=
    ⟨Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso M (.up ℤ)), fun h _ => by rw [h]⟩
  have hextM {F F' : DerivedCategory M ⥤ DerivedCategory M} (a b : F ⟶ F') :
      (∀ K : CochainComplex M ℤ, a.app (DerivedCategory.Q.obj K) =
        b.app (DerivedCategory.Q.obj K)) ↔ a = b :=
    ⟨Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso M (.up ℤ)), fun h _ => by rw [h]⟩
  have hα (r : ℕ+) (α : G ⟶ H r ⋙ G) (K : CochainComplex M ℤ) :
      (transformation G H V Q v e r α).app (DerivedCategory.Q.obj K) =
        v.hom.app K ≫ DerivedCategory.Q.map ((alphaChain G H r α).app K) ≫
          (evaluationFactors G H V Q v e (.of (some r))).inv.app K := by
    dsimp [transformation]
    rw [Localization.liftNatTrans_app]
    rfl
  refine ⟨?_, ?_, hextB, hextM, ?_⟩
  · intro r α K i
    change α.app (K.X i) ≫ 𝟙 _ = α.app (K.X i)
    exact Category.comp_id _
  · intro r α
    refine ⟨transformation G H V Q v e r α, hα r α, ?_⟩
    intro δ hδ
    exact (hextB _ _).mp (fun K => (hδ K).trans (hα r α K).symm)
  · intro T t ht
    have hEnd {P R : FreeMagma (Option ℕ+)} (a : EndExpression P R) :
        ∀ K : CochainComplex M ℤ,
          (a.derived Q t).app (DerivedCategory.Q.obj K) ≫
              (wordFactors H Q e R).hom.app K =
            (wordFactors H Q e P).hom.app K ≫
              DerivedCategory.Q.map ((a.chain H T).app K) := by
      induction a with
      | compositor m =>
        intro K
        simpa [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Category.id_comp, Category.comp_id] using ht m K
      | compositorInv m =>
        intro K
        change (t m).inv.app (DerivedCategory.Q.obj K) ≫
            (wordFactors H Q e (.mul (.of (some m)) (.of (some 1)))).hom.app K =
          (e (m + 1)).hom.app K ≫ DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (T m) (.up ℤ)).inv.app K)
        apply (cancel_mono (DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (T m) (.up ℤ)).hom.app K))).mp
        have h := ht m K
        dsimp [wordFactors, chainWord, derivedWord]
        simp only [Category.id_comp, Category.comp_id]
        simp only [Category.assoc] at h ⊢
        rw [← h]
        simp [← Functor.map_comp]
      | id P => intro K; simp [EndExpression.derived, EndExpression.chain, Functor.map_id,
          Category.id_comp, Category.comp_id]
      | comp a b ha hb =>
        intro K
        simp only [EndExpression.derived, EndExpression.chain, NatTrans.comp_app,
          Functor.map_comp, Category.assoc]
        rw [hb, ← Category.assoc, ha, Category.assoc]
      | input W a ha =>
        intro K
        dsimp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord]
        simp only [Category.id_comp, Category.comp_id, Category.assoc]
        rw [← (a.derived Q t).naturality_assoc, ha]
      | output a W ha =>
        intro K
        dsimp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord]
        simp only [Category.id_comp, Category.comp_id, Category.assoc]
        rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp, Category.assoc]
        congr 1
        exact (wordFactors H Q e W).hom.naturality _
      | assoc P R S =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | assocInv P R S =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | leftUnit P =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | leftUnitInv P =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | rightUnit P =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | rightUnitInv P =>
        intro K
        simp [EndExpression.derived, EndExpression.chain, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
    have heval_mul (W P : FreeMagma (Option ℕ+)) (K : CochainComplex M ℤ) :
        (evaluationFactors G H V Q v e (.mul W P)).hom.app K =
          (derivedWord Q P ⋙ V).map ((wordFactors H Q e W).hom.app K) ≫
            (evaluationFactors G H V Q v e P).hom.app ((chainWord H W).obj K) := by
      dsimp [evaluationFactors, wordFactors, chainWord, derivedWord]
      simp [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
    have hEval {P R : FreeMagma (Option ℕ+)}
        (a : EvaluationExpression G H P R) : ∀ K : CochainComplex M ℤ,
          (a.derived G H V Q v e t).app (DerivedCategory.Q.obj K) ≫
              (evaluationFactors G H V Q v e R).hom.app K =
            (evaluationFactors G H V Q v e P).hom.app K ≫
              DerivedCategory.Q.map ((a.chain G H T).app K) := by
      induction a with
      | alpha r α =>
        intro K
        dsimp only [EvaluationExpression.derived, EvaluationExpression.chain]
        rw [hα]
        simp only [Category.assoc, Iso.inv_hom_id_app]
        simp [evaluationFactors, wordFactors, chainWord, derivedWord,
          Functor.map_id, Category.id_comp, Category.comp_id]
      | id P =>
        intro K
        simp [EvaluationExpression.derived, EvaluationExpression.chain, Functor.map_id,
          Category.id_comp, Category.comp_id]
      | comp a b ha hb =>
        intro K
        simp only [EvaluationExpression.derived, EvaluationExpression.chain, NatTrans.comp_app,
          Functor.map_comp, Category.assoc]
        rw [hb, ← Category.assoc, ha, Category.assoc]
      | input W a ha =>
        intro K
        dsimp only [EvaluationExpression.derived, EvaluationExpression.chain,
          Functor.whiskerLeft_app]
        rw [heval_mul, heval_mul]
        simp only [Category.assoc]
        rw [← (a.derived G H V Q v e t).naturality_assoc]
        congr 1
        exact ha _
      | evaluation a =>
        intro K
        dsimp [EvaluationExpression.derived, EvaluationExpression.chain, evaluationFactors,
          chainWord, derivedWord]
        simp only [Category.id_comp, Category.comp_id, Category.assoc]
        rw [← Category.assoc, ← Functor.map_comp, hEnd a, Functor.map_comp,
          Category.assoc]
        congr 1
        exact v.hom.naturality _
    have hEnd' {P R : FreeMagma (Option ℕ+)} (a : EndExpression P R)
        (K : CochainComplex M ℤ) :
        (a.derived Q t).app (DerivedCategory.Q.obj K) =
          (wordFactors H Q e P).hom.app K ≫ DerivedCategory.Q.map ((a.chain H T).app K) ≫
            (wordFactors H Q e R).inv.app K := by
      rw [← Category.assoc, ← hEnd a K]
      simp [Category.assoc]
    have hEval' {P R : FreeMagma (Option ℕ+)} (a : EvaluationExpression G H P R)
        (K : CochainComplex M ℤ) :
        (a.derived G H V Q v e t).app (DerivedCategory.Q.obj K) =
          (evaluationFactors G H V Q v e P).hom.app K ≫
            DerivedCategory.Q.map ((a.chain G H T).app K) ≫
            (evaluationFactors G H V Q v e R).inv.app K := by
      rw [← Category.assoc, ← hEval a K]
      simp [Category.assoc]
    have heqEnd {P R : FreeMagma (Option ℕ+)} (a b : EndExpression P R)
        (h : ∀ K : CochainComplex M ℤ, (a.chain H T).app K = (b.chain H T).app K) :
        a.derived Q t = b.derived Q t := by
      apply (hextM _ _).mp
      intro K
      rw [hEnd', hEnd', h K]
    have heqEval {P R : FreeMagma (Option ℕ+)} (a b : EvaluationExpression G H P R)
        (h : ∀ K : CochainComplex M ℤ, (a.chain G H T).app K = (b.chain G H T).app K) :
        a.derived G H V Q v e t = b.derived G H V Q v e t := by
      apply (hextB _ _).mp
      intro K
      rw [hEval', hEval', h K]
    refine ⟨hEnd', hEval', heqEnd, heqEval, ?_⟩
    intro S hS
    constructor
    · intro P R a b h
      ext X
      exact congr_app (heqEnd a b h) X.obj
    · intro P R a b h
      exact congrArg (Functor.whiskerLeft S.ι) (heqEval a b h)


end CategoryTheory.ExactEvaluationDescent
