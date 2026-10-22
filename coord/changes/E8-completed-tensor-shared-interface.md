# CategoryTheory.ConstantCompletion completed tensor interface relocation

## Reason

The two categorical coherence lemmas and the ordinary derived-pullback lemma must import
these shared definitions without importing the theorem that uses them. Move the existing
interface to CompletedTensorUnitInsertionData and publicly reexport it from the item.
Every interface declaration signature and body is byte-for-byte unchanged; only the docstring
blueprint annotations now identify the data node. No target meaning changes.

## Old

In lean/Sheaf/Paper/CompletedTensorUnitInsertion.lean:

```lean
section Constraints

variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [SymmetricCategory B]

/-- The left insertion of the actual reflector unit, after tensor and completion.
Source: Stacks 099G, proof steps 1--2
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def tensorInsertLeft (T : B ⥤ B) (η : 𝟭 B ⟶ T) (V W : B) :=
  T.map (η.app V ⊗ₘ 𝟙 W)

/-- The right insertion of the actual reflector unit, after tensor and completion.
Source: Stacks 099G, proof step 2
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def tensorInsertRight (T : B ⥤ B) (η : 𝟭 B ⟶ T) (V W : B) :=
  T.map (𝟙 V ⊗ₘ η.app W)

/-- The completed tensor constraints, with their exact insertion normalization.
A monoidal structure supplies naturality, the pentagon and triangle; a symmetric
structure supplies involutivity and both hexagons. The equations below fix their
underlying arrows, including both unitors, on the full complete subcategory.
Source: Stacks 099G, proof steps 5--6
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedConstraintModel (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hLeft : ∀ V W : B, IsIso (tensorInsertLeft T η V W))
    (hRight : ∀ V W : B, IsIso (tensorInsertRight T η V W))
    (hη : ∀ V : P.FullSubcategory, IsIso (η.app V.obj))
    (m : MonoidalCategory P.FullSubcategory)
    (s : @SymmetricCategory P.FullSubcategory _ m) : Prop :=
  letI := hLeft
  letI := hRight
  letI (V : P.FullSubcategory) := hη V
  letI := m
  letI := s
  (∀ V W : P.FullSubcategory, (V ⊗ W).obj = T.obj (V.obj ⊗ W.obj)) ∧
  (∀ (V W V' W' : P.FullSubcategory) (f : V ⟶ V') (g : W ⟶ W'),
    HEq (f ⊗ₘ g).hom (T.map (f.hom ⊗ₘ g.hom))) ∧
  (𝟙_ P.FullSubcategory).obj = T.obj (𝟙_ B) ∧
  (∀ V W Z : P.FullSubcategory,
    HEq (α_ V W Z).hom.hom
      (inv (tensorInsertLeft T η (V.obj ⊗ W.obj) Z.obj) ≫
        T.map (α_ V.obj W.obj Z.obj).hom ≫
          tensorInsertRight T η V.obj (W.obj ⊗ Z.obj))) ∧
  (∀ V W : P.FullSubcategory,
    HEq (β_ V W).hom.hom (T.map (β_ V.obj W.obj).hom)) ∧
  (∀ V : P.FullSubcategory,
    HEq (λ_ V).hom.hom
      (inv (tensorInsertLeft T η (𝟙_ B) V.obj) ≫
        T.map (λ_ V.obj).hom ≫ inv (η.app V.obj))) ∧
  (∀ V : P.FullSubcategory,
    HEq (ρ_ V).hom.hom
      (inv (tensorInsertRight T η V.obj (𝟙_ B)) ≫
        T.map (ρ_ V.obj).hom ≫ inv (η.app V.obj)))

variable {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [SymmetricCategory E]

/-- The completed inverse image, using fullness and the reflector's complete output.
Source: Stacks 099N, proof step 3
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def completeInverse (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T' : E ⥤ E) (hT' : ∀ V : E, P' (T'.obj V)) :
    P.FullSubcategory ⥤ P'.FullSubcategory :=
  ObjectProperty.lift P' (P.ι ⋙ L ⋙ T') (fun V ↦ hT' (L.obj V.obj))

/-- Associativity, symmetry and both tensor-unit equations for the completed comparison.
The oplax monoidal laws assert the actual associativity and unitor equations. Its
cotensorator and unit are exactly the separately normalized completed isomorphisms;
the last equation is compatibility with the specified completed symmetry.
Source: Stacks 099G and 07A4, proof steps 8--9
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedPullbackCoherence (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E) (hT' : ∀ V : E, P' (T'.obj V))
    (μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T')
    (ec : (L ⋙ T').obj (T.obj (𝟙_ B)) ≅ T'.obj (𝟙_ E))
    (m : MonoidalCategory P.FullSubcategory)
    (m' : MonoidalCategory P'.FullSubcategory)
    (s : @SymmetricCategory P.FullSubcategory _ m)
    (s' : @SymmetricCategory P'.FullSubcategory _ m') : Prop :=
  letI := m
  letI := m'
  letI := s
  letI := s'
  ∃ o : (completeInverse P P' L T' hT').OplaxMonoidal,
    (∀ V W : P.FullSubcategory,
      HEq (o.δ V W).hom
        (μc.hom.app (V.obj, W.obj))) ∧
    HEq (o.η).hom ec.hom ∧
    (∀ V W : P.FullSubcategory,
      o.δ V W ≫
          (β_ ((completeInverse P P' L T' hT').obj V)
            ((completeInverse P P' L T' hT').obj W)).hom =
        (completeInverse P P' L T' hT').map (β_ V W).hom ≫
          o.δ W V)

/-- All three insertions and the unique normalized coherent completed comparison.
The completed constraints are specified by `CompletedConstraintModel`, so coherence
refers to completion of the ordinary constraints, including completion of the unit.
Source: Stacks 099G, 099M, 099N and 07A4, proof steps 1--9
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedTensorAssertions (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E)
    (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (μ : tensor B ⋙ L ≅ (L.prod L) ⋙ tensor E) : Prop :=
  ∃ (_hT : ∀ V : B, P (T.obj V)) (hT' : ∀ V : E, P' (T'.obj V))
    (hη : ∀ V : P.FullSubcategory, IsIso (η.app V.obj))
    (hη' : ∀ V : P'.FullSubcategory, IsIso (η'.app V.obj))
    (hLeft : ∀ V W : B, IsIso (tensorInsertLeft T η V W))
    (hRight : ∀ V W : B, IsIso (tensorInsertRight T η V W))
    (hLeft' : ∀ V W : E, IsIso (tensorInsertLeft T' η' V W))
    (hRight' : ∀ V W : E, IsIso (tensorInsertRight T' η' V W)),
    (∀ V : B, IsIso (T'.map (L.map (η.app V)))) ∧
    ∃ (e : L.obj (𝟙_ B) ≅ 𝟙_ E)
      (μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T')
      (ec : (L ⋙ T').obj (T.obj (𝟙_ B)) ≅ T'.obj (𝟙_ E)),
      (∀ V : B, μ.hom.app (𝟙_ B, V) ≫ (e.hom ⊗ₘ 𝟙 (L.obj V)) ≫
        (λ_ (L.obj V)).hom = L.map (λ_ V).hom) ∧
      (∀ V : B, μ.hom.app (V, 𝟙_ B) ≫ (𝟙 (L.obj V) ⊗ₘ e.hom) ≫
        (ρ_ (L.obj V)).hom = L.map (ρ_ V).hom) ∧
      (∀ V W : B,
        T'.map (L.map (η.app (V ⊗ W))) ≫ μc.hom.app (V, W) =
          T'.map (μ.hom.app (V, W) ≫ (η'.app (L.obj V) ⊗ₘ η'.app (L.obj W)))) ∧
      (∀ ν : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T',
        (∀ V W : B,
          T'.map (L.map (η.app (V ⊗ W))) ≫ ν.hom.app (V, W) =
            T'.map (μ.hom.app (V, W) ≫ (η'.app (L.obj V) ⊗ₘ η'.app (L.obj W)))) →
          ν = μc) ∧
      T'.map (L.map (η.app (𝟙_ B))) ≫ ec.hom = T'.map e.hom ∧
      ∃ (m : MonoidalCategory P.FullSubcategory)
        (m' : MonoidalCategory P'.FullSubcategory)
        (s : @SymmetricCategory P.FullSubcategory _ m)
        (s' : @SymmetricCategory P'.FullSubcategory _ m'),
        CompletedConstraintModel P T η hLeft hRight hη m s ∧
        CompletedConstraintModel P' T' η' hLeft' hRight' hη' m' s' ∧
        CompletedPullbackCoherence P P' L T T' hT' μc ec m m' s s'

end Constraints

section ConstantSites

variable {C E : Type u} [SmallCategory C] [SmallCategory E]
  (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
  (A : Type u) [CommRing A]

/-- The published ordinary derived monoidal structure at the standard localization.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedMonoidal : MonoidalCategory (D (constant JC A)) :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  RingedDerivedNative.monoidal.{u, u, u} JC (constant JC A)

/-- Its published Koszul symmetry, with precisely that monoidal structure.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedSymmetric :
    @SymmetricCategory (D (constant JC A)) _ (constantDerivedMonoidal JC A) :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  RingedDerivedNative.symmetric.{u, u, u} JC (constant JC A)

/-- The ordinary tensor bifunctor, transparently from the published monoidal structure.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedTensor : D (constant JC A) × D (constant JC A) ⥤ D (constant JC A) :=
  @tensor (D (constant JC A)) _ (constantDerivedMonoidal JC A)

variable {JC JD A}
  {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}

/-- The existing pure-tensor-normalized ordinary pullback comparison data, specialized
only to the actual inverse image of the constant ring and its canonical ring map.
Source: Stacks 03EL and 07A4 (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev ConstantTensorData (F : InverseImageData L) (A : Type u) [CommRing A] :=
  SheafOfModules.CanonicalRingedTensorComparison (constant JC A) (constant JD A)
    (F.rings.obj (constant JC A)) L (F.algebra (constant JC A)) (constantMap F A)
    (pull F (constantMap F A)) (fun _ ↦ rfl)

/-- The Tag 07A4 normalization of ordinary derived inverse-image tensor comparison.
The equation is written without inverting a derived comparison at a non-K-flat object.
It uses the canonical cochain comparison, oriented from the tensor of the pullbacks
into the pullback of the tensor. Both source factors range over all flat-term K-flat
complexes; the images are again K-flat. This fixes the whole natural comparison by
fully faithful restriction to representatives.
Source: Stacks 07A4 (blueprint: lem-pur-completed-tensor-unit-insertion). -/
def ConstantTensorNormalization (F : InverseImageData L)
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A]
    (k : ConstantTensorData F A)
    (μ : constantDerivedTensor JC A ⋙ (derivedPull F V adj (constantMap F A)).functor ≅
      (((derivedPull F V adj (constantMap F A)).functor).prod
        ((derivedPull F V adj (constantMap F A)).functor)) ⋙ constantDerivedTensor JD A) :
    Prop :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  letI := HasDerivedCategory.standard (Mod (constant JD A))
  ∀ (P Q : Cx (constant JC A))
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := constant JC A) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (R := constant JC A) Q),
    (∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlat (Q.X n)) →
    ∃ (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := constant JD A)
        (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj P))
      (_hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := constant JD A)
        (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj Q)),
      (derivedPull F V adj (constantMap F A)).functor.map
          (RingedDerivedNative.tensorIso.{u, u, u} JC (constant JC A) P Q (Or.inl hP)).hom ≫
        μ.hom.app ((CategoryTheory.ConstantCompletion.Q (constant JC A)).obj P,
          (CategoryTheory.ConstantCompletion.Q (constant JC A)).obj Q) ≫
        (constantDerivedTensor JD A).map
          (Prod.mkHom ((derivedPull F V adj (constantMap F A)).comparison.app P)
            ((derivedPull F V adj (constantMap F A)).comparison.app Q)) ≫
        (RingedDerivedNative.tensorIso.{u, u, u} JD (constant JD A)
          (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj P)
          (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj Q)
          (Or.inl hP')).inv ≫
        (CategoryTheory.ConstantCompletion.Q (constant JD A)).map
          (k.total (constant JC A) (constant JD A) (F.rings.obj (constant JC A))
            L (F.algebra (constant JC A)) (constantMap F A) (pull F (constantMap F A))
            (fun _ ↦ rfl) P Q) =
        (derivedPull F V adj (constantMap F A)).comparison.app
          ((WeilConjectures.coefficientTotalTensor.{u, u, u} JC (constant JC A)).obj (P, Q))

end ConstantSites

```

## New

The Lean declarations above, with docstring blueprint markers updated to the data node, are in
lean/Sheaf/Paper/CompletedTensorUnitInsertionData.lean. The original module contains:

```lean
public import Sheaf.Paper.CompletedTensorUnitInsertionData
```

There is no change to any definition, signature, namespace, universe, or visibility.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedTensorUnitInsertion | E8 | Reexports the identical definitions and proves the existing theorem from the separate components. |
| Sheaf.Paper.CompletedTensorUnitInsertionData | E8 (new) | Houses the unchanged public definitions. |
| Sheaf.Paper.ConstantNativePullbackMonoidal | E8 (new) | Uses the ordinary native tensor comparison interface. |
| Sheaf.Paper.ReflectiveCompletedMonoidal | E8 (new) | Uses the completed constraint model. |
| Sheaf.Paper.ReflectiveCompletedPullbackCoherence | E8 (new) | Uses the completed comparison and coherence interfaces. |

`tools/downstream.py Sheaf.Paper.CompletedTensorUnitInsertion --uses` with all eleven
names reports zero downstream modules and finds each name only in the item itself.
A name search in both library roots likewise found no other consumer.
The original module and the Challenge target declarations retain their statements.
The original DAG node now attaches the theorem; the data node attaches the eleven definitions.

## Status

landed 20261022T025322-L-1275852 2026-10-22 (merge of deliver/E8/Sheaf.Paper.CompletedTensorUnitInsertion)
