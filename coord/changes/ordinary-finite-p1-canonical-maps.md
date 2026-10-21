# P1DecompositionTwistTransport and the canonical decomposition arrows

## Reason

Repair of C-0f23c R1/R2 (returned head 0f23cccac4): reuse F1's landed transport
uniqueness, discard the unlanded duplicate module/node, and preserve the existing
ownership of p1DecompositionTwist and p1DecompositionMap by
def-sp-p1-decomposition-arrows. That existing node's Lean attachment now points to
OrdinaryFiniteP1DecompositionMaps; the new helper node owns only the remaining
helpers. The untwist, Kummer base-change and evaluation nodes cite the existing
arrow node in stmt_deps. This repair changes no Lean signature or definition body.
Unused plain proof imports are removed from the two still-holed modules.

The inverse-twist decomposition needs independent proofs of evaluation naturality,
untwisting, and the component base-change equations. Move its pre-existing explicit
arrows into a common prerequisite module, preserving the public names and re-exporting
that module from the original item. The module separation resolves the proof dependency
cycle; it is not a way to evade the compile limit. A diagnostic version retaining all
original declarations in one file compiled in 53 seconds before the extraction.

Construct the existing compact P1DecompositionTwistTransport record by projecting
Scheme.finiteEtaleTwistPullbackData, instead of unpacking its existence theorem into
another choice. The compact record, all its field names, and its constructor remain
verbatim. In particular AmbientDiagonalPurityBaseChange uses these projections.
Each arrow retains exactly its old characterizing equation; no additional witness is
chosen. The existing full data determine the normalized roots, signed twists and
evaluation maps. Cache this projection behind an irreducible definition.

Cache three purely categorical composites behind irreducible definitions: shifted
comparison, tensor-evaluation adjoint, and biproduct comparison. Their bodies are exactly
the old composites in the same order. Cache the negative-product normalization as a proved
lemma. These changes keep consumers from expanding the large concrete derived-category
and finite-twist records. No target theorem signature is changed. The canonical maps
still have exactly their old mathematical meaning. Because target definitions transitively
use these maps, their statement review must nevertheless be reopened under AGENTS.md §4.

## Old

```lean
structure P1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) where
  roots : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) →
    ((upperStar AddCommGrpCat.{u + 1} f).obj (Y.rootsOfUnitySheaf N) ≅
      X.rootsOfUnitySheaf N)
  line : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IsUnit (N : Γ(Y, ⊤)) → IsUnit (N : Γ(X, ⊤)) → ∀ a : ℤ,
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a
  product : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
    (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1))
  roots_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))),
    (upperStar AddCommGrpCat.{u + 1} f).map (kernel.ι (N • 𝟙 Y.gmSheaf)) ≫
        Scheme.upperStarGmSheafToGmSheaf f =
      (roots f hY).hom ≫ kernel.ι (N • 𝟙 X.gmSheaf)
  line_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
      (W : Y.Etaleᵒᵖ) (a : A) (z : (Y.rootsOfUnitySheaf N).obj.obj W),
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (line f hY hX 1).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N Y hA W a z) =
    Scheme.finiteEtaleTateOneGenerator A N X hA
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W) a
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (roots f hY).hom).hom.app W z)
  zero_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))),
    line f hY hX 0 =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A)
  power_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    line f hY hX (.ofNat (n + 2)) =
      asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
        (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
        (Scheme.finiteEtaleTateLine Y N A hA)) ≪≫
      tensorIso (line f hY hX (.ofNat (n + 1))) (line f hY hX 1)
  negative_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((ihom.ev (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N Y hA 0)) ≫ (line f hY hX 0).hom =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
          (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
          (Scheme.finiteEtaleTateSheaf A N Y hA (.negSucc n)) ≫
        tensorHom (line f hY hX (.ofNat (n + 1))).hom (line f hY hX (.negSucc n)).hom ≫
        (ihom.ev (Scheme.finiteEtaleTateSheaf A N X hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N X hA 0)
  product_normalization : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
    (product T hT).hom ≫ eqToHom
        (congrArg (Scheme.finiteEtaleTateSheaf A N T hA) (add_neg_cancel (1 : ℤ))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
        (Scheme.finiteEtaleTateSheaf A N T hA 0)

/-- Project the fully normalized dependency theorem into the compact record above.
Every selected arrow retains its characterizing equation; no arbitrary line,
orientation or unconstrained comparison is selected.
Source: Stacks Tags 03PK and 03Q1 (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    P1DecompositionTwistTransport A N hA :=
  Classical.choice ((Scheme.etaleFiniteTwistPullback A N hN hA).elim fun r hr ↦
    hr.elim fun c hc ↦ hc.elim fun p hp ↦
      ⟨{ roots := r
         line := c
         product := fun T hT ↦ p T hT 1 (-1)
         roots_normalization := hp.2.1
         line_normalization := hp.2.2.1
         zero_normalization := hp.the project server
         power_normalization := hp.the project server.1
         negative_normalization := hp.the project server.2.1
         product_normalization := fun T hT ↦ hp.the project server.the project server.the project server.2.1 T hT 0 }⟩)

/-- The signed twist pullback with its roots, pure-tensor and negative-evaluation
normalizations retained in `p1DecompositionTwistTransport`.
Source: Stacks Tags 03PK and 03Q1 (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSheafPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a :=
  (p1DecompositionTwistTransport A N hN hA).line
    f hY ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) a

/-- The inverse-line product, whose hom is characterized as internal-Hom evaluation.
Source: Stacks Tag 03PK (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSheafProduct (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1) :=
  (p1DecompositionTwistTransport A N hN hA).product T hT

/-- A finite signed twist placed in degree zero and shifted by an integer.
Source: the definition K=A_S(-1)[-2] (blueprint: thm-amb-p1-decomposition). -/
abbrev p1DecompositionTwist (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (a b : ℤ) :
    DerivedCategoryModule A T :=
  ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA a))⟦b⟧

/-- Derived inverse image of a signed shifted twist, with the canonical shift and
degree-zero comparisons and the normalized sheaf comparison.
Source: Stacks Tag 03Q1 (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionTwistPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a b : ℤ) :
    (ordinaryFinitePullback A f).obj (p1DecompositionTwist A N hA Y a b) ≅
      p1DecompositionTwist A N hA X a b :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  ((ordinaryFinitePullback A f).commShiftIso b).app _ ≪≫
    (shiftFunctor _ b).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (p1DecompositionSheafPullback A N hN hA f hY a))

/-- Compute the tensor of the positive line and its sheaf dual in degree zero.
The positive line is flat by its normalized inverse-product isomorphism.
Source: the evaluation step in the node (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionDegreeZeroTensor (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (ordinaryFiniteLine A N hA T)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1)) :=
  singleFunctorObjTensorIso (Scheme.finiteEtaleTateSheaf A N T hA 1)
    (Scheme.finiteEtaleTateSheaf A N T hA (-1))
    (ObjectProperty.flat_of_tensorIso (p1DecompositionSheafProduct A N hN hA T hT))

/-- Evaluate the degree-zero dual against the positive line, using symmetry and
then the actual internal-Hom evaluation, after the canonical flat tensor comparison.
Source: the evaluation step in the node (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionDegreeZeroEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1)))).obj
      (ordinaryFiniteLine A N hA T) ⟶ ordinaryFiniteUnit A T :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app _).app _ ≫
    (p1DecompositionDegreeZeroTensor A N hN hA T hT).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app (ordinaryFiniteConstant A T))

/-- Evaluation of A_T(-1)[-2] against A_T(1)[2]: cancel the shifts and apply
`p1DecompositionDegreeZeroEvaluation`.
Source: the evaluation in the defining adjoint of h
(blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (p1DecompositionTwist A N hA T (-1) (-2))).obj
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A T :=
  (derivedTensorShiftIso (ModuleCat.{u + 1} A)
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA (-1)))
    (ordinaryFiniteLine A N hA T) (-2) 2).hom ≫
    (shiftFunctorZero _ ℤ).hom.app _ ≫
    p1DecompositionDegreeZeroEvaluation A N hN hA T hT

/-- The unit component A_S -> Rq_* A_P under the constant-object comparison.
Source: the component 1 in the blueprint (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionUnit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine S ↘ S)).homEquiv _ _
      (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom

/-- The component h is the adjoint of the tensor-with-Chern-class/evaluation
composite, using the canonical negative-twist pullback and tensor unit.
Source: the explicit definition of h in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionChernAdjoint (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    p1DecompositionTwist A N hA S (-1) (-2) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine S ↘ S)).homEquiv _ _
      ((derivedTensorSingleUnitIso _).inv ≫
        ((ordinaryFiniteTensor A (ProjectiveLine S)).obj
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
            (p1DecompositionTwist A N hA S (-1) (-2)))).map c ≫
        ((ordinaryFiniteTensor A (ProjectiveLine S)).map
          (p1DecompositionTwistPullback A N hN hA (ProjectiveLine S ↘ S) hS (-1) (-2)).hom).app _ ≫
        p1DecompositionEvaluation A N hN hA (ProjectiveLine S)
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom))

/-- The specified ordered map (1,h), with no independent choice of decomposition.
Source: the displayed isomorphism in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  biprod.desc (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)

/-- The canonical pullback map on A_S plus A_S(-1)[-2], assembled from the
images of the two projections and the constant and signed-twist comparisons.
Source: the arbitrary-base compatibility clause (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSourceMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A g).obj
        (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFiniteUnit A S' ⊞ p1DecompositionTwist A N hA S' (-1) (-2)) :=
  biprod.lift
    ((ordinaryFinitePullback A g).map biprod.fst ≫ (ordinaryFiniteUnitPullback A g).hom)
    ((ordinaryFinitePullback A g).map biprod.snd ≫
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom)
```

## New

```lean
structure P1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) where
  roots : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) →
    ((upperStar AddCommGrpCat.{u + 1} f).obj (Y.rootsOfUnitySheaf N) ≅
      X.rootsOfUnitySheaf N)
  line : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IsUnit (N : Γ(Y, ⊤)) → IsUnit (N : Γ(X, ⊤)) → ∀ a : ℤ,
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a
  product : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
    (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1))
  roots_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))),
    (upperStar AddCommGrpCat.{u + 1} f).map (kernel.ι (N • 𝟙 Y.gmSheaf)) ≫
        Scheme.upperStarGmSheafToGmSheaf f =
      (roots f hY).hom ≫ kernel.ι (N • 𝟙 X.gmSheaf)
  line_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
      (W : Y.Etaleᵒᵖ) (a : A) (z : (Y.rootsOfUnitySheaf N).obj.obj W),
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (line f hY hX 1).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N Y hA W a z) =
    Scheme.finiteEtaleTateOneGenerator A N X hA
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W) a
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (roots f hY).hom).hom.app W z)
  zero_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))),
    line f hY hX 0 =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A)
  power_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    line f hY hX (.ofNat (n + 2)) =
      asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
        (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
        (Scheme.finiteEtaleTateLine Y N A hA)) ≪≫
      tensorIso (line f hY hX (.ofNat (n + 1))) (line f hY hX 1)
  negative_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((ihom.ev (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N Y hA 0)) ≫ (line f hY hX 0).hom =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
          (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
          (Scheme.finiteEtaleTateSheaf A N Y hA (.negSucc n)) ≫
        tensorHom (line f hY hX (.ofNat (n + 1))).hom (line f hY hX (.negSucc n)).hom ≫
        (ihom.ev (Scheme.finiteEtaleTateSheaf A N X hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N X hA 0)
  product_normalization : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
    (product T hT).hom ≫ eqToHom
        (congrArg (Scheme.finiteEtaleTateSheaf A N T hA) (add_neg_cancel (1 : ℤ))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
        (Scheme.finiteEtaleTateSheaf A N T hA 0)

/-- Keep precisely the compact record's projections of full normalized transport.
Source: Stacks Tags 03PK and 03Q1 (blueprint: def-asd-ordinary-finite-p1-decomposition-maps). -/
def p1DecompositionTransportOfData (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A N hA) :
    P1DecompositionTwistTransport A N hA :=
  { roots := t.r
    line := t.c
    product := fun T hT ↦ t.p T hT 1 (-1)
    roots_normalization := t.laws.2.1
    line_normalization := t.laws.2.2.1
    zero_normalization := t.laws.the project server
    power_normalization := t.laws.the project server.1
    negative_normalization := t.laws.the project server.2.1
    product_normalization := fun T hT ↦ t.laws.the project server.the project server.the project server.2.1 T hT 0 }

/-- Project the already constructed fully normalized transport into the compact
interface, keeping each characterizing equation and making no additional choice.
Source: Stacks Tags 03PK and 03Q1 (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    P1DecompositionTwistTransport A N hA :=
  p1DecompositionTransportOfData A N hA (Scheme.finiteEtaleTwistPullbackData A N hN hA)

/-- The signed twist pullback with its roots, pure-tensor and negative-evaluation
normalizations retained in `p1DecompositionTwistTransport`.
Source: Stacks Tags 03PK and 03Q1 (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSheafPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a :=
  (p1DecompositionTwistTransport A N hN hA).line
    f hY ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) a

/-- The inverse-line product, whose hom is characterized as internal-Hom evaluation.
Source: Stacks Tag 03PK (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSheafProduct (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1) :=
  (p1DecompositionTwistTransport A N hN hA).product T hT

/-- The normalized inverse product is the actual evaluation.
Source: Stacks Tag 03PK (blueprint: def-asd-ordinary-finite-p1-decomposition-maps).
Proof: take the n=0 negative-evaluation normalization of the canonical finite-twist data. -/
theorem p1DecompositionSheafProduct_hom (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (p1DecompositionSheafProduct A N hN hA T hT).hom =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
        (Scheme.finiteEtaleTateSheaf A N T hA 0) := by
  have h := (p1DecompositionTwistTransport A N hN hA).product_normalization T hT
  simpa only [p1DecompositionSheafProduct, eqToHom_refl, Category.comp_id] using h

/-- A finite signed twist placed in degree zero and shifted by an integer.
Source: the definition K=A_S(-1)[-2] (blueprint: thm-amb-p1-decomposition). -/
abbrev p1DecompositionTwist (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (a b : ℤ) :
    DerivedCategoryModule A T :=
  ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA a))⟦b⟧

/-- Shift a comparison between functors, without unfolding its concrete categories.
Source: functoriality of the shift (blueprint: def-asd-ordinary-finite-p1-decomposition-maps). -/
@[irreducible]
def p1DecompositionShiftedComparison {C D C₀ D₀ : Type*}
    [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (single : C₀ ⥤ C) (single' : D₀ ⥤ D)
    (pull : C₀ ⥤ D₀) (comp : single ⋙ F ≅ pull ⋙ single')
    (L : C₀) (M : D₀) (e : pull.obj L ≅ M) (b : ℤ) :
    F.obj ((single.obj L)⟦b⟧) ≅ (single'.obj M)⟦b⟧ :=
  (F.commShiftIso b).app _ ≪≫
    (shiftFunctor _ b).mapIso (comp.app L ≪≫ single'.mapIso e)

/-- Derived inverse image of a signed shifted twist, with the canonical shift and
degree-zero comparisons and the normalized sheaf comparison.
Source: Stacks Tag 03Q1 (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionTwistPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a b : ℤ) :
    (ordinaryFinitePullback A f).obj (p1DecompositionTwist A N hA Y a b) ≅
      p1DecompositionTwist A N hA X a b :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  p1DecompositionShiftedComparison (ordinaryFinitePullback A f)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} A) f)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f)
    (Scheme.finiteEtaleTateSheaf A N Y hA a) (Scheme.finiteEtaleTateSheaf A N X hA a)
    (p1DecompositionSheafPullback A N hN hA f hY a) b

/-- Compute the tensor of the positive line and its sheaf dual in degree zero.
The positive line is flat by its normalized inverse-product isomorphism.
Source: the evaluation step in the node (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionDegreeZeroTensor (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (ordinaryFiniteLine A N hA T)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1)) :=
  singleFunctorObjTensorIso (Scheme.finiteEtaleTateSheaf A N T hA 1)
    (Scheme.finiteEtaleTateSheaf A N T hA (-1))
    (ObjectProperty.flat_of_tensorIso (p1DecompositionSheafProduct A N hN hA T hT))

/-- Evaluate the degree-zero dual against the positive line, using symmetry and
then the actual internal-Hom evaluation, after the canonical flat tensor comparison.
Source: the evaluation step in the node (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionDegreeZeroEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1)))).obj
      (ordinaryFiniteLine A N hA T) ⟶ ordinaryFiniteUnit A T :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app _).app _ ≫
    (p1DecompositionDegreeZeroTensor A N hN hA T hT).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app (ordinaryFiniteConstant A T))

/-- Evaluation of A_T(-1)[-2] against A_T(1)[2]: cancel the shifts and apply
`p1DecompositionDegreeZeroEvaluation`.
Source: the evaluation in the defining adjoint of h
(blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (p1DecompositionTwist A N hA T (-1) (-2))).obj
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A T :=
  (derivedTensorShiftIso (ModuleCat.{u + 1} A)
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA (-1)))
    (ordinaryFiniteLine A N hA T) (-2) 2).hom ≫
    (shiftFunctorZero _ ℤ).hom.app _ ≫
    p1DecompositionDegreeZeroEvaluation A N hN hA T hT

/-- The unit component A_S -> Rq_* A_P under the constant-object comparison.
Source: the component 1 in the blueprint (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionUnit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine S ↘ S)).homEquiv _ _
      (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom

/-- Form a tensor-evaluation adjoint in arbitrary categories.
Source: the tensor-Hom adjunction (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionTensorAdjoint {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (tensor : D ⥤ D ⥤ D)
    (K : C) (U L V K' : D)
    (unit : F.obj K ≅ (tensor.obj (F.obj K)).obj U) (pull : F.obj K ≅ K')
    (eval : (tensor.obj K').obj L ⟶ V) (c : U ⟶ L) : K ⟶ G.obj V :=
  adj.homEquiv _ _ (unit.hom ≫ (tensor.obj (F.obj K)).map c ≫
    (tensor.map pull.hom).app L ≫ eval)

/-- The component h is the adjoint of the tensor-with-Chern-class/evaluation
composite, using the canonical negative-twist pullback and tensor unit.
Source: the explicit definition of h in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionChernAdjoint (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    p1DecompositionTwist A N hA S (-1) (-2) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  p1DecompositionTensorAdjoint (ordinaryFinitePullback A (ProjectiveLine S ↘ S))
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S))
    (ordinaryFiniteTensor A (ProjectiveLine S)) (p1DecompositionTwist A N hA S (-1) (-2))
    (ordinaryFiniteUnit A (ProjectiveLine S))
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (ordinaryFiniteUnit A (ProjectiveLine S))
    (p1DecompositionTwist A N hA (ProjectiveLine S) (-1) (-2))
    (derivedTensorSingleUnitIso _).symm
    (p1DecompositionTwistPullback A N hN hA (ProjectiveLine S ↘ S) hS (-1) (-2))
    (p1DecompositionEvaluation A N hN hA (ProjectiveLine S)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom)) c

/-- The specified ordered map (1,h), with no independent choice of decomposition.
Source: the displayed isomorphism in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  biprod.desc (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)

/-- Assemble two component comparisons on a pulled-back biproduct.
Source: the universal property of the biproduct (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionBiprodMap {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) (X Y : C) (X' Y' : D) (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') :
    F.obj (X ⊞ Y) ⟶ X' ⊞ Y' :=
  biprod.lift (F.map biprod.fst ≫ e.hom) (F.map biprod.snd ≫ e'.hom)

/-- The canonical pullback map on A_S plus A_S(-1)[-2], assembled from the
images of the two projections and the constant and signed-twist comparisons.
Source: the arbitrary-base compatibility clause (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSourceMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A g).obj
        (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFiniteUnit A S' ⊞ p1DecompositionTwist A N hA S' (-1) (-2)) :=
  p1DecompositionBiprodMap (ordinaryFinitePullback A g)
    (ordinaryFiniteUnit A S) (p1DecompositionTwist A N hA S (-1) (-2))
    (ordinaryFiniteUnit A S') (p1DecompositionTwist A N hA S' (-1) (-2))
    (ordinaryFiniteUnitPullback A g) (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2))
```

## Users

The item re-exports the common interface. The complete users list includes the
three consumers reported by the earlier delivery preflight and the two consumers
reported in the return for cd03cf5612, including declarations whose rework rows
are still open. Their existing attachments and source are preserved.
No consumer source is adapted in this delivery. The original compact record interface
is retained specifically so the AmbientDiagonalPurityBaseChange projections remain valid.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Publicly imports the common interface; statement unchanged; proof supplied. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Uses twist, twist pullback and decomposition map under the same names and types. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | SpP1NormalizedAt uses the signed twist and exact decomposition map in its normalization equation; names, types and canonical mathematical maps are preserved. |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | unclaimed | Builds normalized families using the signed twist and decomposition map; theorem signature and proof are unchanged. |
| Sheaf.Paper.PurityFrameKummer | unclaimed in shared snapshot | Uses signed sheaf pullback under the same name and type. |
| Sheaf.Paper.PurityFrameClass | unclaimed in shared snapshot | Transitive importer; no direct reference to changed declarations. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed in shared snapshot | Transitive importer; no direct reference to changed declarations. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed; open rework row | Uses roots, line and their normalization projections, all preserved verbatim. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed; open rework row | Uses signed sheaf pullback under the same name and type. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed; open rework row | Uses signed sheaf pullback under the same name and type. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed; quarantined, open rework row | Archived source uses signed sheaf pullback under the same name and type; its archive and Lean attachment are preserved. |

Repair validation (2026-10-21): lcompile.py --all recompiled all seven packet
modules successfully without warnings; each file took at most 42.2 seconds. A
source-level declaration comparison found no missing original declarations and no
changed original signatures.
GeoP1Cohomology, ProEtaleProjectiveLineTraceSystem and SpP1NormalizedFamilyCore
compiled unchanged against the refreshed packet in 36.1, 43.2 and 56.4 seconds,
respectively, without warnings. The two consumers named in the return therefore
need no source adaptation. Consumer copies used only for these checks remain in
the scratchpad and are not delivered.

Earlier validation: lcompile.py --all compiled all seven packet modules without warnings.
Four downstream modules compiled unchanged against the packet: GeoP1Cohomology,
PurityFrameKummer, PurityFramePrincipalBoundary, and PurityFrameClass. The exact
AmbientDiagonalPurityBaseChange transport-record construction compiled unchanged in
23.3 seconds. Its compact record and all projections are byte-for-byte unchanged.
The generic SupportedTwistMultiplication construction, including both signed
pullbacks, compiled unchanged in a diagnostic prefix in 47.6 seconds. Profiling
shows 29 seconds of kernel checking and 38 seconds of concurrent module linting;
the same baseline prefix exceeded 60 seconds.

Validation limits: the unchanged whole AmbientDiagonalPurityBaseChange and
SupportedCupFunctoriality already exceed 60 seconds against the published baseline.
The whole SupportedTwistMultiplication took 56.8 seconds against that baseline and
exceeded 60 seconds against the packet. Whole-file passes for those three are not
claimed. Their open rework entries, attachments and sources are preserved. No
consumer source is changed and no forced adaptations are present. The change
record lists all ten consumers, including these three and both consumers named
in the return for cd03cf5612.

## Status

landed 20261021T125938-L-2464238 2026-10-21 (merge of deliver/A6/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition)
