# WeilConjectures.IntegralComparisonSystem: separate its interface from existence

## Reason

The published `integralPullbackComparisonRealization_simultaneous` is stronger than
`integralPullbackComparisonRealization`: its system is chosen before all coefficient
fields and inclusions. Specializing its proposition is the shortest existing proof.
Its module currently imports the original module for the definitions, so using it
in the original module would close an import cycle. Move the definitions, unchanged,
to `Sheaf.Paper.IntegralComparisonSystemData` and publicly re-export them from the
original module. Update only the simultaneous module's first import to that interface.
No theorem statement, definition body, visibility, attribute, normalization or
mathematical assumption changes. This is a dependency-cycle repair, not a performance
split. No data is extracted from a mere existence theorem into any definition.

The simultaneous module is held by D3 in the current claim record. Its theorem and
proof are untouched. The forced import replacement retains all the public definitions
its statement uses. The lost import only carried the weaker existence theorem, which
its statement and proof never use. Existing direct consumers of the simultaneous module
were searched; none uses the weaker theorem without separately importing its module.
No Challenge.lean statement or interpretation changes; the definitions it can use are
verbatim the same.

## Old

The following block occurs in `Sheaf.Paper.IntegralPullbackComparisonRealization`:

```lean
/-- Apply reduction to the defining pullback realization, then the actual
whole-system action counit. By integralComparisonReductionCounit_formula this
is derived coefficient change of the K-injective-normalized epsilon.
Source: Stacks 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonPullbackCounit {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SZ : CoefficientDerivedSystemCalculus l E Z)
    (ρ : IntegralComparisonRoosModel l E Z)
    (M : IntegralComparisonPullbackModel l E f SY ρ) :
    integralDerivedPullback l E f ⋙ SZ.reduction ⟶
      SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f :=
  Functor.whiskerRight M.realization.hom SZ.reduction ≫
    Functor.whiskerLeft (SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f)
      SZ.adjunction.counit

/-- The scalar analogue of the entire-system counit construction.
Source: Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarCounit (Y : Scheme.{t})
    (SE : CoefficientDerivedSystemCalculus l E Y)
    (SL : CoefficientDerivedSystemCalculus l L Y)
    (ρ : IntegralComparisonRoosModel l L Y)
    (M : IntegralComparisonScalarModel l E L ι Y SE ρ) :
    integralScalarExtensionOfUniverses l E L ι Y ⋙ SL.reduction ⟶
      SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι Y :=
  Functor.whiskerRight M.realization.hom SL.reduction ≫
    Functor.whiskerLeft (SE.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι Y)
      SL.adjunction.counit

/-- Coherent realization interfaces at one coefficient field. Each constituent
has the actual representative normalization; effectivity is asserted only on
the intrinsic constructible-complete domain with ell invertible.
Source: Stacks 099N(5), 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonCoefficientData where
  /-- The published normalized reduction calculus on each small pro-etale site. -/
  system : ∀ X : Scheme.{u}, CoefficientDerivedSystemCalculus l E X
  /-- Total limit is identified with the specified Roos construction. -/
  roos : ∀ X : Scheme.{u}, IntegralComparisonRoosModel l E X
  /-- The pullback realization, tested on every simultaneous K-flat presentation. -/
  pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IntegralComparisonPullbackModel l E f (system Y) (roos X)
  /-- The counit-built diagram map is invertible on every allowed input. -/
  effective : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    IsIso ((integralComparisonPullbackCounit l E f (system Y) (system X)
      (roos X) (pullback f)).app K.obj)
  /-- Derived completeness makes the normalized reconstruction unit invertible. -/
  complete : ∀ (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X),
    IsIso (((system X).adjunction.unit).app K.obj)

/-- The scalar realization, with its entire-system counit invertible on the
intrinsic constructible domain. Source: Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonScalarData
    (DE : IntegralComparisonCoefficientData l E) (DL : IntegralComparisonCoefficientData l L) where
  /-- The cochain-normalized scalar realization on every scheme. -/
  model : ∀ X : Scheme.{u},
    IntegralComparisonScalarModel l E L ι X (DE.system X) (DL.roos X)
  /-- The specified scalar counit is an isomorphism, without a Tor-amplitude bound. -/
  effective : ∀ (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X),
    IsIso ((integralComparisonScalarCounit l E L ι X (DE.system X) (DL.system X)
      (DL.roos X) (model X)).app K.obj)

/-- One simultaneously normalized system for all finite coefficient extensions.
Small coefficient models and their embeddings express subextensions of any fixed
algebraic closure without identifying its universe with the site universe.
Source: blueprint final common-stage transport paragraph; Stacks 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonSystem (l : ℕ) [Fact l.Prime] where
  /-- All one-field realization data, with the same functors as the dependencies. -/
  coefficient : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], IntegralComparisonCoefficientData l E
  /-- All finite scalar inclusions at once, including identity and composite inclusions. -/
  scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    IntegralComparisonScalarData l E L ι (coefficient E) (coefficient L)

variable (D : IntegralComparisonSystem.{u} l)

/-- Eta is realization of h-star applied to the whole-system counit for k.
Source: Stacks 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonEta {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj K.obj) ≅
      (coefficientSequenceLimit l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          ((integralComparisonDerivedSequencePullback l E k).obj
            (((D.coefficient E).system V).reduction.obj K.obj))) :=
  letI := (D.coefficient E).effective k K
  ((D.coefficient E).pullback h).realization.app
      ((integralDerivedPullback l E k).obj K.obj) ≪≫
    (coefficientSequenceLimit l E Z).mapIso
      ((integralComparisonDerivedSequencePullback l E h).mapIso
        (asIso ((integralComparisonPullbackCounit l E k
          ((D.coefficient E).system V) ((D.coefficient E).system W)
          ((D.coefficient E).roos W) ((D.coefficient E).pullback k)).app K.obj)))

/-- Lambda is realization of scalar change of the whole-system pullback counit.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonLambda {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E f).obj K.obj) ≅
      (coefficientSequenceLimit l L X).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((integralComparisonDerivedSequencePullback l E f).obj
            (((D.coefficient E).system Y).reduction.obj K.obj))) :=
  letI := (D.coefficient E).effective f K
  ((D.scalar E L ι).model X).realization.app
      ((integralDerivedPullback l E f).obj K.obj) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonDerivedSequenceScalar l E L ι X).mapIso
        (asIso ((integralComparisonPullbackCounit l E f
          ((D.coefficient E).system Y) ((D.coefficient E).system X)
          ((D.coefficient E).roos X) ((D.coefficient E).pullback f)).app K.obj)))

/-- Mu is pullback of the whole-system scalar counit, followed by the inverse
of the generator-normalized scalar/pullback associator on entire diagrams.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonMu {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l L f).obj ((integralScalarExtension l E L ι Y).obj K.obj) ≅
      (coefficientSequenceLimit l L X).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((integralComparisonDerivedSequencePullback l E f).obj
            (((D.coefficient E).system Y).reduction.obj K.obj))) :=
  letI := (D.scalar E L ι).effective Y K
  ((D.coefficient L).pullback f).realization.app
      ((integralScalarExtension l E L ι Y).obj K.obj) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonDerivedSequencePullback l L f).mapIso
        (asIso ((integralComparisonScalarCounit l E L ι Y
          ((D.coefficient E).system Y) ((D.coefficient L).system Y)
          ((D.coefficient L).roos Y) ((D.scalar E L ι).model Y)).app K.obj))) ≪≫
    (coefficientSequenceLimit l L X).mapIso
      ((integralComparisonSystemScalarPullback l E L ι f).app
        (((D.coefficient E).system Y).reduction.obj K.obj)).symm

/-- The specified integral compositor is Rlim of the finite compositor, followed
by eta inverse. Source: Stacks 0D6D, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonComposition {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E (h ≫ k)).obj K.obj ≅
      (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj K.obj) :=
  ((D.coefficient E).pullback (h ≫ k)).realization.app K.obj ≪≫
    (coefficientSequenceLimit l E Z).mapIso
      ((integralComparisonSystemComposition l E h k).app
        (((D.coefficient E).system V).reduction.obj K.obj)) ≪≫
    (integralComparisonEta l E D h k K).symm

/-- The specified scalar comparison is lambda followed by mu inverse.
Source: Stacks 06YY, 099N, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalar {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :=
  integralComparisonLambda l E L ι D f K ≪≫ (integralComparisonMu l E L ι D f K).symm

/-- The actual scalar extension on the intrinsic full categories. The auxiliary
prime-to-characteristic parameter of the existing interface is discharged by
p=ell+1; this supplies no assumption on schemes or reductions.
Source: blueprint integral scalar extension, order 1460
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonConstructibleScalar (X : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension (l + 1) l
    (Nat.ne_of_lt (Nat.lt_succ_self l)) E L ι X


/-- The identity pullback is the identity finite diagram followed by the
inverse derived-completeness unit. Source: Stacks 099N, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonUnit (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralDerivedPullback l E (𝟙 X)).obj K.obj ≅ K.obj :=
  letI := (D.coefficient E).complete X K
  ((D.coefficient E).pullback (𝟙 X)).realization.app K.obj ≪≫
    (coefficientSequenceLimit l E X).mapIso
      ((integralComparisonSystemUnit l E X).app
        (((D.coefficient E).system X).reduction.obj K.obj)) ≪≫
    (asIso (((D.coefficient E).system X).adjunction.unit.app K.obj)).symm

/-- Identity scalar extension under ordinary multiplication and the specified
completion map chi. Source: blueprint scalar-extension unit; Stacks 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarUnit (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E E (AlgHom.id ℚ_[l] E) X).obj K.obj ≅ K.obj :=
  (scalarCompletionIso l E E (AlgHom.id ℚ_[l] E) X K.obj K.property.1).symm ≪≫
    (integralOrdinaryDerivedScalarUnit l E X).app K.obj

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The integral scalar associator is precisely the ordinary derived tensor
associator conjugated by the specified completion maps chi.
Source: blueprint common-stage transport; Stacks 06YY, 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarAssociator (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l L M j X).obj
        ((integralScalarExtension l E L ι X).obj K.obj) ≅
      (integralScalarExtension l E M (j.comp ι) X).obj K.obj :=
  (scalarCompletionIso l L M j X _
      (((integralComparisonConstructibleScalar l E L ι X).obj K).property.1)).symm ≪≫
    (integralOrdinaryDerivedScalar l L M j X).mapIso
      (scalarCompletionIso l E L ι X K.obj K.property.1).symm ≪≫
    (integralOrdinaryDerivedScalarComp l E L ι X M j).app K.obj ≪≫
    scalarCompletionIso l E M (j.comp ι) X K.obj K.property.1

end WeilConjectures

namespace WeilConjectures

/-- The inherited sequence site is essentially small in its object universe.
This instance specializes `essentiallySmallSelf`, avoiding inference through an
undetermined maximum in ordinary change-of-rings model projections.
Source: blueprint size convention; Stacks 0941
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
instance (priority := 1001) integralComparisonSequenceSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) := essentiallySmallSelf.{0, u, u + 1} _

/-- Composition laws for the specified families, on strict systems and their realization.
Source: Stacks 0D6D, 0941; blueprint common-stage transport
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonCompositionLaws
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonSystem.{u} l) : Prop where
  /-- The finite composition equation is an equation of entire quotient systems. -/
  systemAssociative : ∀ {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) (N : coefficientSequenceModules l E V),
    (integralComparisonSequenceComposition.{u, u} l E (j ≫ h) k).hom.app N ≫
        (integralComparisonSequenceComposition.{u, u} l E j h).hom.app
          ((integralComparisonSequencePullback.{u, u} l E k).obj N) =
      eqToHom (congrArg (fun f : Y ⟶ V ↦
        (integralComparisonSequencePullback.{u, u} l E f).obj N) (Category.assoc j h k).symm) ≫
        (integralComparisonSequenceComposition.{u, u} l E j (h ≫ k)).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E j).map
          ((integralComparisonSequenceComposition.{u, u} l E h k).hom.app N)
  /-- The source identity is the specified inverse-image unit, before realization. -/
  systemUnitSource : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceComposition.{u, u} l E (𝟙 X) f).hom.app N ≫
        (integralComparisonSequenceUnit.{u, u} l E X).hom.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj N) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralComparisonSequencePullback.{u, u} l E g).obj N) (Category.id_comp f))
  /-- The target identity is the same unit, before realization. -/
  systemUnitTarget : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceComposition.{u, u} l E f (𝟙 Y)).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E f).map
          ((integralComparisonSequenceUnit.{u, u} l E Y).hom.app N) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralComparisonSequencePullback.{u, u} l E g).obj N) (Category.comp_id f))
  /-- Naturality of the realized composition comparisons. -/
  naturality : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K J : sfIntegralConstructibleCategory l E V) (r : K ⟶ J),
    (integralDerivedPullback l E (h ≫ k)).map r.hom ≫
        (integralComparisonComposition l E D h k J).hom =
      (integralComparisonComposition l E D h k K).hom ≫
        (integralDerivedPullback l E h).map ((integralDerivedPullback l E k).map r.hom)
  /-- Associativity after transport by eta, with the actual scheme equality. -/
  associative : ∀ {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    (integralComparisonComposition l E D (j ≫ h) k K).hom ≫
        (integralComparisonComposition l E D j h
          ((constructibleIntegralPullback l E k).obj K)).hom =
      eqToHom (congrArg (fun f : Y ⟶ V ↦
        (integralDerivedPullback l E f).obj K.obj) (Category.assoc j h k).symm) ≫
        (integralComparisonComposition l E D j (h ≫ k) K).hom ≫
        (integralDerivedPullback l E j).map
          ((integralComparisonComposition l E D h k K).hom)
  /-- Realized source unit, with the completeness normalization. -/
  unitSource : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonComposition l E D (𝟙 X) f K).hom ≫
        (integralComparisonUnit l E D X ((constructibleIntegralPullback l E f).obj K)).hom =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.id_comp f))
  /-- Realized target unit. -/
  unitTarget : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonComposition l E D f (𝟙 Y) K).hom ≫
        (integralDerivedPullback l E f).map ((integralComparisonUnit l E D Y K).hom) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.comp_id f))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)

/-- The left side of the scalar/composition equation, in the full constructible category.
Source: blueprint common-stage transport; Stacks 06YY, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarSquareLeft {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstructibleScalar l E L ι Z).obj
        ((constructibleIntegralPullback l E (h ≫ k)).obj K) ⟶
      (constructibleIntegralPullback l L h).obj ((constructibleIntegralPullback l L k).obj
        ((integralComparisonConstructibleScalar l E L ι V).obj K)) :=
  ObjectProperty.homMk
    ((integralScalarExtension l E L ι Z).map
        (integralComparisonComposition l E D h k K).hom ≫
      (integralComparisonScalar l E L ι D h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (integralDerivedPullback l L h).map (integralComparisonScalar l E L ι D k K).hom)

/-- The right side, with the very same source and target integral objects.
Source: blueprint common-stage transport; Stacks 06YY, 0D6D
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
def integralComparisonScalarSquareRight {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstructibleScalar l E L ι Z).obj
        ((constructibleIntegralPullback l E (h ≫ k)).obj K) ⟶
      (constructibleIntegralPullback l L h).obj ((constructibleIntegralPullback l L k).obj
        ((integralComparisonConstructibleScalar l E L ι V).obj K)) :=
  ObjectProperty.homMk
    ((integralComparisonScalar l E L ι D (h ≫ k) K).hom ≫
      (integralComparisonComposition l L D h k
        ((integralComparisonConstructibleScalar l E L ι V).obj K)).hom)

/-- All coherence equations for the normalized construction. Equations on systems precede
realization; the integral equations refer to the displayed counit-built eta, lambda and mu.
Source: Stacks 099N, 0D6D, 06YY, 0941; blueprint common-stage transport
(blueprint: lem-trf-integral-pullback-comparison-realization). -/
structure IntegralComparisonRealizationCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l) : Prop where
  /-- Associativity and units for every coefficient field, including E and L. -/
  composition : ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F],
    IntegralComparisonCompositionLaws l F D
  /-- The scalar/composition equation already holds on entire quotient diagrams. -/
  systemScalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (N : coefficientSequenceModules l E V),
    (integralComparisonSequenceScalarModel.{u, u} l E L ι Z).E.map
        ((integralComparisonSequenceComposition.{u, u} l E h k).hom.app N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l E L ι h).hom.app
          ((integralComparisonSequencePullback.{u, u} l E k).obj N) ≫
        (integralComparisonSequencePullback.{u, u} l L h).map
          ((integralComparisonSequenceScalarPullback.{u, u} l E L ι k).hom.app N) =
      (integralComparisonSequenceScalarPullback.{u, u} l E L ι (h ≫ k)).hom.app N ≫
        (integralComparisonSequenceComposition.{u, u} l L h k).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι V).E.obj N)
  /-- Scalar comparison is natural for all derived constructible morphisms. -/
  naturality : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K J : sfIntegralConstructibleCategory l E Y) (r : K ⟶ J),
    (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E f).map r.hom) ≫
        (integralComparisonScalar l E L ι D f J).hom =
      (integralComparisonScalar l E L ι D f K).hom ≫
        (integralDerivedPullback l L f).map ((integralScalarExtension l E L ι Y).map r.hom)
  /-- The node's displayed equation, with its specified integral families. -/
  scalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    integralComparisonScalarSquareLeft l E L ι D h k K =
      integralComparisonScalarSquareRight l E L ι D h k K
  /-- The same equation in raw rationalization, without a perfectness restriction. -/
  rationalScalarComposition : ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    (sfRationalConstructibleLocalization l L Z).map
        (integralComparisonScalarSquareLeft l E L ι D h k K) =
      (sfRationalConstructibleLocalization l L Z).map
        (integralComparisonScalarSquareRight l E L ι D h k K)
  /-- The scalar comparison respects identity scheme maps before realization. -/
  systemScalarSchemeUnit : ∀ (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (N : coefficientSequenceModules l E X),
    (integralComparisonSequenceScalarPullback.{u, u} l E L ι (𝟙 X)).hom.app N ≫
        (integralComparisonSequenceUnit.{u, u} l L X).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.obj N) =
      (integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.map
        ((integralComparisonSequenceUnit.{u, u} l E X).hom.app N)
  /-- Realized scalar comparison respects the specified completed pullback unit. -/
  scalarSchemeUnit : ∀ (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X),
    (integralComparisonScalar l E L ι D (𝟙 X) K).hom ≫
        (integralComparisonUnit l L D X
          ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom =
      (integralScalarExtension l E L ι X).map (integralComparisonUnit l E D X K).hom
  /-- Identity coefficients give multiplication on systems. -/
  systemScalarIdentity : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceScalarPullback.{u, u} l E E (AlgHom.id ℚ_[l] E) f).hom.app N ≫
        (integralComparisonSequencePullback.{u, u} l E f).map
          ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app N) =
      (integralComparisonSequenceScalarUnit.{u, u} l E X).hom.app
        ((integralComparisonSequencePullback.{u, u} l E f).obj N)
  /-- Identity coefficients give the identity under multiplication and completeness. -/
  scalarIdentity : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonScalar l E E (AlgHom.id ℚ_[l] E) D f K).hom ≫
        (integralDerivedPullback l E f).map (integralComparisonScalarUnit l E Y K).hom =
      (integralComparisonScalarUnit l E X ((constructibleIntegralPullback l E f).obj K)).hom
  /-- Scalar associativity is an equation on systems with the actual tensor associator. -/
  systemScalarTower : ∀ (M : Type u) [Field M] [Algebra ℚ_[l] M]
    [FiniteDimensional ℚ_[l] M] (j : L →ₐ[ℚ_[l]] M)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (N : coefficientSequenceModules l E Y),
    (integralComparisonSequenceScalarModel.{u, u} l L M j X).E.map
        ((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l L M j f).hom.app
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj N) ≫
        (integralComparisonSequencePullback.{u, u} l M f).map
          ((integralComparisonSequenceScalarComposition.{u, u} l E L ι M j Y).hom.app N) =
      (integralComparisonSequenceScalarComposition.{u, u} l E L ι M j X).hom.app
          ((integralComparisonSequencePullback.{u, u} l E f).obj N) ≫
        (integralComparisonSequenceScalarPullback.{u, u} l E M (j.comp ι) f).hom.app N
  /-- Its realization uses the ordinary derived associator conjugated by chi. -/
  scalarTower : ∀ (M : Type u) [Field M] [Algebra ℚ_[l] M]
    [FiniteDimensional ℚ_[l] M] (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralScalarExtension l L M j X).map (integralComparisonScalar l E L ι D f K).hom ≫
        (integralComparisonScalar l L M j D f
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom ≫
        (integralDerivedPullback l M f).map
          (integralComparisonScalarAssociator l E L ι M j Y K).hom =
      (integralComparisonScalarAssociator l E L ι M j X
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
        (integralComparisonScalar l E M (j.comp ι) D f K).hom

```

The simultaneous module begins with:

```lean
public import Sheaf.Paper.IntegralPullbackComparisonRealization
```

## New

The entire preceding declaration block occurs verbatim in
`Sheaf.Paper.IntegralComparisonSystemData`, with the same prerequisites and options.
The original module retains its public prerequisites and adds:

```lean
public import Sheaf.Paper.IntegralComparisonSystemData
import Sheaf.Paper.SimultaneousIntegralPullbackComparisons
```

Its unchanged theorem statement now has this proof:

```lean
  obtain ⟨D, hD⟩ := integralPullbackComparisonRealization_simultaneous.{u} l
  exact ⟨D, hD E L ι⟩
```

The simultaneous module changes only its first import:

```lean
public import Sheaf.Paper.IntegralComparisonSystemData
```

## Users

The source-only `tools/downstream.py` audit lists the following consumers. All
existing declarations remain available under their original names, with identical
statements and bodies. Holder records were read without editing claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | X2 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | A9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AllStageCtfPullbackUnit | G4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | A4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | J2 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BoundedSiteTensorTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | S3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | C5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | R5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientDualModelTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilIterate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | C6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactExchangeOperationCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | W9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | J4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportTotalLimitRealization | C7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | C8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedInverseImageScalarCounit | U3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompletedUnitPullbackTower | D5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | E6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | D6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | A4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | E6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DlLocalHeartCoverDefects | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualizingClosedSite | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualizingCompositionCoefficientMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Y6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleLisseHomReduction | E8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteScalarMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | F6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdScalarPullbackRealizationIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | F7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | M7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | K1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | K3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | G6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteHomDomainCalculus | G7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteMateDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | K4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | H2 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | G9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | M3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | H5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | N2 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | B4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | V6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | G8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | V5 (assigned item) | Re-export the same definitions; prove the existing theorem by specialization. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransport | A6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | S5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IteratedReturnTransportScalarCalculus | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | U9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.P1CounitScalar | F4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | G1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodCounitScalarWordCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodReindexingCompletionUnitTensor | Z5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointAutomorphismDerivedTransportInverse | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | J2 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointHeartFiniteStage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointInverseImageCoefficientTower | W6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointQuotientTowerHomotopy | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointRestrictionSystemChainMap | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointScalarCompatibleTransportTransfer | H9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | R4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperFiniteNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | T3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | K9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | M7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurTateUnitFlatModelDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | X6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportFiniteComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportNormalizedLift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalPullbackFibreComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalRestrictionComparisonCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RealizedPullbackComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | V9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | Q5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfCompactSupportTowerPresentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfFrameworkThetaShiftCompatibility | C6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | R3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | T1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SimultaneousIntegralPullbackComparisons | D3 | Replace only the first public import by the shared data module to break the cycle. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityScalarExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.StrictLineHeartAssembly | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TensorExchangeCtfDomains | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TowerReductionShiftCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.UnshiftedLineUnitTower | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | E3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | A8 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | B5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | M9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | Z9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCtfRefinementComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | S6 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | E9 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | R1 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenNormalizedProductCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.PointExactRealization | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same declarations and public prerequisites through re-export; no adaptation. |

## Status

landed 20261025T043401-L-1716185 2026-10-25 (merge of deliver/V5/Sheaf.Paper.IntegralPullbackComparisonRealization)
