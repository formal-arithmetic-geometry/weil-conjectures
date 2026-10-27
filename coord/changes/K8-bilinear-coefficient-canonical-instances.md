# BilinearCoefficientDescent records and coefficient constructions

## Reason

The retained full proof exceeded the per-file compile limit. Make its data cheaper
to elaborate while preserving the same objects, maps and coherence equations.
Units uses a subtype. Family and Transformation use structures with compact
internal fields and proved wrappers retaining their original named projections,
constructors and laws. FamilyTower and TransformationSquare name their unchanged
proof constraints. UnitLaws names the two unit cocycles. The ordinary callable data
types remain explicit in the structure layouts, as required by Lean's module compiler.
The sole consumer uses the specifications, not record literals or recursors.
All 20 original theorem signatures remain textually unchanged.

Five specification predicates use proposition structures with exactly their original
two clauses. The public iff lemmas below prove equivalence with each old definition.
Numeric projections and anonymous constructors continue to work for the consumer.
This makes the specification type itself a constant and gives its clauses native
projections. No hypothesis or conclusion is weakened.

The bilinear linear map is stored as private rawHomLinear. Private rawHom evaluates
its two toFun projections as an ordinary curried function. Six proved private
zero/addition/scalar formulas and the pure-tensor formula provide its bilinearity API.
The later tensor proofs use those formulas and the specialized LinearMap and
AddMonoidHom laws, avoiding repeated CoeFun/ZeroHomClass/AddHomClass searches.
The linear map and its evaluation wrapper stay folded after this API is proved.
Private tensorComp likewise evaluates the existing scalar-localized composition
map as a plain function. Its zero/addition and pure-tensor laws are proved from
the existing composition map. All private simp rules are local; no simp attribute
is added to the consumer environment.
The private pairing construction also stays folded after its common-stage API.
A local priority for Mathlib's existing vector-space torsion-free instance avoids
repeated searches on the coefficient fields; it adds no Hom torsion hypothesis.

The two coefficient instances now use the canonical subring constructors directly.
The named `Integers` subring hides the transparent alias; `Integers_eq` proves it is
exactly the recorded coefficient-extension subring. The uniformizer explicitly uses
the same recorded field element, with membership supplied by `uniformizer_mem`.
No new object is selected and no Hom module receives a torsion-free hypothesis.
The localization proof explicitly unfolds these identifications at its two conversion
steps, including their implicit ring and algebra instances.

The raw and common-stage functors have their prescribed object fields explicitly,
using `withObjects`. This constructor transports maps along the supplied equalities;
`withObjects_eq` proves that it is equal to the original functor. The original
existence-and-uniqueness prescriptions therefore characterize exactly the same
functors. The private diagonal and explicitDescent also use direct object fields
and retain their old composite maps and laws; equality with the composite is proved.
Both respectTransparency options remain true; no profiling/debug options are delivered.

Construct the integer inclusion directly by restricting the field inclusion to the
named subrings. Spectral-norm uniqueness and the DVR membership formula prove its
membership property. The geometric scalar-extension construction, additive
pair-category structure and finite integer-ring quotients are not used in the proof.
Their original public imports remain to preserve downstream declarations, repairing
the import-pruning return. No adopted source-library declaration changes.

## Old

```lean
structure Units (S : StageSystem A) where
  unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)
  left : ∀ {i j : I} (h : i ≤ j) (X : A i),
    (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X)
  right : ∀ {i j : I} (h : i ≤ j) (X : A i),
    (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)
```

```lean
structure Family where
  U : ∀ i, A i × A₂ i ⥤ B i
  comparison : ∀ {i j : I} (h : i ≤ j),
    U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j
  tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)
```

```lean
structure Transformation (U V : Family S S₂ T) where
  app : ∀ i, U.U i ⟶ V.U i
  square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (app j).app ((S.T h).obj X, (S₂.T h).obj Y)
```

```lean
instance integersCommRing (E : Padic.FiniteCoefficientFields l Ω) :
    CommRing (Integers l Ω E) :=
  inferInstanceAs (CommRing (Padic.coefficientExtensionIntegers l E.val))

instance integersAlgebra (E : Padic.FiniteCoefficientFields l Ω) :
    Algebra (Integers l Ω E) E.val :=
  inferInstanceAs (Algebra (Padic.coefficientExtensionIntegers l E.val) E.val)
```

```lean
def integerInclusion {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    Integers l Ω E →+* Integers l Ω L :=
  WeilConjectures.integralScalarIntegerInclusion l E.val L.val (IntermediateField.inclusion h)
```

```lean
abbrev Integers (E : Padic.FiniteCoefficientFields l Ω) :=
  Padic.coefficientExtensionIntegers l E.val

def uniformizer (E : Padic.FiniteCoefficientFields l Ω) : Integers l Ω E :=
  Padic.coefficientExtensionUniformizer l E.val

def raw (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :=
  (raw_extension_existsUnique p U hU).exists.choose

def descend (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  (descent_existsUnique U join left right).exists.choose
```

## New

```lean
@[no_expose] def UnitComparisons (S : StageSystem A) := ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)

/-- The two cocycles stored with specified identity comparisons.
Source: common-stage unit equations
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitLaws (S : StageSystem A) (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)) :
    Prop :=
  (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X)) ∧
    (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X))

/-- Specified identity comparisons and their two unit cocycles.
Source: common-stage formula, supplied identity and tower isomorphisms
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Units (S : StageSystem A) :=
  {unit : UnitComparisons S // UnitLaws S unit}

namespace Units

@[no_expose, implicit_reducible] def unit {S : StageSystem A} (uS : Units S) :
    ∀ i, S.T (le_refl i) ≅ 𝟭 (A i) := uS.val

omit [IsDirectedOrder I] in
theorem left {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((uS.unit i).hom.app X) :=
  uS.property.1 h X

omit [IsDirectedOrder I] in
theorem right {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc h (le_refl j)).hom.app X = (uS.unit j).hom.app ((S.T h).obj X) :=
  uS.property.2 h X

@[no_expose] def mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    Units S := ⟨unit, left, right⟩


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem unit_mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    (mk unit left right).unit = unit := by
  exact Eq.trans rfl rfl

end Units
```

```lean
@[no_expose] def FamilyTower (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j) : Prop :=
  ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)

/-- A bilinear family with the specified scalar comparison and its tower equation.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Linearity is imposed separately at integral stages, not on this purely categorical interface. -/
structure Family where
  mkData ::
  functors : ∀ i, A i × A₂ i ⥤ B i
  comparisons : ∀ {i j : I} (h : i ≤ j),
    functors i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ functors j
  coherence : FamilyTower S S₂ T functors comparisons

namespace Family

variable {S S₂ T}

@[no_expose, implicit_reducible] def U (F : Family S S₂ T) : ∀ i, A i × A₂ i ⥤ B i := F.functors

@[no_expose, implicit_reducible] def comparison (F : Family S S₂ T) {i j : I} (h : i ≤ j) :
    F.U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ F.U j := F.comparisons h

omit [IsDirectedOrder I] in
theorem tower (F : Family S S₂ T) :
    ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((F.comparison h).hom.app (X, Y)) ≫
      (F.comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (F.U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((F.U i).obj (X, Y)) ≫
      (F.comparison (h.trans h')).hom.app (X, Y) :=
  F.coherence

@[no_expose] def mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) : Family S S₂ T := Family.mkData U comparison tower


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem U_mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) :
    (mk U comparison tower).U = U := by
  exact Eq.trans rfl rfl

/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem comparison_mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y))
    {i j : I} (h : i ≤ j) :
    HEq ((mk U comparison tower).comparison h) (comparison h) := by
  exact HEq.trans HEq.rfl HEq.rfl

end Family
```

```lean
@[no_expose] def TransformationSquare (U V : Family S S₂ T)
    (app : ∀ i, U.U i ⟶ V.U i) : Prop :=
  ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (app j).app ((S.T h).obj X, (S₂.T h).obj Y)

/-- Compatible transformations, including the scalar square of the statement.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure Transformation (U V : Family S S₂ T) where
  mkData ::
  components : ∀ i, U.U i ⟶ V.U i
  compatibility : TransformationSquare U V components

namespace Transformation

variable {U V : Family S S₂ T}

@[no_expose, implicit_reducible] def app (η : Transformation U V) (i : I) :
    U.U i ⟶ V.U i := η.components i

omit [IsDirectedOrder I] in
theorem square (η : Transformation U V) :
    ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((η.app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (η.app j).app ((S.T h).obj X, (S₂.T h).obj Y) := η.compatibility

@[no_expose] def mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) : Transformation U V :=
  Transformation.mkData app square


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem app_mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) :
    (mk app square).app = app := by
  exact Eq.trans rfl rfl

end Transformation
```

```lean
/-- Give a functor its prescribed object function, transporting its morphisms.
Source: transport along object equalities
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def withObjects
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) : C₀ ⥤ D₀ where
  obj := obj
  map {X Y} f := eqToHom (h X).symm ≫ F.map f ≫ eqToHom (h Y)
  map_id X := by
    simp only [F.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  map_comp f g := by
    simp only [F.map_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- Object normalization preserves the functor itself.
Source: equality of functors by object equality and heterogeneous map equality
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem withObjects_eq
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) :
    withObjects F obj h = F := by
  unfold withObjects
  apply Functor.hext (fun X ↦ (h X).symm)
  intro X Y f
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The unique raw extension; all its data are determined by the preceding prescription.
Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def raw (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :=
  withObjects (raw_extension_existsUnique p U hU).exists.choose
    (fun X ↦ ⟨U.obj (X.1.obj, X.2.obj)⟩)
    (raw_extension_existsUnique p U hU).exists.choose_spec.2.1

/-- The chosen raw functor satisfies the full extension prescription.
Source: the proved unique extension
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem raw_spec (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :
    IsRawExtension p U (raw p U hU) := by
  unfold raw
  rw [withObjects_eq]
  exact (raw_extension_existsUnique p U hU).exists.choose_spec

/-- The raw extension retains the stipulated object.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem raw_obj (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X : ScalarLocalization R C p × ScalarLocalization R C p) :
    (raw p U hU).obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩ := by
  exact Eq.trans rfl rfl
```

```lean
/-- The unique representative-normalized descended bifunctor.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def descend (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  withObjects (descent_existsUnique U join left right).exists.choose
    (output U join left right)
    (descent_existsUnique U join left right).exists.choose_spec.1

/-- The chosen common-stage functor satisfies the complete representative prescription.
Source: the proved unique descent
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem descend_spec (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    IsDescent U join left right (descend U join left right) := by
  unfold descend
  rw [withObjects_eq]
  exact (descent_existsUnique U join left right).exists.choose_spec
```

```lean
/-- The recorded valuation rings, indexed by the genuine finite intermediate extensions.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Integers (E : Padic.FiniteCoefficientFields l Ω) : Subring E.val :=
  Padic.coefficientExtensionIntegers l E.val

/-- The named integer ring is exactly the recorded coefficient-extension subring.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem Integers_eq (E : Padic.FiniteCoefficientFields l Ω) :
    Integers l Ω E = Padic.coefficientExtensionIntegers l E.val := by
  exact Eq.trans rfl rfl

/-- Cache the recorded valuation ring's commutative-ring instance.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance integersCommRing (E : Padic.FiniteCoefficientFields l Ω) :
    CommRing (Integers l Ω E) :=
  Subring.toCommRing (Integers l Ω E)

attribute [local implicit_reducible] integersCommRing

/-- Cache the canonical valuation-subring algebra structure on its coefficient field.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance integersAlgebra (E : Padic.FiniteCoefficientFields l Ω) :
    Algebra (Integers l Ω E) E.val :=
  @Algebra.ofSubsemiring E.val E.val _ _ (Algebra.id E.val)
    (Subring E.val) _ _ (Integers l Ω E)

attribute [local implicit_reducible] integersAlgebra

/-- The recorded uniformizer belongs to the named integer subring.
Source: the coefficient uniformizer definition and `Integers_eq`
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem uniformizer_mem (E : Padic.FiniteCoefficientFields l Ω) :
    (Padic.coefficientExtensionUniformizer l E.val : E.val) ∈ Integers l Ω E := by
  rw [Integers_eq]
  exact (Padic.coefficientExtensionUniformizer l E.val).property

/-- The recorded uniformizer; no extra torsion-free or characteristic hypotheses.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def uniformizer (E : Padic.FiniteCoefficientFields l Ω) : Integers l Ω E :=
  ⟨(Padic.coefficientExtensionUniformizer l E.val : E.val), uniformizer_mem l Ω E⟩

private theorem integerInclusion_absoluteValue
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (x : E.val) :
    Padic.coefficientExtensionAbsoluteValue l L.val (IntermediateField.inclusion h x) =
      Padic.coefficientExtensionAbsoluteValue l E.val x := by
  let ι := IntermediateField.inclusion h
  let f : AbsoluteValue E.val ℝ :=
    (Padic.coefficientExtensionAbsoluteValue l L.val).comp ι.toRingHom.injective
  have hf : ∀ a : Padic l, f (algebraMap (Padic l) E.val a) = ‖a‖ := by
    intro a
    change Padic.coefficientExtensionAbsoluteValue l L.val
      (ι (algebraMap (Padic l) E.val a)) = ‖a‖
    rw [ι.commutes]
    exact spectralNorm_extends a
  exact spectralNorm_unique_field_norm_ext hf x

/-- The field inclusion preserves the recorded valuation subrings.
Source: spectral-norm uniqueness and the defining DVR membership formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof: the absolute value on the larger field restricts to the unique extension
of the p-adic absolute value on the smaller field. Integer-ring membership is
absolute value at most one in both fields, so the restriction preserves it. -/
theorem integerInclusion_mem {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (x : Integers l Ω E) :
    IntermediateField.inclusion h (x : E.val) ∈ Integers l Ω L := by
  have hE := (Padic.extension_integers_dvr l E.val
    (Padic.coefficientExtensionAbsoluteValue l E.val)
    (spectralNorm_extends (K := Padic l) (L := E.val))).choose_spec.choose_spec.1 (x : E.val)
  have hL := (Padic.extension_integers_dvr l L.val
    (Padic.coefficientExtensionAbsoluteValue l L.val)
    (spectralNorm_extends (K := Padic l) (L := L.val))).choose_spec.choose_spec.1
      (IntermediateField.inclusion h (x : E.val))
  have hx : Padic.coefficientExtensionAbsoluteValue l E.val (x : E.val) ≤ 1 := by
    apply hE.mp
    simpa only [Integers, Padic.coefficientExtensionIntegers] using x.property
  rw [← integerInclusion_absoluteValue l Ω h (x : E.val)] at hx
  simpa only [Integers, Padic.coefficientExtensionIntegers] using hL.mpr hx

/-- The canonical integer-ring restriction of the given intermediate-field inclusion.
Source: common-stage coefficient formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def integerInclusion {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    Integers l Ω E →+* Integers l Ω L :=
  ((IntermediateField.inclusion h).toRingHom.comp
    (Integers l Ω E).subtype).codRestrict
      (Integers l Ω L) (integerInclusion_mem l Ω h)
```

The uniformizer and integer inclusion additionally use
`no_expose` so their canonical data remain folded in exported artifacts. Their
proved equations are:

```lean
theorem uniformizer_val (E : Padic.FiniteCoefficientFields l Ω) :
    (uniformizer l Ω E : E.val) = (Padic.coefficientExtensionUniformizer l E.val : E.val) := by
  exact Eq.trans rfl rfl

theorem integerInclusion_apply {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (x : Integers l Ω E) :
    (integerInclusion l Ω h x : L.val) = IntermediateField.inclusion h (x : E.val) := by
  exact Eq.trans rfl rfl
```

## Specification predicates

The following old definitions are replaced by proposition structures. Each new
iff theorem is proved by constructing or projecting the same two clauses.

Old:

```lean
def IsSeparatelyLinear (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) : Prop :=
  (∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R) ∧
  (∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R)
```

New, including its equivalence proof:

```lean
structure IsSeparatelyLinear (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) : Prop where
  right :
    ∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R
  left :
    ∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isSeparatelyLinear_iff (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) :
    IsSeparatelyLinear R U ↔
  (∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R) ∧
  (∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
```

Old:

```lean
def IsRawExtension (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) : Prop :=
  IsSeparatelyLinear (Localization.Away p) F ∧
  (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
    F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
  ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
    HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
      (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g))
```

New, including its equivalence proof:

```lean
structure IsRawExtension (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) : Prop where
  linear :
    IsSeparatelyLinear (Localization.Away p) F
  formula :
      (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
      F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
    ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
      HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
        (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRawExtension_iff (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) :
    IsRawExtension p U F ↔
  IsSeparatelyLinear (Localization.Away p) F ∧
  (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
    F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
  ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
    HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
      (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
```

Old:

```lean
def IsDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) : Prop :=
  (∀ X, F.obj X = output U join left right X) ∧
  ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
    HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
      StageSystem.PairCategory.mkHom L _ _ g))
      (StageSystem.PairCategory.mkHom (X := output U join left right X)
        (Y := output U join left right Y) L hX hY
        ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
          (endpoint U join left right Y hY).inv))
```

New, including its equivalence proof:

```lean
structure IsDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) : Prop where
  objects :
    ∀ X, F.obj X = output U join left right X
  arrows :
    ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
      (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
      (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
      (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
      HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
        StageSystem.PairCategory.mkHom L _ _ g))
        (StageSystem.PairCategory.mkHom (X := output U join left right X)
          (Y := output U join left right Y) L hX hY
          ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
            (endpoint U join left right Y hY).inv))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isDescent_iff (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) :
    IsDescent U join left right F ↔
  (∀ X, F.obj X = output U join left right X) ∧
  ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
    HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
      StageSystem.PairCategory.mkHom L _ _ g))
      (StageSystem.PairCategory.mkHom (X := output U join left right X)
        (Y := output U join left right Y) L hX hY
        ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
          (endpoint U join left right Y hY).inv)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
```

Old:

```lean
def IsRationalSystem
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))) : Prop :=
  (∀ {i j : I} (h : i ≤ j), Q.T h =
    ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ∧
  (∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i),
    HEq ((Q.assoc h h').hom.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').hom.app X) ∧
    HEq ((Q.assoc h h').inv.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').inv.app X))
```

New, including its equivalence proof:

```lean
structure IsRationalSystem
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))) : Prop where
  transitions :
    ∀ {i j : I} (h : i ≤ j), Q.T h =
      ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)
  associators :
    ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i),
      HEq ((Q.assoc h h').hom.app ⟨X⟩)
        ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').hom.app X) ∧
      HEq ((Q.assoc h h').inv.app ⟨X⟩)
        ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').inv.app X)

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRationalSystem_iff
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))) :
    IsRationalSystem π φ unitImage S semi Q ↔
  (∀ {i j : I} (h : i ≤ j), Q.T h =
    ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ∧
  (∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i),
    HEq ((Q.assoc h h').hom.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').hom.app X) ∧
    HEq ((Q.assoc h h').inv.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').inv.app X)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
```

Old:

```lean
def IsRationalFamily
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    {T : StageSystem B} (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))}
    {P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i))}
    (F : Family Q Q P) : Prop :=
  (∀ i, F.U i = raw (π i) (U.U i) (hU i)) ∧
  (∀ {i j : I} (h : i ≤ j) (X Y : A i),
    HEq ((F.comparison h).hom.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) ∧
    HEq ((F.comparison h).inv.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).inv.app (X, Y)))
```

New, including its equivalence proof:

```lean
structure IsRationalFamily
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    {T : StageSystem B} (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))}
    {P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i))}
    (F : Family Q Q P) : Prop where
  functors :
    ∀ i, F.U i = raw (π i) (U.U i) (hU i)
  comparisons :
    ∀ {i j : I} (h : i ≤ j) (X Y : A i),
      HEq ((F.comparison h).hom.app (⟨X⟩, ⟨Y⟩))
        ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) ∧
      HEq ((F.comparison h).inv.app (⟨X⟩, ⟨Y⟩))
        ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).inv.app (X, Y))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRationalFamily_iff
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    {T : StageSystem B} (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))}
    {P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i))}
    (F : Family Q Q P) :
    IsRationalFamily U hU F ↔
  (∀ i, F.U i = raw (π i) (U.U i) (hU i)) ∧
  (∀ {i j : I} (h : i ≤ j) (X Y : A i),
    HEq ((F.comparison h).hom.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) ∧
    HEq ((F.comparison h).inv.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).inv.app (X, Y))) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
```

## Users

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BilinearCoefficientDescent | K8 | Equivalent record data and normalized coefficient constructions. |
| Sheaf.Paper.WeilTensorComparisonRationalDescent | unclaimed (previously Q2) | Sole direct importer; unchanged. Original public imports are retained. |

A current import search finds only the downstream module above. No target statement
changes. The integer-ring identification and object-normalization equations establish
that the repaired definitions retain their original mathematical meaning. The return
is repaired by restoring all three flagged public imports in the item. No downstream
adaptation is included. Validation details are in report.md.

## Status

landed 20261026T070219-L-3467120 2026-10-26 (merge of deliver/K8/Sheaf.CategoryTheory.BilinearCoefficientDescent)
