module

public import Sheaf.Paper.CompactSupportCondensedRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.Compactification.RefinementCategory


/-! # Data for filtered descent of condensed representing pairs

Source: blueprint sec-smooth-purity, sk-thm-sp-qbar proof, filtered Hom-colimit display
and its model-independence paragraph; sk-prop-sp-unique-adjoint-categorical proof,
Transposes, Naturality, Inverse and Uniqueness.
(blueprint: def-pur-filtered-condensed-representing-pair-data).

All categories, scalar functors, and compact-support functors below are the recorded
condensed module-object constructions. The small helper records only package the data
and conclusions of this one statement. No integral model or exceptional tower is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The existing finite-coefficient proper/open composite, restricted to bounded constructibles.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev finiteSupport (E : PadicAlgCl.FiniteIntermediateField l) :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactification
    (Profinite.continuousMapRingObj E) l c

/-- The same existing proper/open composite for the finite-subfield-valued closure ring.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev omegaSupport :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj l) l c


open CompactSupportCondensedRealization

/-- The existing inclusion comparison for the finite-coefficient support functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev finiteCompatibility (E : PadicAlgCl.FiniteIntermediateField l) :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
    (Profinite.continuousMapRingObj E) l c

/-- The existing inclusion comparison for the closure-coefficient support functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev omegaCompatibility :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
    (Profinite.padicAlgClRingObj l) l c

/-- The finite and closure scalar comparisons for the fixed compactification.
Their canonical normalization is imposed by `ScalarComparisons.IsCanonical`; no arbitrary
comparison is allowed by the main theorem.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
structure ScalarComparisons where
  finite : ∀ {E H : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ H),
    finiteSupport l k c E ⋙ constructibleExtendScalars Y.left l h ≅
      constructibleExtendScalars X.left l h ⋙ finiteSupport l k c H
  omega : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    finiteSupport l k c E ⋙ constructibleToPadicAlgCl Y.left l E ≅
      constructibleToPadicAlgCl X.left l E ⋙ omegaSupport l k c

/-- Normalization by the original coefficient projection mates, after the existing
inclusion comparisons. These equations determine every component of the comparisons.
They retain the specified scalar comparisons of compact-support condensed realization.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def ScalarComparisons.IsCanonical (s : ScalarComparisons l k c) : Prop :=
  (∀ {E H : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l E),
    (derivedExtendScalarsSubfield Y.left l h).map
        ((finiteCompatibility l k c E).inv.app C) ≫
      ((s.finite h).hom.app C).hom ≫
        (finiteCompatibility l k c H).hom.app
          ((constructibleExtendScalars X.left l h).obj C) =
      (condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app C.obj) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField l)
    (C : PadicSubfieldConstructible X.left l E),
    (derivedExtendScalarsToPadicAlgCl Y.left l E).map
        ((finiteCompatibility l k c E).inv.app C) ≫
      ((s.omega E).hom.app C).hom ≫
        (omegaCompatibility l k c).hom.app
          ((constructibleToPadicAlgCl X.left l E).obj C) =
      (condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app C.obj)


/-- A supplied finite representing pair and all its finite-overfield Hom bijections.
The counit at the base field is `t`; `Pair.IsCompatible` expresses naturality and
scalar compatibility by the counit formula, including identity scalar extension.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
structure Pair (s : ScalarComparisons l k c) (E : PadicAlgCl.FiniteIntermediateField l) where
  M : PadicSubfieldConstructible X.left l E
  L : PadicSubfieldConstructible Y.left l E
  t : (finiteSupport l k c E).obj M ⟶ L
  beta : ∀ (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l H),
    (C ⟶ (constructibleExtendScalars X.left l h).obj M) ≃
      ((finiteSupport l k c H).obj C ⟶
        (constructibleExtendScalars Y.left l h).obj L)

/-- The finite representing bijections are the natural maps determined by the extended
base counit. This is equivalent to their naturality, scalar compatibility, and the
assertion that their counits extend `t`: apply naturality to a map into `M` and its
identity. The inverse projection comparison gives the required source transport.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def Pair.IsCompatible {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E) : Prop :=
  ∀ (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l H)
    (a : C ⟶ (constructibleExtendScalars X.left l h).obj d.M),
    d.beta H h C a = (finiteSupport l k c H).map a ≫
      (s.finite h).inv.app d.M ≫ (constructibleExtendScalars Y.left l h).map d.t

/-- The represented object extended by the recorded closure scalar functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev Pair.omegaM {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E) :=
  (constructibleToPadicAlgCl X.left l E).obj d.M

/-- The target object extended by the recorded closure scalar functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev Pair.omegaL {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E) :=
  (constructibleToPadicAlgCl Y.left l E).obj d.L

/-- The extended base counit, transported through the specified projection comparison.
The inverse comparison has source the support of the extended represented object.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def Pair.omegaCounit {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E) :
    (omegaSupport l k c).obj (d.omegaM l k c) ⟶ d.omegaL l k c :=
  (s.omega E).inv.app d.M ≫ (constructibleToPadicAlgCl Y.left l E).map d.t

/-- The proposed closure-coefficient Hom bijections, for every bounded constructible test object.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev Pair.OmegaBijections {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E) :=
  ∀ C : PadicAlgClConstructible X.left l,
    (C ⟶ d.omegaM l k c) ≃ ((omegaSupport l k c).obj C ⟶ d.omegaL l k c)

/-- The finite-representative formula for the induced filtered-colimit bijection.
The tensor-transitivity comparisons identify the extensions of the represented objects.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def Pair.IsInduced {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E)
    (B : d.OmegaBijections l k c) : Prop :=
  ∀ (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l H)
    (a : C ⟶ (constructibleExtendScalars X.left l h).obj d.M),
    B ((constructibleToPadicAlgCl X.left l H).obj C)
        ((constructibleToPadicAlgCl X.left l H).map a ≫
          (constructibleToPadicAlgClCompIso X.left l h).hom.app d.M) =
      (s.omega H).inv.app C ≫
        (constructibleToPadicAlgCl Y.left l H).map (d.beta H h C a) ≫
          (constructibleToPadicAlgClCompIso Y.left l h).hom.app d.L

/-- Contravariant naturality in the test object, on the actual closure-coefficient category.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def Pair.IsNatural {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E)
    (B : d.OmegaBijections l k c) : Prop :=
  ∀ (C D : PadicAlgClConstructible X.left l) (h : D ⟶ C) (a : C ⟶ d.omegaM l k c),
    B D (h ≫ a) = (omegaSupport l k c).map h ≫ B C a


/-- A map of two supplied representing pairs, defined over any common finite overfield.
Compatibility is required on all finite-stage representing maps at that field.
Thus maps need not be defined over either pair's original coefficient field.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
structure DataMap {s : ScalarComparisons l k c}
    {E F : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (d' : Pair l k c s F) where
  H : PadicAlgCl.FiniteIntermediateField l
  hE : E ≤ H
  hF : F ≤ H
  a : (constructibleExtendScalars X.left l hE).obj d.M ⟶
    (constructibleExtendScalars X.left l hF).obj d'.M
  b : (constructibleExtendScalars Y.left l hE).obj d.L ⟶
    (constructibleExtendScalars Y.left l hF).obj d'.L
  compatible : ∀ (C : PadicSubfieldConstructible X.left l H)
    (u : C ⟶ (constructibleExtendScalars X.left l hE).obj d.M),
    d'.beta H hF C (u ≫ a) = d.beta H hE C u ≫ b

/-- The represented-object map extended from its common finite field, using the
recorded tensor-transitivity comparisons.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def DataMap.omegaA {s : ScalarComparisons l k c}
    {E F : PadicAlgCl.FiniteIntermediateField l}
    {d : Pair l k c s E} {d' : Pair l k c s F} (m : DataMap l k c d d') :
    d.omegaM l k c ⟶ d'.omegaM l k c :=
  (constructibleToPadicAlgClCompIso X.left l m.hE).inv.app d.M ≫
    (constructibleToPadicAlgCl X.left l m.H).map m.a ≫
      (constructibleToPadicAlgClCompIso X.left l m.hF).hom.app d'.M

/-- The target-object map extended from its common finite field, using the
recorded tensor-transitivity comparisons.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def DataMap.omegaB {s : ScalarComparisons l k c}
    {E F : PadicAlgCl.FiniteIntermediateField l}
    {d : Pair l k c s E} {d' : Pair l k c s F} (m : DataMap l k c d d') :
    d.omegaL l k c ⟶ d'.omegaL l k c :=
  (constructibleToPadicAlgClCompIso Y.left l m.hE).inv.app d.L ≫
    (constructibleToPadicAlgCl Y.left l m.H).map m.b ≫
      (constructibleToPadicAlgClCompIso Y.left l m.hF).hom.app d'.L

/-- All conclusions for the descended representing bijection: the finite representative
formula; test-object naturality; the extended-counit formula and its identity value;
uniqueness among induced natural bijections; independence of every finite object model,
identifying isomorphism and morphism representative; the invertible counit-preserving
transpose under every specified adjunction and its uniqueness; and naturality of both
the bijections and their transposes in common-finite-field maps of supplied pairs.
The explicit `adj.homEquiv` and counit equation retain dependence on the chosen counit.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
def Pair.IsDescent {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E)
    (B : d.OmegaBijections l k c) : Prop :=
  d.IsInduced l k c B ∧ d.IsNatural l k c B ∧
  (∀ (C : PadicAlgClConstructible X.left l) (u : C ⟶ d.omegaM l k c),
    B C u = (omegaSupport l k c).map u ≫ d.omegaCounit l k c) ∧
  B (d.omegaM l k c) (𝟙 _) = d.omegaCounit l k c ∧
  (∀ B' : d.OmegaBijections l k c,
    d.IsInduced l k c B' → d.IsNatural l k c B' → B' = B) ∧
  (∀ (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (D : PadicSubfieldConstructible X.left l H) (C : PadicAlgClConstructible X.left l)
    (e : (constructibleToPadicAlgCl X.left l H).obj D ≅ C)
    (u : C ⟶ d.omegaM l k c)
    (v : D ⟶ (constructibleExtendScalars X.left l h).obj d.M),
    e.hom ≫ u = (constructibleToPadicAlgCl X.left l H).map v ≫
      (constructibleToPadicAlgClCompIso X.left l h).hom.app d.M →
    B C u = (omegaSupport l k c).map e.inv ≫ (s.omega H).inv.app D ≫
      (constructibleToPadicAlgCl Y.left l H).map (d.beta H h D v) ≫
        (constructibleToPadicAlgClCompIso Y.left l h).hom.app d.L) ∧
  (∀ (J : PadicAlgClConstructible Y.left l ⥤ PadicAlgClConstructible X.left l)
    (adj : omegaSupport l k c ⊣ J),
    IsIso (adj.homEquiv (d.omegaM l k c) (d.omegaL l k c) (d.omegaCounit l k c)) ∧
    (omegaSupport l k c).map
        (adj.homEquiv (d.omegaM l k c) (d.omegaL l k c) (d.omegaCounit l k c)) ≫
      adj.counit.app (d.omegaL l k c) = d.omegaCounit l k c ∧
    (∀ v : d.omegaM l k c ⟶ J.obj (d.omegaL l k c),
      (omegaSupport l k c).map v ≫ adj.counit.app (d.omegaL l k c) =
        d.omegaCounit l k c →
      v = adj.homEquiv (d.omegaM l k c) (d.omegaL l k c) (d.omegaCounit l k c))) ∧
  (∀ (F : PadicAlgCl.FiniteIntermediateField l) (d' : Pair l k c s F),
    d'.IsCompatible l k c → ∀ (B' : d'.OmegaBijections l k c),
    d'.IsInduced l k c B' → d'.IsNatural l k c B' → ∀ m : DataMap l k c d d',
    (∀ (C : PadicAlgClConstructible X.left l) (u : C ⟶ d.omegaM l k c),
      B' C (u ≫ m.omegaA l k c) = B C u ≫ m.omegaB l k c) ∧
    (∀ (J : PadicAlgClConstructible Y.left l ⥤ PadicAlgClConstructible X.left l)
      (adj : omegaSupport l k c ⊣ J),
      m.omegaA l k c ≫
          adj.homEquiv (d'.omegaM l k c) (d'.omegaL l k c) (d'.omegaCounit l k c) =
        adj.homEquiv (d.omegaM l k c) (d.omegaL l k c) (d.omegaCounit l k c) ≫
          J.map (m.omegaB l k c)))

end WeilConjectures.FilteredCondensedRepresentingPair
