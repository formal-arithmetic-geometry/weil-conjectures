/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Mathlib.CategoryTheory.PathCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients

/-! # Mixed geometric and scalar coherence on strict quotient systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D and the generator calculations
of the DAG node (blueprint: lem-trf-quotient-system-mixed-coherence).

The equations are asserted both before localization and in the unbounded derived
categories of entire quotient diagrams. Finite geometric coherence quantifies over
all binary assemblies of an arbitrary path, including the empty path. No realization,
normalization, boundedness, Tor-amplitude or flatness assumption is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u a v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem sequenceDerived_ext
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) {D : Type a} [Category.{v} D]
    {F G : coefficientSequenceDerived l E X ⥤ D} (α β : F ⟶ G)
    (h : ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) K
  let := hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).mp
  rw [α.naturality, β.naturality, h P hP]

section ScalarComparisons

variable (l : ℕ) [Fact l.Prime]
  (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)

/-- The scalar associator is uniquely determined by its ordinary tensor formula and
universal cochain counits. Source: Stacks 06YY, 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence).
Proof: resolve an input by one flat-term K-flat complex on the sequence site.
Ordinary extension preserves these complexes, including under successive coefficient
maps. The three universal counits are therefore invertible. Conjugate the localization
of the ordinary associator, c tensor (b tensor x) to c*j(b) tensor x, by these counits.
Naturality and the universal derived property descend this map to the localization;
the inverse ordinary associator gives its inverse. Cancellation of the resolution
isomorphisms proves uniqueness. The calculation uses neither flatness of the ring maps
nor a bound on the input complex. -/
theorem integralComparisonSystemScalarComposition_existsUnique (X : Scheme.{t}) :
    ∃! a : integralComparisonDerivedSequenceScalar l E L ι X ⋙
        integralComparisonDerivedSequenceScalar l L M j X ≅
      integralComparisonDerivedSequenceScalar l E M (j.comp ι) X,
      ∀ (P : CochainComplex (coefficientSequenceModules l E X) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X) P →
        a.hom.app (DerivedCategory.Q.obj P) ≫
            (integralComparisonSequenceScalarModel l E M (j.comp ι) X).ε.app P =
          (integralComparisonDerivedSequenceScalar l L M j X).map
              ((integralComparisonSequenceScalarModel l E L ι X).ε.app P) ≫
            (integralComparisonSequenceScalarModel l L M j X).ε.app
              (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
                (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (integralComparisonSequenceScalarComposition l E L ι M j X)
                  (.up ℤ)).hom.app P) := by
  let A := coefficientSequenceModules l E X
  let ma := integralComparisonSequenceScalarModel l E L ι X
  let mb := integralComparisonSequenceScalarModel l L M j X
  let mc := integralComparisonSequenceScalarModel l E M (j.comp ι) X
  let e := integralComparisonSequenceScalarComposition l E L ι M j X
  let δ : DerivedCategory.Q ⋙ (ma.T ⋙ mb.T) ⟶
      mc.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := Functor.whiskerRight ma.ε mb.T ≫
    Functor.whiskerLeft (ma.E.mapHomologicalComplex (.up ℤ)) mb.ε ≫
    Functor.whiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)).hom DerivedCategory.Q
  let := mc.universal
  let c := mc.T.leftDerivedLift mc.ε (HomologicalComplex.quasiIso A (.up ℤ))
    (ma.T ⋙ mb.T) δ
  have hc (P : CochainComplex A ℤ) :
      c.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P =
        mb.T.map (ma.ε.app P) ≫ mb.ε.app
          ((ma.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) :=
    mc.T.leftDerived_fac_app mc.ε (HomologicalComplex.quasiIso A (.up ℤ)) _ δ P
  have hciso (P : CochainComplex A ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P)
      (hflat : ∀ n : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E X)) (P.X n))) :
      IsIso (c.app (DerivedCategory.Q.obj P)) := by
    have hPa := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (integralComparisonSequenceScalarMap l E L ι X) P ma.E ma.obj_eq ma.map_eq hP hflat).1
    have := ma.computes P hP
    have := mb.computes _ hPa
    have := mc.computes P hP
    have : IsIso (c.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (mc.ε.app P)
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    let P := DerivedCategory.Q.objPreimage K
    rw [NatTrans.isIso_app_iff_of_iso c (DerivedCategory.Q.objObjPreimageIso K).symm]
    obtain ⟨R, f, hR, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P
    let := hf
    have : IsIso (DerivedCategory.Q.map f) := inferInstance
    have := hciso R hR hflat
    have h := c.naturality (DerivedCategory.Q.map f)
    have : IsIso (((ma.T ⋙ mb.T).map (DerivedCategory.Q.map f)) ≫
        c.app (DerivedCategory.Q.obj P)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ma.T ⋙ mb.T).map (DerivedCategory.Q.map f)) _
  refine ⟨asIso c, fun P _ ↦ hc P, ?_⟩
  intro b hb
  apply Iso.ext
  apply sequenceDerived_ext l E X b.hom c
  intro P hP
  have := mc.computes P hP
  apply (cancel_mono (mc.ε.app P)).mp
  exact (hb P hP).trans (hc P).symm

/-- The canonical derived associator, with multiplication normalization before localization.
Source: Stacks 06YY, 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralComparisonSystemScalarComposition (X : Scheme.{t}) :=
  (integralComparisonSystemScalarComposition_existsUnique l E L M ι j X).exists.choose

/-- The derived scalar unit is the localization of multiplication, with its canonical
cochain counit. Source: Stacks 06YY
(blueprint: lem-trf-quotient-system-mixed-coherence).
Proof: on a K-flat representative localize the ordinary multiplication unitor and
precede it by the universal derived counit. This is invertible there. K-flat resolutions
and naturality extend it to every derived object; cancellation of each resolution
isomorphism gives uniqueness. The inverse inserts the scalar one. -/
theorem integralComparisonSystemScalarUnit_existsUnique (X : Scheme.{t}) :
    ∃! a : integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ (P : CochainComplex (coefficientSequenceModules l E X) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X) P →
        a.hom.app (DerivedCategory.Q.obj P) =
          (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).ε.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (integralComparisonSequenceScalarUnit l E X) (.up ℤ)).hom.app P) := by
  let A := coefficientSequenceModules l E X
  let m := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let e := integralComparisonSequenceScalarUnit l E X
  let d : m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  let β : DerivedCategory.Q ⋙ 𝟭 (coefficientSequenceDerived l E X) ⟶
      m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := d.inv
  let := m.universal
  let : (𝟭 (coefficientSequenceDerived l E X)).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (asIso β)
  let c := Functor.leftDerivedNatIso m.T (𝟭 _) m.ε β
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _)
  have hc (P : CochainComplex A ℤ) :
      c.hom.app (DerivedCategory.Q.obj P) = m.ε.app P ≫ d.hom.app P := by
    have h := Functor.leftDerivedNatTrans_app m.T (𝟭 _) m.ε β
      (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 _) P
    change c.hom.app (DerivedCategory.Q.obj P) ≫ d.inv.app P = m.ε.app P ≫ 𝟙 _ at h
    simpa using congrArg (fun f ↦ f ≫ d.hom.app P) h
  refine ⟨c, fun P _ ↦ hc P, ?_⟩
  intro b hb
  apply Iso.ext
  exact sequenceDerived_ext l E X b.hom c.hom (fun P hP ↦ (hb P hP).trans (hc P).symm)

/-- The derived scalar multiplication unitor on the whole quotient diagram.
Source: Stacks 06YY (blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralComparisonSystemScalarUnit (X : Scheme.{t}) :=
  (integralComparisonSystemScalarUnit_existsUnique l E X).exists.choose


end ScalarComparisons

/-- Every scheme occurring in the finite string has ell invertible.
Source: the standing scheme hypothesis of the node
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def IntegralQuotientPathInvertible (l : ℕ) {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}}, Quiver.Path X Y → Prop
  | _, .nil => ∀ x : X, Nonempty (Invertible (l : X.residueField x))
  | Y, .cons p _ => IntegralQuotientPathInvertible l p ∧
      ∀ y : Y, Nonempty (Invertible (l : Y.residueField y))

/-- Binary parenthesizations of a fixed finite string, with empty pieces permitted.
Source: the finite-string assertion of the node, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
inductive IntegralQuotientBracketing :
    {X Y : Scheme.{t}} → Quiver.Path X Y → Type (t + 1)
  | nil (X : Scheme.{t}) : IntegralQuotientBracketing (Quiver.Path.nil : Quiver.Path X X)
  | single {X Y : Scheme.{t}} (f : X ⟶ Y) : IntegralQuotientBracketing f.toPath
  | comp {X Y Z : Scheme.{t}} {p : Quiver.Path X Y} {q : Quiver.Path Y Z}
      (a : IntegralQuotientBracketing p) (b : IntegralQuotientBracketing q) :
      IntegralQuotientBracketing (p.comp q)

/-- Interpret the parenthesized string by iterated pullback, retaining its entire diagram.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientBracketFunctor
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X)) :
    ∀ {X Y : Scheme.{t}} {p : Quiver.Path X Y},
      IntegralQuotientBracketing p → (D Y ⥤ D X)
  | _, _, _, .nil _ => 𝟭 _
  | _, _, _, .single f => U f
  | _, _, _, .comp a b =>
      integralQuotientBracketFunctor D U b ⋙ integralQuotientBracketFunctor D U a

/-- The comparison associated to a parenthesization, recursively using only the given
canonical compositor and inverse-image unitor. Equal composites use equality transport.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientBracketComparison
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
    (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X)) :
    ∀ {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p),
      U (CategoryTheory.composePath p) ≅ integralQuotientBracketFunctor D U b
  | _, _, _, .nil X => e X
  | _, _, _, .single f =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_toPath f))
  | _, _, _, .comp (p := p) (q := q) a b =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_comp p q)) ≪≫
        c (CategoryTheory.composePath p) (CategoryTheory.composePath q) ≪≫
        Functor.isoWhiskerLeft (U (CategoryTheory.composePath q))
          (integralQuotientBracketComparison D U c e a) ≪≫
        Functor.isoWhiskerRight (integralQuotientBracketComparison D U c e b)
          (integralQuotientBracketFunctor D U a)

/-- Clause-by-clause packaging of mixed coherence; every field is an equality of the
specified transformations, rather than an assumption supplying arbitrary comparisons.
Source: Stacks 0D6D, with the node's mixed tensor-generator calculations
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
structure IntegralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] : Prop where
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  ordinary_mixed : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {V W Z : Scheme.{t}}
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (h : Z ⟶ W) (k : W ⟶ V),
    Functor.whiskerRight (integralComparisonSequenceComposition l E h k).hom
      ((integralComparisonSequenceScalarModel l E L ι Z).E) ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E k)
          (integralComparisonSequenceScalarPullback l E L ι h).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι k).hom
          (integralComparisonSequencePullback l L h) =
      (integralComparisonSequenceScalarPullback l E L ι (h ≫ k)).hom ≫
        Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι V).E)
          (integralComparisonSequenceComposition l L h k).hom
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  ordinary_scalar_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    (integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarUnit l E Y).hom
          (integralComparisonSequencePullback l E f) =
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceScalarUnit l E X).hom
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  ordinary_scalar_tower : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι f).hom
      ((integralComparisonSequenceScalarModel l L M j X).E) ≫
        Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι Y).E)
          (integralComparisonSequenceScalarPullback l L M j f).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarComposition l E L ι M j Y).hom
          (integralComparisonSequencePullback l M f) =
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
          (integralComparisonSequenceScalarComposition l E L ι M j X).hom ≫
        (integralComparisonSequenceScalarPullback l E M (j.comp ι) f).hom
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  ordinary_associative : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T V W Z : Scheme.{t}}
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
    (integralComparisonSequenceComposition l E (f ≫ g) h).hom ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E h)
          (integralComparisonSequenceComposition l E f g).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.assoc f g h)) ≫
        (integralComparisonSequenceComposition l E f (g ≫ h)).hom ≫
        Functor.whiskerRight (integralComparisonSequenceComposition l E g h).hom
          (integralComparisonSequencePullback l E f)
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  ordinary_unital : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    ((integralComparisonSequenceComposition l E (𝟙 X) f).hom ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E f)
          (integralComparisonSequenceUnit l E X).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.id_comp f))) ∧
    ((integralComparisonSequenceComposition l E f (𝟙 Y)).hom ≫
        Functor.whiskerRight (integralComparisonSequenceUnit l E Y).hom
          (integralComparisonSequencePullback l E f) =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.comp_id f)))
  /-- All parenthesizations of every finite string give the same comparison. -/
  ordinary_finite : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
    (a b : IntegralQuotientBracketing p),
    ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E) a =
      integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E) b,
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E)
        (integralComparisonSequenceComposition.{t, u} l E)
        (integralComparisonSequenceUnit.{t, u} l E) a ≪≫ eqToIso h =
      integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E)
        (integralComparisonSequenceComposition.{t, u} l E)
        (integralComparisonSequenceUnit.{t, u} l E) b
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  derived_mixed : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {V W Z : Scheme.{t}}
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (h : Z ⟶ W) (k : W ⟶ V),
    Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
      (integralComparisonDerivedSequenceScalar l E L ι Z) ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
          (integralComparisonSystemScalarPullback l E L ι h).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι k).hom
          (integralComparisonDerivedSequencePullback l L h) =
      (integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι V)
          (integralComparisonSystemComposition l L h k).hom
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  derived_scalar_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    (integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarUnit l E Y).hom
          (integralComparisonDerivedSequencePullback l E f) =
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemScalarUnit l E X).hom
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  derived_scalar_tower : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι f).hom
      (integralComparisonDerivedSequenceScalar l L M j X) ≫
        Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι Y)
          (integralComparisonSystemScalarPullback l L M j f).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarComposition l E L M ι j Y).hom
          (integralComparisonDerivedSequencePullback l M f) =
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
          (integralComparisonSystemScalarComposition l E L M ι j X).hom ≫
        (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  derived_associative : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T V W Z : Scheme.{t}}
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
    (integralComparisonSystemComposition l E (f ≫ g) h).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E h)
          (integralComparisonSystemComposition l E f g).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.assoc f
        g h)) ≫
        (integralComparisonSystemComposition l E f (g ≫ h)).hom ≫
        Functor.whiskerRight (integralComparisonSystemComposition l E g h).hom
          (integralComparisonDerivedSequencePullback l E f)
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  derived_unital : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    ((integralComparisonSystemComposition l E (𝟙 X) f).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
          (integralComparisonSystemUnit l E X).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.id_comp
        f))) ∧
    ((integralComparisonSystemComposition l E f (𝟙 Y)).hom ≫
        Functor.whiskerRight (integralComparisonSystemUnit l E Y).hom
          (integralComparisonDerivedSequencePullback l E f) =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.comp_id
        f)))
  /-- All parenthesizations of every finite string give the same comparison. -/
  derived_finite : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
    (a b : IntegralQuotientBracketing p),
    ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E) a =
      integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E) b,
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E)
          (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
          a ≪≫ eqToIso h =
      integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E)
          (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
          b

/-- Mixed geometric/scalar coherence of the canonical operations on strict quotient systems.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and the node's eight proof steps
(blueprint: lem-trf-quotient-system-mixed-coherence).

Proof: (1) Work on the ringed sequence site, not in towers in a derived category.
The adjunction determines inverse-image maps on unit sections; the tensor adjunction
then determines scalar-linear maps on unit tensors. (2) The two three-arrow compositors
send a unit to the same successive units. Identity units insert the identity map.
Induction on a binary assembly proves finite-string coherence, including the empty
and singleton paths. Transport along an equality of scheme arrows uses that same mate.
(3) In the mixed square both routes send 1 tensor gamma_hk(x) to
 gamma_h gamma_k(1 tensor x). (4) For the scalar unit both routes send
1 tensor gamma_f(x) to gamma_f(x), and scalar linearity handles general coefficients.
(5) In a coefficient tower both routes send c tensor (b tensor gamma_f(x)) to
 gamma_f(c*j(b) tensor x). This includes identity and equal coefficient extensions.
(6) Unit naturality and tensor functoriality commute with every vertical restriction
and horizontal quotient transition; quotient ring homomorphisms preserve products.
The resulting equalities are equalities of module-system transformations, so applying
mapHomologicalComplex gives equal cochain maps in all degrees, commuting with the
differential and without signs. (7) Choose one flat-term K-flat resolution of the
entire system, using lem-pc-kflat-resolution. Ringed-topos pullback preserves K-flat
complexes with flat terms (lem-weil-pbc-ringed-topos-kflat-pullback), as does scalar
extension, including for nonflat coefficient maps. Iterate this for the finite diagram.
The universal cochain counits of lem-pur-derived-change-of-rings identify the specified
derived maps with the localized ordinary maps on this simultaneous model.
(8) Localization preserves the equalities. Naturality and cancellation of the
resolution isomorphism prove them on every input. No normalization, boundedness,
finite Tor-amplitude or flatness of a quotient coefficient map was used. -/
theorem integralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] :
    IntegralQuotientMixedCoherence.{t, u} l := by
  sorry

end WeilConjectures
