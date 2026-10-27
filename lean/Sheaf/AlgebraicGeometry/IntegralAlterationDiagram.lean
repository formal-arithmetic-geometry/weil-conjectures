module

public import Sheaf.TraceFormula.LocalDimensionFormula
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Integral alteration diagrams and cartesian comparisons

Source: Kurano--Shimomoto, Definition 3.2 and Lemma 4.4, printed pp. 3 and 5
(blueprint: def-per-integral-alteration-diagram).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness of the canonical extension of generic stalks for a dominant morphism.
Source: Kurano--Shimomoto, Definition 3.2, printed p. 3
(blueprint: def-per-integral-alteration-diagram). -/
def Scheme.Hom.HasFiniteGenericFieldExtension {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] : Prop :=
  @Module.Finite Y.functionField X.functionField _ _
    (@Algebra.toModule _ _ _ _ f.dominantFunctionFieldAlgebra)

/-- An indexed integral alteration diagram with its specified proper covering witness.
The index is kept as data and may have empty open members. Finiteness of the index is
imposed by consumers. Source: Kurano--Shimomoto, Definition 3.2, printed p. 3,
restricted to integral witness schemes as in the spreading lemma
(blueprint: def-per-integral-alteration-diagram). -/
structure IntegralAlterationDiagram (I : Type w) (S : Scheme.{u}) where
  /-- The integral base, a property retained when restricting outside the prime. -/
  integral_S : IsIntegral S
  /-- The integral members of the alteration family. -/
  T : I → Scheme.{u}
  integral_T : ∀ i, IsIntegral (T i)
  noetherian_T : ∀ i, IsNoetherian (T i)
  f : ∀ i, T i ⟶ S
  dominant_f : ∀ i, IsDominant (f i)
  finiteType_f : ∀ i, LocallyOfFiniteType (f i) ∧ QuasiCompact (f i)
  finiteGeneric_f : ∀ i, @Scheme.Hom.HasFiniteGenericFieldExtension _ _
    (integral_T i) integral_S (f i) (dominant_f i)
  /-- The specified proper covering witness. -/
  P : Scheme.{u}
  integral_P : IsIntegral P
  noetherian_P : IsNoetherian P
  g : P ⟶ S
  proper_g : IsProper g
  surjective_g : Surjective g
  finiteGeneric_g : @Scheme.Hom.HasFiniteGenericFieldExtension _ _
    integral_P integral_S g ⟨surjective_g.surj.denseRange⟩
  U : I → P.Opens
  covers : iSup U = ⊤
  h : ∀ i, (U i).toScheme ⟶ T i
  commutes : ∀ i, h i ≫ f i = (U i).ι ≫ g

/-- A comparison which identifies the entire source diagram with the base change of the
specified target diagram. The cartesian squares for the cover members retain the indexed
open cover, and the last equality retains each chosen `h`. Source: Kurano--Shimomoto,
Lemma 4.4, first proof paragraph, printed p. 5
(blueprint: def-per-integral-alteration-diagram). -/
def IntegralAlterationDiagram.IsCartesianOver {I : Type w} {S R : Scheme.{u}}
    (D : IntegralAlterationDiagram I S)
    (E : IntegralAlterationDiagram I R) (s : S ⟶ R) : Prop :=
  ∃ (t : ∀ i, D.T i ⟶ E.T i) (p : D.P ⟶ E.P)
    (v : ∀ i, (D.U i).toScheme ⟶ (E.U i).toScheme),
    (∀ i, IsPullback (t i) (D.f i) (E.f i) s) ∧
    IsPullback p D.g E.g s ∧
    (∀ i, IsPullback (v i) (D.U i).ι (E.U i).ι p) ∧
    (∀ i, v i ≫ E.h i = D.h i ≫ t i)

end AlgebraicGeometry
