/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstruction
import WeilConjectures.SixFunctors.NormalizedRingCompactScalar.NormalizedRingCompactScalarCocycle
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedRationalLeftLaws
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedRingRefinementLaws
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedCommonCoefficientLaws
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms

/-! # Coherence of normalized exceptional coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local irreducible] ScalarLocalization.category
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientRingCoherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) : Prop where
  cocycle (c : Compactification f) {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle.{u, v} l Ω ((R.comparison c a ha).complete l Ω)
      ((R.comparison c b hb).complete l Ω) ((R.comparison c d hd).complete l Ω)
      (R.scalarComposition a b d h ha hb hd true).iso
      (R.scalarComposition a b d h ha hb hd false).iso
  identityLeft (c : Compactification f) {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u, v} l Ω X (s.stage l)) :
    (R.comparison c a ha).q.hom.app K ≫
        (R.operation c (s.stage l)).F.map ((R.scalarIdentity a h ha true).iso.hom.app K) =
      (R.scalarIdentity a h ha false).iso.hom.app ((R.operation c (s.stage l)).F.obj K)
  identityRight (c : Compactification f) {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C.{u, v} l Ω Y (s.stage l)) :
    (R.comparison c a ha).b.hom.app L ≫
        (R.operation c (s.stage l)).G.map ((R.scalarIdentity a h ha false).iso.hom.app L) =
      (R.scalarIdentity a h ha true).iso.hom.app ((R.operation c (s.stage l)).G.obj L)

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientFieldCoherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) : Prop where
  rationalCocycle (c : Compactification f) (E L M : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier) :
    FieldCocycle.{u, v} l Ω ((F.rationalComparison c E L i).complete l Ω)
      ((F.rationalComparison c L M j).complete l Ω)
      ((F.rationalComparison c E M (j.comp i)).complete l Ω)
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
  rationalIdentityLeft (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.rational E)) :
    (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K)
  rationalIdentityRight (c : Compactification f) (E : FieldStage.{max u v} l)
      (L : C.{u, v} l Ω Y (.rational E)) :
    (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).b.hom.app L ≫
        (R.operation c (.rational E)).G.map
          ((sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app L) =
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).G.obj L)

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientCommonCoherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) : Prop where
  commonCocycleLeft (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq
      ((commonInclusion.{u, v} l Ω Y j).map
          ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app
              K) ≫
        (M.commonComparison c j).q.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X i j h).obj K))
      ((commonTransition.{u, v} l Ω Y i j h).hom.app
            ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
        (M.commonComparison c i).q.hom.app K ≫
        (R.operation c .closed).F.map
          ((commonTransition.{u, v} l Ω X i j h).inv.app K))
  commonCocycleRight (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω i))) :
    HEq
      ((commonInclusion.{u, v} l Ω X j).map
          ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b.hom.app
              L) ≫
        (M.commonComparison c j).b.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y i j h).obj L))
      ((commonTransition.{u, v} l Ω X i j h).hom.app
            ((R.operation c (.rational (commonField.{u, v} l Ω i))).G.obj L) ≫
        (M.commonComparison c i).b.hom.app L ≫
        (R.operation c .closed).G.map
          ((commonTransition.{u, v} l Ω Y i j h).inv.app L))

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientRefinementCoherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M) : Prop where
  refinementIdentity (c : Compactification f) (s : Stage.{max u v} l) :
    (N.refinement (Compactification.Refinement.id c) s).left = Iso.refl _
  refinementComposition {a b c : Compactification f}
      (r : a.Refinement b) (t : b.Refinement c) (s : Stage.{max u v} l) :
    (N.refinement (r.comp t) s).left = (N.refinement r s).left ≪≫ (N.refinement t s).left

/-- The laws for the same normalized construction, without changing its maps.
Source: blueprint coefficient and refinement coherence
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientCoherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : CoefficientConstruction.{u, v} l Ω D hl (f := f)) : Prop where
  ring : CoefficientRingCoherence.{u, v} l Ω D hl P.ring
  fields : CoefficientFieldCoherence.{u, v} l Ω D hl P.ring P.fields
  common : CoefficientCommonCoherence.{u, v} l Ω D hl P.ring P.fields P.common
  refinements :
    CoefficientRefinementCoherence.{u, v} l Ω D hl P.ring P.fields P.common P.refinements

private theorem right_identity_of_left
    {X Y : Scheme.{max u v}} {s : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X s)
    (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y s)
    [TX.CommShift ℤ] [TY.CommShift ℤ]
    (a : CounitComparison.{u, v} l Ω A A TX TY)
    (uX : TX ≅ 𝟭 _) (uY : TY ≅ 𝟭 _)
    (hleft : ∀ K, a.q.hom.app K ≫ A.F.map (uX.hom.app K) =
      uY.hom.app (A.F.obj K)) (L : C.{u, v} l Ω Y s) :
    a.b.hom.app L ≫ A.G.map (uY.hom.app L) = uX.hom.app (A.G.obj L) := by
  apply (A.adjunction.homEquiv _ _).symm.injective
  change A.F.map _ ≫ A.adjunction.counit.app _ =
    A.F.map _ ≫ A.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [A.adjunction.counit_naturality]
  apply (cancel_epi (a.q.hom.app (A.G.obj L))).1
  calc
    _ = TY.map (A.adjunction.counit.app L) ≫ uY.hom.app L := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ uY.hom.app L) (a.counit L)
    _ = uY.hom.app (A.F.obj (A.G.obj L)) ≫ A.adjunction.counit.app L :=
      uY.hom.naturality _
    _ = _ := by
      rw [← hleft, Category.assoc]
      rfl

private theorem field_identity_of_left
    {X Y : Scheme.{max u v}} {s : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X s)
    (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y s)
    (a : CounitFieldComparison.{u, v} l Ω A A TX TY)
    (uX : TX ≅ 𝟭 _) (uY : TY ≅ 𝟭 _)
    (hleft : ∀ K, a.q.hom.app K ≫ A.F.map (uX.hom.app K) =
      uY.hom.app (A.F.obj K)) (L : C.{u, v} l Ω Y s) :
    a.b.hom.app L ≫ A.G.map (uY.hom.app L) = uX.hom.app (A.G.obj L) := by
  let := a.shiftX
  let := a.shiftY
  exact right_identity_of_left l Ω A TX TY a.comparison uX uY hleft L

private def normalizedScalar {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (T : Scheme.{max u v}) (S : Scalar.{u, v} l Ω a T) :
    NormalizedRingCompactScalar.Scalar.{u, v} l Ω a T :=
  ⟨S.functor, S.realization⟩

private def normalizedAssociator {s t r : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l)}
    {d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T)
    (B : Scalar.{u, v} l Ω b T) (D : Scalar.{u, v} l Ω d T)
    (α : ScalarComposition.{u, v} l Ω h T A B D) :
    NormalizedRingCompactScalar.Associator.{u, v} l Ω h T
      (normalizedScalar l Ω a T A) (normalizedScalar l Ω b T B)
      (normalizedScalar l Ω d T D) :=
  ⟨α.iso, α.normalized⟩

private def normalizedUnit {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T)
    (e : ScalarIdentity.{u, v} l Ω h T A) :
    NormalizedRingCompactScalar.Unit.{u, v} l Ω h T (normalizedScalar l Ω a T A) :=
  ⟨e.iso, e.normalized⟩

private theorem right_cocycle_of_counit
    {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s}
    {B : Operation.{u, v} l Ω X Y t} {D : Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    [TX.CommShift ℤ] [TY.CommShift ℤ] [UX.CommShift ℤ] [UY.CommShift ℤ]
    [VX.CommShift ℤ] [VY.CommShift ℤ]
    (a : CounitComparison.{u, v} l Ω A B TX TY) (b : CounitComparison.{u, v} l Ω B D UX UY)
    (d : CounitComparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY)
    (hleft : ∀ K, UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫
      D.F.map (αX.hom.app K) = αY.hom.app (A.F.obj K) ≫ d.q.hom.app K)
    (L : C.{u, v} l Ω Y s) :
    UX.map (a.b.hom.app L) ≫ b.b.hom.app (TY.obj L) ≫ D.G.map (αY.hom.app L) =
      αX.hom.app (A.G.obj L) ≫ d.b.hom.app L := by
  apply (D.adjunction.homEquiv _ _).symm.injective
  change D.F.map _ ≫ D.adjunction.counit.app _ =
    D.F.map _ ≫ D.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [D.adjunction.counit_naturality]
  let e := UY.mapIso (a.q.app (A.G.obj L)) ≪≫ b.q.app (TX.obj (A.G.obj L))
  have : Epi e.hom := inferInstance
  apply (cancel_epi e.hom).1
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  have hn := b.q.hom.naturality (a.b.hom.app L)
  dsimp only [Functor.comp_map] at hn
  have hα := αY.hom.naturality (A.adjunction.counit.app L)
  dsimp only [Functor.comp_map] at hα
  calc
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        b.q.hom.app (B.G.obj (TY.obj L)) ≫
        D.F.map (b.b.hom.app (TY.obj L)) ≫
        D.adjunction.counit.app (UY.obj (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% hn]
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        UY.map (B.adjunction.counit.app (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% (b.counit (TY.obj L))]
    _ = UY.map (TY.map (A.adjunction.counit.app L)) ≫ αY.hom.app L := by
      rw [← UY.map_comp_assoc, ← UY.map_comp_assoc, Category.assoc, a.counit]
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫
        VY.map (A.adjunction.counit.app L) := hα
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫ d.q.hom.app (A.G.obj L) ≫
        D.F.map (d.b.hom.app L) ≫ D.adjunction.counit.app (VY.obj L) := by
      rw [d.counit L]
    _ = _ := by rw [← reassoc_of% (hleft (A.G.obj L))]

private theorem field_cocycle_of_left
    {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s}
    {B : Operation.{u, v} l Ω X Y t} {D : Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    (a : CounitFieldComparison.{u, v} l Ω A B TX TY)
    (b : CounitFieldComparison.{u, v} l Ω B D UX UY)
    (d : CounitFieldComparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY)
    (hleft : ∀ K, UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫
      D.F.map (αX.hom.app K) = αY.hom.app (A.F.obj K) ≫ d.q.hom.app K) :
    FieldCocycle.{u, v} l Ω (a.complete l Ω) (b.complete l Ω) (d.complete l Ω) αX αY := by
  let := a.shiftX
  let := a.shiftY
  let := b.shiftX
  let := b.shiftY
  let := d.shiftX
  let := d.shiftY
  refine { left := hleft, right := ?_ }
  intro L
  exact right_cocycle_of_counit.{u, v} l Ω
    (s := s) (t := t) (r := r) (A := A) (B := B) (D := D)
    (TX := TX) (TY := TY) (UX := UX) (UY := UY) (VX := VX) (VY := VY)
    a.comparison b.comparison d.comparison αX αY hleft L

private theorem ring_coherence
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) :
    CoefficientRingCoherence.{u, v} l Ω D hl R := by
  let sup (c : Compactification f) (s : RingStage.{max u v} l) :
      NormalizedRingCompactScalar.Support l Ω c s :=
    ⟨(R.operation c (s.stage l)).F, R.left c s⟩
  let sc {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) :
      NormalizedRingCompactScalar.Scalar l Ω a (endpoint X Y side) :=
    normalizedScalar l Ω a (endpoint X Y side) (R.scalar a ha side)
  have left (c : Compactification f) {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d)
      (K : C.{u, v} l Ω X (s.stage l)) :
      (R.scalar b hb false).functor.map ((R.comparison c a ha).q.hom.app K) ≫
        (R.comparison c b hb).q.hom.app ((R.scalar a ha true).functor.obj K) ≫
        (R.operation c (r.stage l)).F.map
          ((R.scalarComposition a b d h ha hb hd true).iso.hom.app K) =
      (R.scalarComposition a b d h ha hb hd false).iso.hom.app
        ((R.operation c (s.stage l)).F.obj K) ≫ (R.comparison c d hd).q.hom.app K := by
    exact (NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle l Ω c D hl).composition
      a b d h (sup c s) (sup c t) (sup c r)
      (sc a ha true) (sc a ha false) (sc b hb true) (sc b hb false)
      (sc d hd true) (sc d hd false)
      (R.comparison c a ha).q (R.comparison c b hb).q (R.comparison c d hd).q
      (R.comparison_normalized c a ha) (R.comparison_normalized c b hb)
      (R.comparison_normalized c d hd)
      (normalizedAssociator l Ω h X _ _ _ (R.scalarComposition a b d h ha hb hd true))
      (normalizedAssociator l Ω h Y _ _ _ (R.scalarComposition a b d h ha hb hd false)) K
  have unit (c : Compactification f) {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u, v} l Ω X (s.stage l)) :
      (R.comparison c a ha).q.hom.app K ≫
        (R.operation c (s.stage l)).F.map ((R.scalarIdentity a h ha true).iso.hom.app K) =
      (R.scalarIdentity a h ha false).iso.hom.app ((R.operation c (s.stage l)).F.obj K) := by
    exact (NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle l Ω c D hl).identity
      a h (sup c s) (sc a ha true) (sc a ha false) (R.comparison c a ha).q
      (R.comparison_normalized c a ha)
      (normalizedUnit l Ω h X _ (R.scalarIdentity a h ha true))
      (normalizedUnit l Ω h Y _ (R.scalarIdentity a h ha false)) K
  refine ⟨?_, unit, ?_⟩
  · intro c s t r a b d h ha hb hd
    refine { left := ?_, right := ?_ }
    · intro K
      exact left c a b d h ha hb hd K
    · intro L
      change (R.scalar b hb true).functor.map ((R.comparison c a ha).b.hom.app L) ≫
          (R.comparison c b hb).b.hom.app ((R.scalar a ha false).functor.obj L) ≫
          (R.operation c (r.stage l)).G.map
            ((R.scalarComposition a b d h ha hb hd false).iso.hom.app L) =
        (R.scalarComposition a b d h ha hb hd true).iso.hom.app
          ((R.operation c (s.stage l)).G.obj L) ≫ (R.comparison c d hd).b.hom.app L
      exact right_cocycle_of_counit.{u, v} l Ω
        (s := s.stage l) (t := t.stage l) (r := r.stage l)
        (A := R.operation c (s.stage l)) (B := R.operation c (t.stage l))
        (D := R.operation c (r.stage l))
        (TX := (R.scalar a ha true).functor) (TY := (R.scalar a ha false).functor)
        (UX := (R.scalar b hb true).functor) (UY := (R.scalar b hb false).functor)
        (VX := (R.scalar d hd true).functor) (VY := (R.scalar d hd false).functor)
        (R.comparison c a ha) (R.comparison c b hb) (R.comparison c d hd)
        (R.scalarComposition a b d h ha hb hd true).iso
        (R.scalarComposition a b d h ha hb hd false).iso (left c a b d h ha hb hd) L
  · intro c s a h ha L
    exact right_identity_of_left l Ω (R.operation c (s.stage l))
      (R.scalar a ha true).functor (R.scalar a ha false).functor
      (R.comparison c a ha) (R.scalarIdentity a h ha true).iso
      (R.scalarIdentity a h ha false).iso (unit c a h ha) L

private theorem rationalization_surjective
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
    (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω T (.rational E)) :
    ∃ L : C.{u, v} l Ω T (.integral E), (rationalization.{u, v} l Ω E T).obj L = K := by
  let : ∀ x : T, Invertible (l : T.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) T
  have h := (integral_residue_tor D l hl E.carrier T).2
  let L : C.{u, v} l Ω T (.integral E) := ⟨K.obj.obj, h ▸ K.obj.property⟩
  exact ⟨L, rfl⟩

private theorem identity_heq {C : Type*} [Category C] {A B : C} (h : A = B) :
    HEq (𝟙 A) (𝟙 B) := by cases h; rfl

private theorem refinement_of_ring
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (hid : ∀ c (s : RingStage.{max u v} l),
      (N.refinement (.id c) (s.stage l)).left = Iso.refl _)
    (hcomp : ∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c)
      (s : RingStage.{max u v} l),
      (N.refinement (r.comp t) (s.stage l)).left =
        (N.refinement r (s.stage l)).left ≪≫ (N.refinement t (s.stage l)).left) :
    CoefficientRefinementCoherence.{u, v} l Ω D hl R F M N := by
  have ratid (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.rational E)) :
      (N.refinement (.id c) (.rational E)).left.hom.app K = 𝟙 _ := by
    obtain ⟨L, rfl⟩ := rationalization_surjective l Ω D hl X E K
    have hn := N.refinementRational (.id c) E L
    rw [hid c (.integral E)] at hn
    simp only [Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id] at hn
    exact eq_of_heq (hn.trans (identity_heq ((F.rationalAction c E).1 L).symm))
  have ratcomp {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.rational E)) :
      (N.refinement (r.comp t) (.rational E)).left.hom.app K =
        (N.refinement r (.rational E)).left.hom.app K ≫
          (N.refinement t (.rational E)).left.hom.app K := by
    obtain ⟨L, rfl⟩ := rationalization_surjective l Ω D hl X E K
    have hn := N.refinementRational (r.comp t) E L
    rw [hcomp r t (.integral E)] at hn
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] at hn
    exact eq_of_heq (hn.trans
      (CategoryTheory.heq_comp ((F.rationalAction a E).1 L).symm
        ((F.rationalAction b E).1 L).symm ((F.rationalAction c E).1 L).symm
        (N.refinementRational r E L).symm (N.refinementRational t E L).symm))
  refine ⟨?_, ?_⟩
  · intro c s
    apply Iso.ext
    apply NatTrans.ext
    funext K
    cases s with
    | finite E n => exact congrArg (fun e ↦ e.hom.app K) (hid c (.finite E n))
    | integral E => exact congrArg (fun e ↦ e.hom.app K) (hid c (.integral E))
    | rational E => exact ratid c E K
    | closed =>
      rcases K with ⟨i, K⟩
      change (N.refinement (.id c) .closed).left.hom.app
        ((commonInclusion l Ω X i).obj K) = 𝟙 _
      erw [← N.refinementCommon (.id c) i K, ratid]
      erw [(commonInclusion l Ω Y i).map_id]
      calc
        _ = (M.commonComparison c i).q.inv.app K ≫
            (M.commonComparison c i).q.hom.app K :=
          congrArg (fun h ↦ (M.commonComparison c i).q.inv.app K ≫ h)
            (Category.id_comp ((M.commonComparison c i).q.hom.app K))
        _ = _ := (M.commonComparison c i).q.inv_hom_id_app K
  · intro a b c r t s
    apply Iso.ext
    apply NatTrans.ext
    funext K
    cases s with
    | finite E n => exact congrArg (fun e ↦ e.hom.app K) (hcomp r t (.finite E n))
    | integral E => exact congrArg (fun e ↦ e.hom.app K) (hcomp r t (.integral E))
    | rational E => exact ratcomp r t E K
    | closed =>
      rcases K with ⟨i, K⟩
      change (N.refinement (r.comp t) .closed).left.hom.app
        ((commonInclusion l Ω X i).obj K) =
          (N.refinement r .closed).left.hom.app ((commonInclusion l Ω X i).obj K) ≫
          (N.refinement t .closed).left.hom.app ((commonInclusion l Ω X i).obj K)
      erw [← N.refinementCommon (r.comp t) i K,
        ← N.refinementCommon r i K, ← N.refinementCommon t i K, ratcomp]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc ((M.commonComparison b i).q.hom.app K),
        (M.commonComparison b i).q.hom_inv_id_app K, Category.id_comp]

/-- The normalized scalar mates and proper/open refinement maps obey their cocycles.
Source: the coefficient identity/composition and compactification-refinement clauses of
current blueprint exceptional inverse image; mate pasting and uniqueness of adjoints
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence).

Proof: Apply the faithful full inclusions at ring stages. Conjugate q by the recorded
left and scalar realizations. The normalization equation identifies it with the actual
proper/open coefficient mate. The scalar composition normalization identifies the
associator with the derived tensor associator. Pasting the proper/open restriction
squares, and transposing under extension/restriction adjunction, proves the q composition
law. The identity square gives q's identity law, with multiplication as tensor unit.
The counit equation uniquely determines b under the target adjunction. Transpose both
sides of the proposed b composition law: naturality and the q composition law reduce
them to the same composite of the source counit with the inverse coefficient mate.
The same argument for the identity square proves b's identity law. Thus no identity
or composition law for b is presumed.

Rationalization sends these equations to their localized equations. Every rational
object is represented by an integral object (and the integral residue-Tor theorem
puts that representative in the required finite-Tor category), so the normalized
rational maps have the displayed identity and composition laws. For closed coefficients
represent all finitely many objects and arrows at a common finite coefficient field;
the common inclusion normalization and transition isomorphisms identify the two
composites there. Equality in the filtered colimit gives both common-stage cocycles,
with the stated heterogeneous identifications.

Finally, the ring-stage refinement normalization determines its left map: the open
adjunction unit determines the open comparison, and the proper counit and composition
isomorphism determine its pushforward. The compactification coherence theorem gives
identity and transitivity for those actual proper/open maps. Faithfulness of the full
inclusions gives refinementIdentity and refinementComposition. Their rational images
and common-stage maps obey the same laws by refinementRational and refinementCommon.
Empty schemes, identity coefficient maps, nonflat finite quotients and ramified en
transitions are covered by these same normalization and mate calculations. -/
theorem coefficient_construction_coherence (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : CoefficientConstruction.{u, v} l Ω D hl (f := f)) :
    CoefficientCoherence.{u, v} l Ω D hl P := by
  obtain ⟨hcomp, hid⟩ := normalized_rational_left_laws l Ω D hl P.ring P.fields
  obtain ⟨hcommonLeft, hcommonRight⟩ :=
    normalized_common_coefficient_laws l Ω D hl P.ring P.fields P.common
  obtain ⟨hrefId, hrefComp⟩ :=
    normalized_ring_refinement_laws l Ω D hl P.ring P.fields P.common P.refinements
  refine ⟨ring_coherence l Ω D hl P.ring, ?_,
    ⟨hcommonLeft, hcommonRight⟩,
    refinement_of_ring l Ω D hl P.ring P.fields P.common P.refinements hrefId hrefComp⟩
  refine ⟨?_, hid, ?_⟩
  · intro c E L M i j
    exact field_cocycle_of_left.{u, v} l Ω
      (s := .rational E) (t := .rational L) (r := .rational M)
      (A := P.ring.operation c (.rational E))
      (B := P.ring.operation c (.rational L))
      (D := P.ring.operation c (.rational M))
      (TX := rationalScalar.{u, v} l Ω E L i X) (TY := rationalScalar.{u, v} l Ω E L i Y)
      (UX := rationalScalar.{u, v} l Ω L M j X) (UY := rationalScalar.{u, v} l Ω L M j Y)
      (VX := rationalScalar.{u, v} l Ω E M (j.comp i) X)
      (VY := rationalScalar.{u, v} l Ω E M (j.comp i) Y)
      (P.fields.rationalComparison c E L i) (P.fields.rationalComparison c L M j)
      (P.fields.rationalComparison c E M (j.comp i))
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j) (hcomp c E L M i j)
  · intro c E L
    exact field_identity_of_left.{u, v} l Ω (P.ring.operation c (.rational E))
      (rationalScalar.{u, v} l Ω E E (AlgHom.id (Padic l) E.carrier) X)
      (rationalScalar.{u, v} l Ω E E (AlgHom.id (Padic l) E.carrier) Y)
      (P.fields.rationalComparison c E E (AlgHom.id (Padic l) E.carrier))
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero)
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero) (hid c E) L

end ConstructibleExceptionalCoefficients
end WeilConjectures
