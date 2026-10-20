/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction

/-! # Coherence of normalized exceptional coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientRingCoherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing l Ω D hl (f := f)) : Prop where
  cocycle (c : Compactification f) {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle l Ω ((R.comparison c a ha).complete l Ω)
      ((R.comparison c b hb).complete l Ω) ((R.comparison c d hd).complete l Ω)
      (R.scalarComposition a b d h ha hb hd true).iso
      (R.scalarComposition a b d h ha hb hd false).iso
  identityLeft (c : Compactification f) {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C l Ω X (s.stage l)) :
    (R.comparison c a ha).q.hom.app K ≫
        (R.operation c (s.stage l)).F.map ((R.scalarIdentity a h ha true).iso.hom.app K) =
      (R.scalarIdentity a h ha false).iso.hom.app ((R.operation c (s.stage l)).F.obj K)
  identityRight (c : Compactification f) {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C l Ω Y (s.stage l)) :
    (R.comparison c a ha).b.hom.app L ≫
        (R.operation c (s.stage l)).G.map ((R.scalarIdentity a h ha false).iso.hom.app L) =
      (R.scalarIdentity a h ha true).iso.hom.app ((R.operation c (s.stage l)).G.obj L)

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientFieldCoherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing l Ω D hl (f := f))
    (F : CoefficientConstructionFields l Ω D hl R) : Prop where
  rationalCocycle (c : Compactification f) (E L M : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier) :
    FieldCocycle l Ω ((F.rationalComparison c E L i).complete l Ω)
      ((F.rationalComparison c L M j).complete l Ω)
      ((F.rationalComparison c E M (j.comp i)).complete l Ω)
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
  rationalIdentityLeft (c : Compactification f) (E : FieldStage.{u} l)
      (K : C l Ω X (.rational E)) :
    (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K)
  rationalIdentityRight (c : Compactification f) (E : FieldStage.{u} l)
      (L : C l Ω Y (.rational E)) :
    (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).b.hom.app L ≫
        (R.operation c (.rational E)).G.map
          ((sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app L) =
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).G.obj L)

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientCommonCoherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing l Ω D hl (f := f))
    (F : CoefficientConstructionFields l Ω D hl R)
    (M : CoefficientConstructionCommon l Ω D hl R F) : Prop where
  commonCocycleLeft (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C l Ω X (.rational (commonField l Ω i))) :
    HEq
      ((commonInclusion l Ω Y j).map
          ((F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app
              K) ≫
        (M.commonComparison c j).q.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X i j h).obj K))
      ((commonTransition l Ω Y i j h).hom.app
            ((R.operation c (.rational (commonField l Ω i))).F.obj K) ≫
        (M.commonComparison c i).q.hom.app K ≫
        (R.operation c .closed).F.map
          ((commonTransition l Ω X i j h).inv.app K))
  commonCocycleRight (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (L : C l Ω Y (.rational (commonField l Ω i))) :
    HEq
      ((commonInclusion l Ω X j).map
          ((F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b.hom.app
              L) ≫
        (M.commonComparison c j).b.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y i j h).obj L))
      ((commonTransition l Ω X i j h).hom.app
            ((R.operation c (.rational (commonField l Ω i))).G.obj L) ≫
        (M.commonComparison c i).b.hom.app L ≫
        (R.operation c .closed).G.map
          ((commonTransition l Ω Y i j h).inv.app L))

/-- Identity and composition laws for the normalized maps at these stages.
Source: blueprint coefficient and compactification cocycle clauses
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientRefinementCoherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing l Ω D hl (f := f))
    (F : CoefficientConstructionFields l Ω D hl R)
    (M : CoefficientConstructionCommon l Ω D hl R F)
    (N : CoefficientConstructionRefinements l Ω D hl R F M) : Prop where
  refinementIdentity (c : Compactification f) (s : Stage.{u} l) :
    (N.refinement (Compactification.Refinement.id c) s).left = Iso.refl _
  refinementComposition {a b c : Compactification f}
      (r : a.Refinement b) (t : b.Refinement c) (s : Stage.{u} l) :
    (N.refinement (r.comp t) s).left = (N.refinement r s).left ≪≫ (N.refinement t s).left

/-- The laws for the same normalized construction, without changing its maps.
Source: blueprint coefficient and refinement coherence
(blueprint: lem-sf-constructible-exceptional-coefficient-coherence). -/
structure CoefficientCoherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : CoefficientConstruction l Ω D hl (f := f)) : Prop where
  ring : CoefficientRingCoherence l Ω D hl P.ring
  fields : CoefficientFieldCoherence l Ω D hl P.ring P.fields
  common : CoefficientCommonCoherence l Ω D hl P.ring P.fields P.common
  refinements : CoefficientRefinementCoherence l Ω D hl P.ring P.fields P.common P.refinements


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
theorem coefficient_construction_coherence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : CoefficientConstruction l Ω D hl (f := f)) :
    CoefficientCoherence l Ω D hl P := by
  sorry

end ConstructibleExceptionalCoefficients
end WeilConjectures
