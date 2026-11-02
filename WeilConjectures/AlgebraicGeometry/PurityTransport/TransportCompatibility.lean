/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.SmoothDatum.TransportGeometricOperations
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-counit-equations). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Base change of the same counit through the canonical proper/open exchange.
The normalized open comparison has inverse the recorded open base-change arrow.
Source: smooth-purity base change (blueprint: def-pur-transport-counit-equations). -/
def BaseChangeCompatible (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D)
    (Y' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of D.k))],
    ∃ p : LinePullCoordinates ell c (pullback.fst s.map v),
    ∃ o :
      (actualOpen (c.obj ell) s.compactification.i) ⋙
        (actualPull (c.obj ell)
          (pullback.fst s.compactification.g v)) ≅
      (actualPull (c.obj ell) (pullback.fst s.map v)) ⋙
        (actualOpen (c.obj ell)
          (s.compactification.baseChange v).i),
    o.inv =
      ((fun (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          [MonObj R] [IsCommMonObj R] ↦
       let cf := s.compactification
       let h := pullback.fst s.map v
       let k := pullback.fst cf.g v
       let L := (actualOpen R cf.i)
       let L' :=
         (actualOpen R (cf.baseChange v).i)
       let U := (actualPull R h)
       let V := (actualPull R k)
       let sq := cf.isPullback_i_ofIsPullback (IsPullback.of_hasPullback s.map v)
       let theta := CondensedRing.condensedAmbientPullbackComparison R
         { toCommSq := sq.toCommSq
           isoPullback := sq.isoPullback
           hom_fst := sq.isoPullback_hom_fst
           hom_snd := sq.isoPullback_hom_snd }
       (Functor.leftUnitor _).inv ≫
         Functor.whiskerRight
           (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R cf.i).unit
           (U ⋙ L') ≫
         (Functor.squareTransport L L'
           (Functor.isoWhiskerRight
               (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R cf.i).symm U ≪≫
             theta.symm ≪≫
             Functor.isoWhiskerLeft V
               (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R
                 (cf.baseChange v).i))).hom ≫
         Functor.whiskerLeft (L ⋙ V)
           (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R
             (cf.baseChange v).i).counit ≫
         (Functor.rightUnitor _).hom) (c.obj ell)) ∧
    ∀ K : c.ctf ell s.Y.left,
      ∃ hK : property ell c Y'.left
        ((actualPull (c.obj ell) v).obj K.obj),
      (actualPull (c.obj ell) v).map ((a c s).trace K) =
        (CondensedRing.condensedAmbientExchange (c.obj ell)
          { toCommSq := ⟨pullback.condition⟩
            isoPullback := Iso.refl _
            hom_fst := Category.id_comp _
            hom_snd := Category.id_comp _ }).app
              ((CondensedRing.openImmersionLowerShriek
                (c.obj ell) s.compactification.i).mapDerivedCategory.obj
                  ((c.smoothSource ell s.map s.dim).obj K.obj)) ≫
          (actualPush (c.obj ell)
            (pullback.snd s.compactification.g v)).map
              (o.hom.app ((c.smoothSource ell s.map s.dim).obj K.obj)) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) (s.compactification.baseChange v)).map
              (sourceBaseChange ell c s.map v s.dim p K.obj).hom ≫
          (a c (s.baseChange Y' v)).trace ⟨_, hK⟩

/-- Composition of the same smooth counits, on the specified proper/open model.
The interchange is fixed by its restriction equation. Quantifying over every such
interchange expresses the canonical compositor without selecting an unrelated map.
Source: smooth trace composition (blueprint: def-pur-transport-counit-equations). -/
def CompositionCompatible (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (a : AdjunctionFamily ell D) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D)
    (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)),
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa using (primeUnit D ell hEll).map
          ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let t : SmoothDatum D :=
      { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
    ∃ p : LinePullCoordinates ell c s.map,
    ∀ (K : c.ctf ell Z.left)
      (m : (actualOpen (c.obj ell) cg.i).obj
        ((actualPush (c.obj ell) s.compactification.g).obj
          ((CondensedRing.openImmersionLowerShriek
            (c.obj ell) s.compactification.i).mapDerivedCategory.obj
            ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj))) ⟶
        (actualPush (c.obj ell) cr.obj.obj.g).obj
          ((actualOpen (c.obj ell) cr.obj.obj.i).obj
            ((CondensedRing.openImmersionLowerShriek
            (c.obj ell) s.compactification.i).mapDerivedCategory.obj
              ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj))))
      (_hm :
        let R := c.obj ell
        letI : MonObj R := inferInstance
        letI : IsCommMonObj R := inferInstance
        let q := s.compactification.g
        let i := cg.i
        let j := cr.obj.obj.i
        let r := cr.obj.obj.g
        let A := (CondensedRing.openImmersionLowerShriek R s.compactification.i)
          |>.mapDerivedCategory.obj ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj)
        let B := (actualOpen R j).obj A
        let theta :=
          (Functor.mapDerivedCategoryCompIso
            (CondensedRing.upperStar R i) (CondensedRing.upperStar R q)).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            ((CondensedRing.upperStarComp R q i).symm ≪≫
              eqToIso (congrArg (CondensedRing.upperStar R) cr.obj.obj.comm) ≪≫
              CondensedRing.upperStarComp R j r) ≪≫
          Functor.mapDerivedCategoryCompIso
            (CondensedRing.upperStar R r) (CondensedRing.upperStar R j)
        let rho :=
          ((CondensedRing.derivedUpperStarLowerStarAdjunction R q).ofNatIsoLeft
            (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R q)).homEquiv _ _
              (theta.hom.app ((actualPush R r).obj B) ≫
                (CondensedRing.upperStar R j).mapDerivedCategory.map
                  (((CondensedRing.derivedUpperStarLowerStarAdjunction R r).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R r)).counit.app B))
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R i).homEquiv
            _ _ m ≫ rho =
          (actualPush R q).map
            ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R j).unit.app A)),
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).map
              (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          ((a c s).trace
            ⟨(c.smoothSource ell g e).obj K.obj, (a c t).source_closed K.obj K.property⟩) ≫
        (a c t).trace K =
      supportComp (c.obj ell)
          s.compactification cg cr _ m ≫
        (a c (s.comp Z g e cg cr)).trace K

end AlgebraicGeometry.ProEtale.PurityTransport
