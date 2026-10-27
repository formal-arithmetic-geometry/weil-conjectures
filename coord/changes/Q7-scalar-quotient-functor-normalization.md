# AlgebraicGeometry.ProEtale.ScalarQuotientChain functor abbreviations

## Reason

Normalize scalar extension and composites of termwise functors to the termwise lift of
their module-level composition. These are definitionally equal presentations of the
same object and map fields. Explicit result types state the previously inferred types.
Every use of scalarRestrict explicitly selects its already inferred module universe
`max r (t + 1)`, avoiding repeated universe inference. Its abbreviation is unchanged.
Tower, Transport, TransitionFormulas and the final theorem spell successor indices as
`Nat.succ n` instead of `n + 1`, definitionally the same number. This avoids expensive
index normalization in the module-functor types. The final theorem has the same
hypotheses and conclusion up to definitional equality; no target statement changes.
All actions, sections and maps retain their types and values up to definitional equality.
The source-library tree is untouched.

## Old

```lean
abbrev scalarExtend (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :=
  CochainPullback.extend.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a

structure Tower (W : Scheme.{t}) where
  R : Coeff.{t, r} W
  S : Coeff.{t, r} W
  A : ℕ → Coeff.{t, r} W
  B : ℕ → Coeff.{t, r} W
  j : R ⟶ S
  i : ∀ n : ℕ, A n ⟶ B n
  piA : ∀ n : ℕ, R ⟶ A n
  piB : ∀ n : ℕ, S ⟶ B n
  qA : ∀ n : ℕ, A (n + 1) ⟶ A n
  qB : ∀ n : ℕ, B (n + 1) ⟶ B n
  transition_i : ∀ n : ℕ, i (n + 1) ≫ qB n = qA n ≫ i n
  projection_A : ∀ n : ℕ, piA (n + 1) ≫ qA n = piA n
  projection_B : ∀ n : ℕ, piB (n + 1) ≫ qB n = piB n
  projection_i : ∀ n : ℕ, j ≫ piB n = piA n ≫ i n

structure Transport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (DX : Tower.{t, r} X) (DY : Tower.{t, r} Y) where
  cR : (inverseRing g).obj DY.R ≅ DX.R
  cS : (inverseRing g).obj DY.S ≅ DX.S
  cA : ∀ n : ℕ, (inverseRing g).obj (DY.A n) ≅ DX.A n
  cB : ∀ n : ℕ, (inverseRing g).obj (DY.B n) ≅ DX.B n
  j_comm : (inverseRing g).map DY.j ≫ cS.hom = cR.hom ≫ DX.j
  i_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.i n) ≫ (cB n).hom = (cA n).hom ≫ DX.i n
  piA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piA n) ≫ (cA n).hom = cR.hom ≫ DX.piA n
  piB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piB n) ≫ (cB n).hom = cS.hom ≫ DX.piB n
  qA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qA n) ≫ (cA n).hom = (cA (n + 1)).hom ≫ DX.qA n
  qB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qB n) ≫ (cB n).hom = (cB (n + 1)).hom ≫ DX.qB n

abbrev inverseModules {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) :=
  isoSectionwiseModuleInverseImage.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

abbrev inverseComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) :=
  (inverseModules g c).mapHomologicalComplex (.up ℤ)

abbrev left := inverseComplex g d.cR ⋙ scalarExtend X DX.j

abbrev right := scalarExtend Y DY.j ⋙ inverseComplex g d.cS

abbrev finiteLeft (n : ℕ) :=
  scalarExtend Y (DY.piA n) ⋙ inverseComplex g (d.cA n) ⋙ scalarExtend X (DX.i n)

abbrev finiteRight (n : ℕ) :=
  scalarExtend Y (DY.j ≫ DY.piB n) ⋙ inverseComplex g (d.cB n)

abbrev restrictedLeft (n : ℕ) := finiteLeft g d n ⋙ scalarRestrict X (DX.piB n)

abbrev restrictedRight (n : ℕ) := finiteRight g d n ⋙ scalarRestrict X (DX.piB n)

def TransitionFormulas
    (v : ∀ n : ℕ, restrictedLeft g d (n + 1) ⟶ restrictedLeft g d n)
    (w : ∀ n : ℕ, restrictedRight g d (n + 1) ⟶ restrictedRight g d n) : Prop :=
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (a : (DY.A (n + 1)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B (n + 1)).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((v n).app P).f k).val.app (op U) (doublePure g d (n + 1) P k U a s p) =
      doublePure g d n P k U
        ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
        ((DX.qB n).hom.app (op U) s) p) ∧
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B (n + 1)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((w n).app P).f k).val.app (op U) (finitePure g d (n + 1) P k U s p) =
      finitePure g d n P k U
        ((DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p)

theorem scalar_quotient_chain_squares (b : left g d ≅ right g d)
    (hb : UpperFormula g d b) :
    ∃ (bfin : ∀ n : ℕ, finiteLeft g d n ≅ finiteRight g d n)
      (v : ∀ n : ℕ, left g d ⟶ restrictedLeft g d n)
      (w : ∀ n : ℕ, right g d ⟶ restrictedRight g d n)
      (vtrans : ∀ n : ℕ, restrictedLeft g d (n + 1) ⟶ restrictedLeft g d n)
      (wtrans : ∀ n : ℕ, restrictedRight g d (n + 1) ⟶ restrictedRight g d n),
      FiniteFormulas g d bfin ∧ QuotientFormulas g d v w ∧
      TransitionFormulas g d vtrans wtrans ∧
      (∀ n : ℕ,
        v n ≫ Functor.whiskerRight (bfin n).hom (scalarRestrict X (DX.piB n)) =
          b.hom ≫ w n) ∧
      (∀ n : ℕ,
        vtrans n ≫ Functor.whiskerRight (bfin n).hom (scalarRestrict X (DX.piB n)) =
          Functor.whiskerRight (bfin (n + 1)).hom
            (scalarRestrict X (DX.piB (n + 1))) ≫ wtrans n)
```

## New

```lean
abbrev scalarExtend (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :
    moduleComplex W A ⥤ moduleComplex W B :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a).mapHomologicalComplex (.up ℤ)

structure Tower (W : Scheme.{t}) where
  R : Coeff.{t, r} W
  S : Coeff.{t, r} W
  A : ℕ → Coeff.{t, r} W
  B : ℕ → Coeff.{t, r} W
  j : R ⟶ S
  i : ∀ n : ℕ, A n ⟶ B n
  piA : ∀ n : ℕ, R ⟶ A n
  piB : ∀ n : ℕ, S ⟶ B n
  qA : ∀ n : ℕ, A (Nat.succ n) ⟶ A n
  qB : ∀ n : ℕ, B (Nat.succ n) ⟶ B n
  transition_i : ∀ n : ℕ, i (Nat.succ n) ≫ qB n = qA n ≫ i n
  projection_A : ∀ n : ℕ, piA (Nat.succ n) ≫ qA n = piA n
  projection_B : ∀ n : ℕ, piB (Nat.succ n) ≫ qB n = piB n
  projection_i : ∀ n : ℕ, j ≫ piB n = piA n ≫ i n

structure Transport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (DX : Tower.{t, r} X) (DY : Tower.{t, r} Y) where
  cR : (inverseRing g).obj DY.R ≅ DX.R
  cS : (inverseRing g).obj DY.S ≅ DX.S
  cA : ∀ n : ℕ, (inverseRing g).obj (DY.A n) ≅ DX.A n
  cB : ∀ n : ℕ, (inverseRing g).obj (DY.B n) ≅ DX.B n
  j_comm : (inverseRing g).map DY.j ≫ cS.hom = cR.hom ≫ DX.j
  i_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.i n) ≫ (cB n).hom = (cA n).hom ≫ DX.i n
  piA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piA n) ≫ (cA n).hom = cR.hom ≫ DX.piA n
  piB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piB n) ≫ (cB n).hom = cS.hom ≫ DX.piB n
  qA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qA n) ≫ (cA n).hom = (cA (Nat.succ n)).hom ≫ DX.qA n
  qB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qB n) ≫ (cB n).hom = (cB (Nat.succ n)).hom ≫ DX.qB n

abbrev inverseModules {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) :
    ringedSiteModules.{max r (t + 1)} ((forgetRing Y).obj RY) ⥤
      ringedSiteModules.{max r (t + 1)} ((forgetRing X).obj RX) :=
  isoSectionwiseModuleInverseImage.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

abbrev inverseComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) : moduleComplex Y RY ⥤ moduleComplex X RX :=
  (inverseModules g c).mapHomologicalComplex (.up ℤ)

abbrev left : moduleComplex Y DY.R ⥤ moduleComplex X DX.S := (inverseModules g d.cR ⋙
  extensionFunctor.{max r (t + 1), t + 1, t} DX.j).mapHomologicalComplex (.up ℤ)

abbrev right : moduleComplex Y DY.R ⥤ moduleComplex X DX.S :=
  (extensionFunctor.{max r (t + 1), t + 1, t} DY.j ⋙
  inverseModules g d.cS).mapHomologicalComplex (.up ℤ)

abbrev finiteLeft (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n) ⋙
    inverseModules g (d.cA n) ⋙ extensionFunctor.{max r (t + 1), t + 1, t}
      (DX.i n)).mapHomologicalComplex (.up ℤ)

abbrev finiteRight (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
    inverseModules g (d.cB n)).mapHomologicalComplex (.up ℤ)

abbrev restrictedLeft (n : ℕ) :=
  finiteLeft g d n ⋙ scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)

abbrev restrictedRight (n : ℕ) :=
  finiteRight g d n ⋙ scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)

def TransitionFormulas
    (v : ∀ n : ℕ, restrictedLeft g d (Nat.succ n) ⟶ restrictedLeft g d n)
    (w : ∀ n : ℕ, restrictedRight g d (Nat.succ n) ⟶ restrictedRight g d n) : Prop :=
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (a : (DY.A (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B (Nat.succ n)).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((v n).app P).f k).val.app (op U) (doublePure g d (Nat.succ n) P k U a s p) =
      doublePure g d n P k U
        ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
        ((DX.qB n).hom.app (op U) s) p) ∧
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((w n).app P).f k).val.app (op U) (finitePure g d (Nat.succ n) P k U s p) =
      finitePure g d n P k U
        ((DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p)

theorem scalar_quotient_chain_squares (b : left g d ≅ right g d)
    (hb : UpperFormula g d b) :
    ∃ (bfin : ∀ n : ℕ, finiteLeft g d n ≅ finiteRight g d n)
      (v : ∀ n : ℕ, left g d ⟶ restrictedLeft g d n)
      (w : ∀ n : ℕ, right g d ⟶ restrictedRight g d n)
      (vtrans : ∀ n : ℕ, restrictedLeft g d (Nat.succ n) ⟶ restrictedLeft g d n)
      (wtrans : ∀ n : ℕ, restrictedRight g d (Nat.succ n) ⟶ restrictedRight g d n),
      FiniteFormulas g d bfin ∧ QuotientFormulas g d v w ∧
      TransitionFormulas g d vtrans wtrans ∧
      (∀ n : ℕ,
        v n ≫ Functor.whiskerRight (bfin n).hom
          (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
          b.hom ≫ w n) ∧
      (∀ n : ℕ,
        vtrans n ≫ Functor.whiskerRight (bfin n).hom
          (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
          Functor.whiskerRight (bfin (Nat.succ n)).hom
            (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB (Nat.succ n))) ≫ wtrans n)
```

## Users

The read-only downstream.py --uses scan on 2026-10-24 found zero downstream modules.
The item itself is the only textual user of these declarations. Parent DAG dependencies
and the unit route are retained; no node is withdrawn. These normalizations preserve
the meanings of the definitions, so no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismScalarQuotientChainSquares | Q7 | Proof uses the module functors and their termwise lifts. |

## Status

landed 20261024T204644-L-3815491 2026-10-24 (merge of deliver/Q7/Sheaf.Paper.IsomorphismScalarQuotientChainSquares)
