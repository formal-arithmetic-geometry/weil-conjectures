# WeilConjectures.PurityFiniteSetting.affineDiagonalPresentedTranspose

## Reason

The existing item contains all constructions and the final orientation theorem.
The trace/base-change half and the normalized DNC half both need those constructions,
so stating them as independent modules would import their own consumer and form a cycle.
Move the constructions to a separate module and publicly reexport them from the item.
This is dependency factoring for independently provable mathematical steps, not a
compile-time workaround. No target statement or definition meaning changes.

## Old

The following declarations lived in
`Sheaf.Paper.AffineDiagonalIntegrationOrientation`:

```lean
abbrev affineDiagonalSpace (Y : Scheme.{u}) (d : ℕ) 
:= affineTraceTower Y d


abbrev affineDiagonalProjection (Y : Scheme.{u}) (d : ℕ) 
:= affineTraceProjection Y d


def affineDiagonalDifferences (Y : Scheme.{u}) (d : ℕ) (i : Fin d) 
:=
  (pullback.snd (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
      (affineTraceCoordinate Y d i) -
    (pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
      (affineTraceCoordinate Y d i)


theorem affineDiagonalDifference_lift (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :
    ∃! b : (ConormalGradedAlgebra.power
        (pullback.diagonal (affineDiagonalProjection Y d)) 1).val.obj (op ⊤),
      (ConormalGradedAlgebra.powerInclusion
        (pullback.diagonal (affineDiagonalProjection Y d)) 1).val.app (op ⊤) b =
          affineDiagonalDifferences Y d i 

def affineDiagonalDifferenceLift (Y : Scheme.{u}) (d : ℕ) (i : Fin d) 
:=
  (affineDiagonalDifference_lift Y d i).exists.choose


def affineDiagonalNormalFunction (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :
    Γ(PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)), ⊤) 
:=
  let s := pullback.diagonal (affineDiagonalProjection Y d)
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let b := ConormalGradedAlgebra.homogeneousClass s A
    (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ (affineDiagonalDifferenceLift Y d i)
  let c := A.right.obj.map (homOfLE (by simp)).op b
  (PurityNormalBundle.normalCone s).presheaf.map (homOfLE (by simp)).op
    ((Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op ⊤) c)


def affineDiagonalNormalCoordinates (Y : Scheme.{u}) (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d))) :
    (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ⟶
      affineTraceTower (affineDiagonalSpace Y d) d 
:=
  AffineSpace.homOfVector
      (Scheme.Hom.normalConeProj (pullback.fst (affineDiagonalProjection Y d)
        (affineDiagonalProjection Y d)) (pullback.diagonal (affineDiagonalProjection Y d)))
      (fun i : ULift.{u} (Fin d) ↦ q.hom.appTop (affineDiagonalNormalFunction Y d i.down)) ≫
    (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).inv


theorem affineDiagonalNormalCoordinates_spec (Y : Scheme.{u}) (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)))
    (_hq : Etale.FiniteSmoothPurity.ReesConeNormalized
      (pullback.diagonal (affineDiagonalProjection Y d)) q) :
    IsIso (affineDiagonalNormalCoordinates Y d q) ∧
    affineDiagonalNormalCoordinates Y d q ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
      Scheme.Hom.normalConeProj (pullback.fst (affineDiagonalProjection Y d)
        (affineDiagonalProjection Y d)) (pullback.diagonal (affineDiagonalProjection Y d)) 

def affineDiagonalProductCoordinates (Y : Scheme.{u}) (d : ℕ) :
    pullback (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) ⟶
      affineTraceTower (affineDiagonalSpace Y d) d 
:=
  AffineSpace.homOfVector
      (pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d))
      (fun i : ULift.{u} (Fin d) ↦
        (pullback.snd (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
          (affineTraceCoordinate Y d i.down)) ≫
    (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).inv


theorem affineDiagonalProductCoordinates_spec (Y : Scheme.{u}) (d : ℕ) :
    IsIso (affineDiagonalProductCoordinates Y d) ∧
      affineDiagonalProductCoordinates Y d ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
        pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) 

def affineDiagonalPresentedTranspose (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (e : U ≅ affineTraceTower B d) (he : e.hom ≫ affineTraceProjection B d = f) :
    Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r + 1)) hA U d ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f 
:=
  letI := P.noetherian aB
  let N := P.coefficients.l ^ (r + 1)
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  let t := Etale.ambientAffineTraceTransport N hN P.Coefficient hA
  let D := Etale.ambientAffineTraceDatum N hN P.Coefficient hA
  let q := affineTraceProjection B d
  letI := affineTraceNoetherian B d
  let sq : IsPullback e.hom f q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  let Q := (Etale.affineTraceRight P.Coefficient N hA B d).obj
    (Etale.ordinaryFiniteUnit P.Coefficient B)
  let tr := (Etale.affineLinearCompactComparison N hN P.Coefficient hA B
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d).inv ≫
      Etale.affineTraceCounit P.Coefficient N hA t D B
        (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d
  let z := (Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} P.Coefficient) q).homEquiv Q (𝟙_ _) tr
  let c := Etale.affineLinearCoefficientDescent P.Coefficient N hA t B
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d
  (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient N hA t f
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d).inv ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e.hom q f he.symm).hom.app
      (Etale.affineLinearBaseCoefficient P.Coefficient N hA B d) ≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map c.inv ≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map z ≫
    Etale.dualizingComplexBaseChangeMap P.Coefficient sq


def affineDiagonalPresentedIntegration (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (e : U ≅ affineTraceTower B d) (he : e.hom ≫ affineTraceProjection B d = f) 
:=
  ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f).homEquiv
    (Etale.affineLinearBaseCoefficient P.Coefficient
      (P.coefficients.l ^ (r + 1)) hA U d) (𝟙_ _)).symm
        (P.affineDiagonalPresentedTranspose d f aB r hA e he)


def affineDiagonalTranslatedCoordinates (Y : Scheme.{u}) (d : ℕ) 
:=
  affineDiagonalProductCoordinates Y d ≫
    (Etale.ambientAffineTranslation (affineDiagonalSpace Y d) d
      (affineTraceCoordinate Y d)).hom


theorem affineDiagonalTranslatedCoordinates_spec (Y : Scheme.{u}) (d : ℕ) :
    IsIso (affineDiagonalTranslatedCoordinates Y d) ∧
    affineDiagonalTranslatedCoordinates Y d ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
      pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) ∧
    pullback.diagonal (affineDiagonalProjection Y d) ≫
        affineDiagonalTranslatedCoordinates Y d ≫
          (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).hom =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) (affineDiagonalSpace Y d) ∧
    ∀ i : Fin d,
      (affineDiagonalTranslatedCoordinates Y d).appTop
        (affineTraceCoordinate (affineDiagonalSpace Y d) d i) =
          affineDiagonalDifferences Y d i 

theorem affineDiagonalProjection_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (affineDiagonalProjection Y d) 

def affineDiagonalPowerComparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
    (e : Scheme.finiteEtaleTateLine T (P.coefficients.l ^ (r' + 1)) P.Coefficient hA' ≅
      Scheme.finiteEtaleTateLine T (P.coefficients.l ^ (r + 1)) P.Coefficient hA) :
    (d : ℕ) →
      Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r' + 1)) hA' T d ≅
      Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r + 1)) hA T d
  
| 0 => Iso.refl _
  | d + 1 => Etale.ordinaryFiniteTensorRightMapIso P.Coefficient T
      (P.affineDiagonalPowerComparison T r r' hA hA' e d)
      ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))


def affineDiagonalTateRestriction (P : PurityFiniteSetting.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    {U B : Scheme.{u}} (f : U ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (d : ℕ) 
:=
  Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
    (Etale.ambientAffineTraceTransport (P.coefficients.l ^ (r + 1))
      (pow_pos P.coefficients.prime.out.pos (r + 1)) P.Coefficient hA)
    f (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d


```

## New

The same declarations now live in
`Sheaf.Paper.AffineDiagonalIntegrationConstructions`, publicly imported by the
original module. Every public signature is identical, and every definition body
is verbatim identical. Existing coordinate proofs are preserved; the normal
coordinate proof uses the already stated graded-coordinate isomorphism.
The original public imports are retained. The original theorem statements remain
in the original module. The two new statement modules import constructions alone,
so no import cycle arises. All four modules use only local elaboration attributes.
The new construction node records the existing construction package, rather than
introducing a second definition of any notion. Its complete implementation is in
`lean/Sheaf/Paper/AffineDiagonalIntegrationConstructions.lean`.

## Users

`python3 tools/downstream.py Sheaf.Paper.AffineDiagonalIntegrationOrientation --names`
reported no source importers. Parent DAG nodes still need the original orientation
node: it is retained with its statement and original module attachment. The new
proof imports and public construction reexport do not change those parents' types.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | P2 | Publicly reexports constructions; final theorem assembled from two smaller obligations. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | P2 delivery | Relocated identical constructions and coordinate proofs. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | P2 delivery | New trace/base-change and diagonal-restriction obligation. |
| Sheaf.Paper.AffineDiagonalDncNormalization | P2 delivery | New standard-pair DNC normalization obligation. |

## Status

landed 20261025T163943-L-914488 2026-10-25 (merge of deliver/P2/Sheaf.Paper.AffineDiagonalIntegrationOrientation)
