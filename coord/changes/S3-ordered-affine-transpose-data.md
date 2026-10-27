# AlgebraicGeometry.ProEtale.OrderedAffineTranspose

## Reason

The comparison-naturality, single-successor coefficient calculation and normalized line trace
need the actual transpose and projection definitions, independently of the theorem they prove.
Move the existing constructions to `Sheaf.Paper.OrderedAffineTransposeData` and publicly reexport
them from their original module. This prevents an import cycle for the three proof obligations.
The original declarations, signatures, visibility and bodies are preserved. Large canonical
map definitions gain `@[irreducible]` so elaboration does not expand the whole derived
construction while checking neighboring maps.
No object or morphism is replaced, and no target's mathematical meaning changes.
This is dependency separation for independently provable lemmas, not a compile-time workaround.

## Old

In `Sheaf.Paper.OrderedAffineTransposeProjection`, before the theorem:

```lean
/-- The canonical identification of the constant coefficient single complex with the tensor unit.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def unitEtaleIso (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    Etale.ordinaryFiniteUnit A Y ≅ 𝟙_ (Etale.DerivedCategoryModule A Y) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
    (Functor.Monoidal.εIso (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))).symm ≪≫
      DerivedCategory.singleFunctorObjUnitIso _

/-- The compared degree-zero coefficient object with its canonical bounded-below witness.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def unitPlus (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) : Plus A Y :=
  (siteComparisonDerivedPullbackPlus Y A).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (Etale.ordinaryFiniteConstant A Y))

/-- The standing compact-support functor at a positive coordinate projection, identity at zero.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def compact (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    (d : ℕ) → D P (iteratedAffineLine Y d) ⥤ D P Y
  | 0 => 𝟭 _
  | d + 1 =>
    letI := (projection_geometry Y (d + 1)).2
    rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P)) (iteratedAffineLineProj Y (d + 1))

/-- The published class-adjunction counit, normalized to the identity in dimension zero.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def counit (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    [CompactSpace Y] (K : Plus (Ring P) Y) : (d : ℕ) →
    (compact P Y d).obj ((exceptional P Y d).obj K.obj) ⟶ K.obj
  | 0 => by unfold compact exceptional; exact 𝟙 _
  | d + 1 => by
    letI := (projection_geometry Y (d + 1)).2
    unfold compact exceptional
    exact rightDerivedUpperShriekCounit (iteratedAffineLineProj Y (d + 1)) K.obj K.property

/-- Exactly tau_d,K: compact support of the recorded ordered comparison, followed by its counit.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def transpose (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    (compact P Y d).obj ((orderedSource P Y d).obj K.obj) ⟶ K.obj :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  (compact P Y d).map (affineSpacePurityComparison P Y aY K Ke hKe eK d) ≫ counit P Y K d

/-- Canonical reassociation from ordered right tensoring to tensoring with the ordered coefficient.
Zero uses the coefficient right unitor; each successor uses the tensor associator. No symmetry
or orientation is chosen.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def powerIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) (W M : C A T) :
    (d : ℕ) → (action ((tensor A T).flip.obj W) d).obj M ≅
      ((tensor A T).obj M).obj
        ((action ((tensor A T).flip.obj W) d).obj (unit A T))
  | 0 => (moduleRightUnit A T M).symm
  | d + 1 => ((tensor A T).flip.obj W).mapIso (powerIso A T W M d) ≪≫
    (α_ M ((action ((tensor A T).flip.obj W) d).obj (unit A T)) W)

/-- The published ordered tensor power of the shifted finite Tate line, T_d=A(d)[2d].
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def tate (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :
    D P (iteratedAffineLine Y d) :=
  (twistAction P (iteratedAffineLine Y d) d).obj (unit (Ring P) (iteratedAffineLine Y d))

/-- The canonical reassociation F_d(K) = Lp_d* K tensor T_d.
It uses powerIso at positive dimension and the identity-pullback unitor at zero.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def sourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) : (d : ℕ) → (orderedSource P Y d).obj K ≅
      projectionSourceObject (Ring P) (iteratedAffineLineProj Y d) (tate P Y d) K
  | 0 => by
    unfold orderedSource projectionSourceObject tate twistAction action
    exact (moduleRightUnit (Ring P) Y K).symm ≪≫
      ((tensor (Ring P) Y).mapIso ((inverseImageId (Ring P) Y).app K).symm).app _
  | d + 1 => by
    unfold orderedSource projectionSourceObject tate twistAction
    exact powerIso (Ring P) (iteratedAffineLine Y (d + 1))
      (shiftedLine P (iteratedAffineLine Y (d + 1))) _ (d + 1)

/-- Canonical inverse-image comparison of the coefficient unit, via the recorded site square.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def unitPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (inverseImage A f).obj (unit A Y) ≅ unit A X :=
  ((pullback A f).app (Etale.ordinaryFiniteUnit A Y)).symm ≪≫
    (comparison A X).mapIso (Etale.ordinaryFiniteUnitPullback A f)

/-- Canonical identification F_d(A_Y) with T_d by inverse image of the coefficient unit.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def tateSourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    (d : ℕ) → (orderedSource P Y d).obj (unit (Ring P) Y) ≅ tate P Y d
  | 0 => by unfold orderedSource tate twistAction action; exact Iso.refl _
  | d + 1 => by
    unfold orderedSource
    exact (twistAction P (iteratedAffineLine Y (d + 1)) (d + 1)).mapIso
      (unitPull (Ring P) (iteratedAffineLineProj Y (d + 1)))

/-- I_d, defined from tau_d,A with its source changed by the canonical coefficient-unit map.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def integration (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    (compact P Y d).obj (tate P Y d) ⟶ unit (Ring P) Y :=
  (compact P Y d).map (tateSourceIso P Y d).inv ≫
    transpose P Y aY (unitPlus (Ring P) Y) (Etale.ordinaryFiniteUnit (Ring P) Y)
      ((Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y).prop_of_iso
        (unitEtaleIso (Ring P) Y).symm (Etale.constructibleFiniteTor_unit (Ring P))) (Iso.refl _) d

/-- The actual coefficient-first projection transformation, in ordered-source coordinates.
Its two tensor symmetries are exactly VectorIntegrationSite.projection. Dimension zero
is the coefficient right unitor; no projection-formula inverse is assumed.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def projection (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) : (d : ℕ) →
    ((tensor (Ring P) Y).obj K).obj ((compact P Y d).obj (tate P Y d)) ⟶
      (compact P Y d).obj ((orderedSource P Y d).obj K)
  | 0 => by
    unfold compact orderedSource tate twistAction action
    exact (moduleRightUnit (Ring P) Y K).hom
  | d + 1 => by
    letI := (projection_geometry Y (d + 1)).2
    have e := (sourceIso P Y K (d + 1)).inv
    unfold projectionSourceObject at e
    exact VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
      (HasCompactification.compactification (iteratedAffineLineProj Y (d + 1)))
      (tate P Y (d + 1)) K ≫
        (compact P Y (d + 1)).map e

/-- Inverse of the specified projection component, using only its isomorphy proof.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def projectionInverse (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (d : ℕ) (h : IsIso (projection P Y K d)) :=
  @inv _ _ _ _ (projection P Y K d) h

/-- Canonical change of compactification on a retained bounded-below etale source.
It is the proper/open site comparison, the ordinary canonical compactification comparison,
and their inverses; no arbitrary compactification isomorphism is chosen.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def fixedSourceTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [QuasiCompact f]
    (c : Compactification f) (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) (M : C A X) (e : (comparison A X).obj L.obj ≅ M) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).mapIso e.symm ≪≫
    (compactSupportSiteComparison A (HasCompactification.compactification f)).app L ≪≫
    (comparison A Y).mapIso ((Etale.rightDerivedLowerShriekIso A c).symm.app L.obj) ≪≫
    ((compactSupportSiteComparison A c).app L).symm ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso e

/-- Canonical identification of the line source at A_Y with its prescribed shifted Tate line.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def lineUnitSourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    source P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P)
      (unit (Ring P) Y) ≅
    coefficient P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P) :=
  eqToIso (source_eq P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P)
    (unit (Ring P) Y)) ≪≫
    ((tensor (Ring P) (AffineSpace PUnit.{u + 1} Y)).mapIso
      (unitPull (Ring P) (AffineSpace PUnit.{u + 1} Y ↘ Y) ≪≫
        coefficientUnitIso (ModuleCat.{u + 1} (Ring P)) _)).app _ ≪≫ (λ_ _)

/-- The specified normalized line integration, transported to the standing compact-support source.
Use the recorded source reassociation and the actual open-counit restriction of projective trace.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def lineNormalizedIntegration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] :
    (compact P Y 1).obj (tate P Y 1) ⟶ unit (Ring P) Y :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  letI := (projection_geometry Y 1).2
  let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) (unit (Ring P) Y) (Etale.ordinaryFiniteUnit (Ring P) Y)
      ((Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y).prop_of_iso
        (unitEtaleIso (Ring P) Y).symm (Etale.constructibleFiniteTor_unit (Ring P))) (Iso.refl _)
  let e0 : (orderedSource P Y 1).obj (unit (Ring P) Y) ⟶
      (lineSource P Y).obj (unit (Ring P) Y) := by
    have e := (sourceReassociation P Y aY (unit (Ring P) Y) 0).hom
    unfold orderedSource at e ⊢
    exact e
  let e := (tateSourceIso P Y 1).inv ≫
    e0 ≫
      eqToHom (lineSource_obj_eq P Y (unit (Ring P) Y))
  (compact P Y 1).map e ≫
    (fixedSourceTransport (Ring P) (affineTraceLineCompactification Y)
      W.complex _ W.iso).hom ≫
    (lineLeft (Ring P) Y).map (lineUnitSourceIso P Y).hom ≫
    AffineLinePurity.integration P.coefficients.l P.extension (P.level - 1) Y
      P.level (annihilates P) (primeUnit P Y aY)

/-- The block transpose equality on Rg_! Rf_! F_f F_g K for arbitrary block lengths a,b.
The left side is the composite-adjunction transpose of Gamma_f,Rg!K F_f(Gamma_g,K).
By the definition of AffineSpacePurity.compositionInverse (transpose of the pasted counit),
this is exactly the transpose after c_g,f inverse and precomposition with compact-support
composition. Both zero cases use the normalized identity counits. B,hB and its ordinary
representative merely retain the applicability witness for F_g K, as in the line definition.
All geometry instances are consequences of the given base map.
Source: current blueprint ordered-composite proof Steps 2--4
(blueprint: lem-pur-ordered-affine-transpose-projection). -/
def BlockLaw (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (a b : ℕ) : Prop :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : LocallyOfFiniteType (towerBase aY b) := (tower_geometry aY b).1
  letI : QuasiCompact (towerBase aY b) := (tower_geometry aY b).2.1
  letI : IsSeparated (towerBase aY b) := (tower_geometry aY b).2.2
  letI : IsNoetherian (iteratedAffineLine Y b) := tower_noetherian P Y aY b
  ∀ (B : Plus (Ring P) (iteratedAffineLine Y b))
    (hB : B.obj = (orderedSource P Y b).obj K.obj)
    (Be : Etale.DerivedCategoryModule (Ring P) (iteratedAffineLine Y b))
    (hBe : etaleFiniteTor (Ring P) (iteratedAffineLine Y b) Be)
    (eB : (comparison (Ring P) (iteratedAffineLine Y b)).obj Be ≅ B.obj),
    (compact P Y b).map
      ((compact P (iteratedAffineLine Y b) a).map
        ((orderedSource P (iteratedAffineLine Y b) a).map
          (eqToHom hB ≫ affineSpacePurityComparison P Y aY K Ke hKe eK b) ≫
          affineSpacePurityComparison P (iteratedAffineLine Y b) (towerBase aY b)
            ⟨_, (stage_applicability P Y aY K Ke hKe eK b).1⟩
            (stageEtale P Y K.obj Ke b) (stage_applicability P Y aY K Ke hKe eK b).2
            (stageComparison P Y K.obj Ke eK b) a) ≫
        counit P (iteratedAffineLine Y b)
          ⟨_, (stage_applicability P Y aY K Ke hKe eK b).1⟩ a) ≫ counit P Y K b =
    (compact P Y b).map
      (transpose P (iteratedAffineLine Y b) (towerBase aY b) B Be hBe eB a) ≫
      (compact P Y b).map (eqToHom hB) ≫ transpose P Y aY K Ke hKe eK b

```

## New

The Lean block above, with unchanged bodies and signatures, is in `Sheaf.Paper.OrderedAffineTransposeData`; its
blueprint docstring tags name the new definition node. The following definitions gain
`@[irreducible]`: `counit`, `transpose`, `powerIso`, `sourceIso`, `tateSourceIso`, `integration`,
`projection`, `fixedSourceTransport`, `lineUnitSourceIso`, `lineNormalizedIntegration`,
and `BlockLaw`. Profiling the first data compile showed 46.8 seconds of type checking
and 48.1 seconds of linting; suppressing automatic expansion at these definition
boundaries avoids repeatedly normalizing their full derived constructions. Explicit
`unfold` remains available for the computations in the item proof. The original module contains:

```lean
public import Sheaf.Paper.OrderedAffineTransposeData
```

Its existing three public imports remain. The new data module has those same public imports;
all statement and definition prerequisites are reexported. The item privately imports the three
new obligation modules and proves its unchanged theorem by dimension induction, zero
normalization, the line lemma and counit naturality. No consumer edit is necessary.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.OrderedAffineTransposeProjection | S3 | Proves the original theorem and reexports unchanged data. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Direct importer (public import of the item module); uses compact, tate, unitPull. Unchanged names, signatures, data and visibility by public reexport; compiles unchanged against the delivery. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Uses compact, tate, tateSourceIso, integration through AffineSpaceTraceProductData; compiles unchanged. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Uses compact, tate, lineNormalizedIntegration; compiles unchanged. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Uses unitEtaleIso, unitPlus, compact, tate, integration, lineNormalizedIntegration; compiles unchanged. |

No consumer edit is needed. The added `@[irreducible]` attributes are visible to all four consumers;
each was compiled (reviewer, 2026-10-26) against the delivered modules without change.
Existing trace-data ownership moves to the data module, preserving its five declaration attachments.
A separate new definition node owns the remaining construction declarations. No node is withdrawn.

## Status

landed 20261025T211647-L-4017776 2026-10-25 (merge of deliver/S3/Sheaf.Paper.OrderedAffineTransposeProjection)
