# NestedAffine shared formula data relocation

## Reason

The normalization, affine regrouping and chart-transport steps need the existing
arrow definitions without importing the theorem that combines them. Move those
constructions into a separate module and publicly reexport it. This prevents an
import cycle; it is not a compile-time workaround. No statement or construction
changes meaning, and no declaration is deleted. No WeilConjectures source file
is edited.

## Old

The following declarations were in
`Sheaf.SecSmoothPurity.NestedAffineOrientation`, in namespace
`WeilConjectures.PurityFiniteSetting.NestedAffine`:

```lean
variable (P : PurityFiniteSetting.{u})

/-- The canonical Tate pullback, with its even shifts already included.
Source: proof (1), canonical source comparisons
(blueprint: lem-sp-nested-affine-orientation). -/
def twistPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) (m : ℕ) :
    (Etale.ordinaryFinitePullback P.Coefficient f).obj (P.diagonalTwistEtale Y m) ≅
      P.diagonalTwistEtale X m :=
  Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)
    f (P.diagonalExponent_isUnit aY) m

/-- The ordered affine integration transpose at the coefficient object.
Source: proof (1), Gamma at R (blueprint: lem-sp-nested-affine-orientation). -/
def gammaUnit (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (m : ℕ) :=
  P.diagonalAffineMate
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)
    (fun T _ hT => Etale.projectiveLineTraceDatum P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates T hT)
    S (P.diagonalExponent_isUnit aS) m

/-- Gamma at an arbitrary coefficient complex is the actual integration transpose.
Source: proof (1), Gamma at H (blueprint: lem-sp-nested-affine-orientation). -/
def gamma (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (m : ℕ)
    (H : Etale.DerivedCategoryModule P.Coefficient S) :=
  DiagonalAffineTrace.ordinaryTranspose P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) m H

/-- The source comparison to the e-block followed by the d-block. The symmetry
is precisely the even-block interchange in the source statement.
Source: proof (1), tensor and shift reassociation
(blueprint: lem-sp-nested-affine-orientation). -/
def source {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) (d e : ℕ) :
    P.diagonalTwistEtale X (d + e) ≅
      ((Etale.ordinaryFiniteTensor P.Coefficient X).obj
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj
          (P.diagonalTwistEtale Y e))).obj (P.diagonalTwistEtale X d) :=
  NestedAffineCoordinates.compositionEtalePowerAdd P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates X d e ≪≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.diagonalTwistEtale X d)).app (P.diagonalTwistEtale X e) ≪≫
    ((Etale.ordinaryFiniteTensor P.Coefficient X).mapIso
      (twistPull P f aY e).symm).app (P.diagonalTwistEtale X d)

/-- The specified inverse diagonal orientation in ordinary coefficient coordinates.
Source: proof (1), a_w (blueprint: lem-sp-nested-affine-orientation). -/
def orientation {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  (NestedAffineCoordinates.chartOrdinaryOrientation P d f aY).inv

/-- The tensor route before the inverse exceptional compositor.
Source: proof (1), second displayed global arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def tensorRoute {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :=
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  (source P f (g ≫ aZ) d e).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.ordinaryFinitePullback P.Coefficient f).map (orientation P e g aZ))
      (orientation P d f (g ≫ aZ)) ≫
    smoothPurityEtaleTheta P.Coefficient f (P.diagonalOrdinaryDualizing g)

/-- Ordered flattening keeps every coordinate, including empty blocks.
Source: proof (1), affine-space coordinate identification
(blueprint: lem-sp-nested-affine-orientation).
Proof: induction on d. For d=0 this is the identity on the e-fold tower.
A successor applies the affine-line functor to the induction equality; rewrite
addition associativity to obtain the total rank d+e. -/
theorem blockEq (S : Scheme.{u}) (d e : ℕ) :
    affineTraceTower (affineTraceTower S e) d = affineTraceTower S (d + e) := by
  induction d with
  | zero => simp only [Nat.zero_add, affineTraceTower]
  | succ d ih =>
    simpa only [Nat.succ_add, affineTraceTower] using
      congrArg (AffineSpace PUnit.{u + 1}) ih

/-- Flattening respects the actual projections.
Source: proof (1), affine-space coordinate identification
(blueprint: lem-sp-nested-affine-orientation).
Proof: induct on d in blockEq. The zero step is the identity unitor. At a
successor the affine-line projection is natural for the preceding equality;
compose its projection with the induction equation and reassociate. -/
theorem blockProjection (S : Scheme.{u}) (d e : ℕ) :
    (eqToIso (blockEq S d e)).hom ≫ affineTraceProjection S (d + e) =
      affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e := by
  let tower (n : ℕ) : Σ T : Scheme.{u}, T ⟶ S :=
    ⟨affineTraceTower S n, affineTraceProjection S n⟩
  let step (q : Σ T : Scheme.{u}, T ⟶ S) : Σ T : Scheme.{u}, T ⟶ S :=
    ⟨AffineSpace PUnit.{u + 1} q.1, (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩
  have hp :
      (⟨affineTraceTower (affineTraceTower S e) d,
        affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e⟩ :
          Σ T : Scheme.{u}, T ⟶ S) = tower (d + e) := by
    induction d with
    | zero =>
      rw [Nat.zero_add]
      simp only [tower, affineTraceTower, affineTraceProjection, Category.id_comp]
    | succ d ih =>
      rw [Nat.succ_add]
      calc
        _ = step ⟨affineTraceTower (affineTraceTower S e) d,
            affineTraceProjection (affineTraceTower S e) d ≫
              affineTraceProjection S e⟩ := by
          simp only [step, affineTraceTower, affineTraceProjection, Category.assoc]
        _ = step (tower (d + e)) := congrArg step ih
        _ = tower ((d + e) + 1) := rfl
  have transport {A B : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S)
      (h : (⟨A, f⟩ : Σ T : Scheme.{u}, T ⟶ S) = ⟨B, g⟩) (w : A = B) :
      (eqToIso w).hom ≫ g = f := by
    cases h
    simp
  exact transport _ _ hp (blockEq S d e)

/-- Total ordered affine integration, transported through coordinate flattening.
Source: proof (1), first affine arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def total (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  letI := affineTraceNoetherian S (d + e)
  let i := (eqToIso (blockEq S d e)).hom
  let p := affineTraceProjection S (d + e)
  (twistPull P i (p ≫ aS) (d + e)).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient i).map (gammaUnit P S aS (d + e)) ≫
    (P.diagonalEtaleLocality N i p).hom ≫
    (P.diagonalDualizingCongr (blockProjection S d e)).hom

/-- The iterated ordered integrations, with the same exceptional compositor.
Source: proof (1), second affine arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def iterated (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  let p := affineTraceProjection S e
  let q := affineTraceProjection (affineTraceTower S e) d
  (source P q (p ≫ aS) d e).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.ordinaryFinitePullback P.Coefficient q).map (gammaUnit P S aS e))
      (𝟙 (P.diagonalTwistEtale (affineTraceTower (affineTraceTower S e) d) d)) ≫
    gamma P (affineTraceTower S e) (p ≫ aS) d (P.diagonalOrdinaryDualizing p) ≫
    (finiteExceptionalComposition P.Coefficient q p).inv.app
      (Etale.ordinaryFiniteUnit P.Coefficient S)

/-- The affine base change of an etale map is etale.
Source: proof (1), Cartesian affine square
(blueprint: lem-sp-nested-affine-orientation).
Proof: the polynomial-coordinate square is the Cartesian square
`affineTraceMap_isPullback`; apply stability of etaleness under base change. -/
theorem mapEtale {V T : Scheme.{u}} (v : V ⟶ T) [Etale v] (d : ℕ) :
    Etale (affineTraceMap v d) := by
  exact MorphismProperty.of_isPullback (affineTraceMap_isPullback v d).flip
    (inferInstanceAs (Etale v))

/-- The composite chart lies over the restricted composite, in the stated order.
Source: proof (1), the Cartesian square and nested coordinates
(blueprint: lem-sp-nested-affine-orientation).
Proof: the affine map square commutes. Precompose by u, postcompose by the
rank-e projection, substitute the two chart equations and reassociate. -/
theorem chartComposite {U V S : Scheme.{u}} (d e : ℕ)
    (u : U ⟶ affineTraceTower V d) (v : V ⟶ affineTraceTower S e)
    (f : U ⟶ V) (g : V ⟶ S)
    (hu : u ≫ affineTraceProjection V d = f)
    (hv : v ≫ affineTraceProjection S e = g) :
    (u ≫ affineTraceMap v d) ≫
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e) =
      f ≫ g := by
  calc
    (u ≫ affineTraceMap v d) ≫
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e) =
        (u ≫ affineTraceProjection V d) ≫ (v ≫ affineTraceProjection S e) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ u ≫ z ≫ affineTraceProjection S e) (affineTraceMap_isPullback v d).w
    _ = f ≫ g := by rw [hu, hv]

/-- Pull an affine arrow back to the chart, using actual source-etale locality.
Source: proof (1), common target identification for the two displayed arrows
(blueprint: lem-sp-nested-affine-orientation). -/
def chartPull (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ)
    {U : Scheme.{u}} [IsNoetherian U]
    (k : U ⟶ affineTraceTower (affineTraceTower S e) d)
    [Etale k] [IsSeparated k] [LocallyOfFiniteType k] [QuasiCompact k]
    (h : U ⟶ S) [HasCompactification h]
    (w : k ≫ (affineTraceProjection (affineTraceTower S e) d ≫
      affineTraceProjection S e) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (phi : P.diagonalTwistEtale
        (affineTraceTower (affineTraceTower S e) d) (d + e) ⟶
      P.diagonalOrdinaryDualizing
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e)) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  letI : HasCompactification
      (k ≫ (affineTraceProjection (affineTraceTower S e) d ≫
        affineTraceProjection S e)) := HasCompactification.of_eq w.symm
  (twistPull P k
    ((affineTraceProjection (affineTraceTower S e) d ≫
      affineTraceProjection S e) ≫ aS) (d + e)).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient k).map phi ≫
    (P.diagonalEtaleLocality N k
      (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e)).hom ≫
    (P.diagonalDualizingCongr w).hom

/-- Source of rank-zero Gamma, through identity pullback and the tensor unit.
Source: proof (1), empty coordinate block
(blueprint: lem-sp-nested-affine-orientation). -/
def zeroSource (B : Scheme.{u}) (H : Etale.DerivedCategoryModule P.Coefficient B) :=
  ((Etale.ordinaryFiniteTensor P.Coefficient B).mapIso
    ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app H)).app
      (Etale.ordinaryFiniteUnit P.Coefficient B) ≪≫
  ((Etale.ordinaryFiniteTensor P.Coefficient B).obj H).mapIso
    (smoothPurityUnitIso P.Coefficient B) ≪≫
  Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} P.Coefficient) B H

/-- All coefficient-domain and normalization clauses used by the nested charts.
Source: proof (1), Gamma normalization and domain checks
(blueprint: lem-sp-nested-affine-orientation). -/
def NormalizedInputs : Prop :=
  ∀ (B : Scheme.{u}) [IsAffine B]
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (m : ℕ),
    letI := P.noetherian aB
    letI := NestedAffineCoordinates.chartTraceProjection_smooth B m
    orientation P m (affineTraceProjection B m) aB = gammaUnit P B aB m ∧
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
      (affineTraceTower B m) (P.diagonalOrdinaryDualizing (affineTraceProjection B m)) ∧
    (∀ H : Etale.DerivedCategoryModule P.Coefficient B,
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) B H →
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceTower B m)
        (DiagonalAffineTrace.OrdinarySource P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates B m H) ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceTower B m)
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
          (affineTraceProjection B m)).obj H) ∧
      gamma P B aB m H =
        Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
          (𝟙 ((Etale.ordinaryFinitePullback P.Coefficient
            (affineTraceProjection B m)).obj H)) (gammaUnit P B aB m) ≫
          smoothPurityEtaleTheta P.Coefficient (affineTraceProjection B m) H ∧
      gamma P B aB 0 H ≫
          ((Etale.rightDerivedUpperShriekIsoOfIso
            (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app H).hom ≫
          ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app H).hom =
        (zeroSource P B H).hom) ∧
    gammaUnit P B aB 0 =
      (((Etale.rightDerivedUpperShriekIsoOfIso
        (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)) ≪≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)).inv


/-- The two nested-chart formulas, read in the common exceptional-composite
coordinates. Source: blueprint composition factors, proof (1)
(blueprint: lem-sp-nested-affine-orientation). -/
def Statement
    (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (S : Z.Opens) (V : Y.Opens) (U : X.Opens)
    [IsAffine S.toScheme] [IsAffine V.toScheme] [IsAffine U.toScheme]
    (hV : V ≤ g ⁻¹ᵁ S) (hU : U ≤ f ⁻¹ᵁ V)
    (v : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin e)) S.toScheme)
    (u : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme)
    [Etale v] [Etale u]
    (hv : (v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv) ≫
      affineTraceProjection S.toScheme e = g.resLE S V hV)
    (hu : (u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv) ≫
      affineTraceProjection V.toScheme d = f.resLE V U hU) : Prop :=
  letI := P.noetherian aZ
  letI := P.noetherian (g ≫ aZ)
  letI := P.noetherian (f ≫ g ≫ aZ)
  letI := isNoetherian_of_locallyOfFiniteType S.ι
  letI := isNoetherian_of_locallyOfFiniteType V.ι
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian S.toScheme e
  letI := affineTraceNoetherian (affineTraceTower S.toScheme e) d
  letI : SmoothOfRelativeDimension (d + e) (f ≫ g) :=
    smoothOfRelativeDimension_comp (n := d) (m := e) f g
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  letI := Dnc.compactifiable P (f ≫ g) aZ
  let fU := f.resLE V U hU
  let gV := g.resLE S V hV
  let h0 := fU ≫ gV
  let vt := v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv
  let ut := u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv
  let k := ut ≫ affineTraceMap vt d
  letI : Etale (affineTraceMap vt d) := mapEtale vt d
  letI : Etale k := inferInstance
  let wk := chartComposite d e ut vt fU gV hu hv
  letI : IsSeparated
      (k ≫ (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
        affineTraceProjection S.toScheme e)) := wk.symm ▸ inferInstanceAs (IsSeparated h0)
  letI := IsSeparated.of_comp k
    (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
      affineTraceProjection S.toScheme e)
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  letI : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  letI : U.toScheme.Over (Spec (.of P.field.k)) := ⟨U.ι ≫ f ≫ g ≫ aZ⟩
  letI : S.toScheme.Over (Spec (.of P.field.k)) := ⟨S.ι ≫ aZ⟩
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ aZ))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aZ)
  letI : QuasiCompact (Z ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aZ)
  letI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ f ≫ g ≫ aZ))
  letI : QuasiCompact (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.ι ≫ aZ))
  letI : QuasiCompact (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (S.ι ≫ aZ))
  letI : (f ≫ g).IsOver (Spec (.of P.field.k)) := ⟨by
      change (f ≫ g) ≫ aZ = f ≫ g ≫ aZ
      simp [Category.assoc]⟩
  letI : U.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : S.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h0.IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change h0 ≫ (S.ι ≫ aZ) = U.ι ≫ f ≫ g ≫ aZ
      simp [h0, fU, gV, Category.assoc]⟩
  let sq : CommSq U.ι h0 (f ≫ g) S.ι :=
    ⟨by simp [h0, fU, gV, Category.assoc]⟩
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    let r :=
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).mapIso
        (NestedAffineCoordinates.chartDualizingUnit P (f ≫ g)).symm ≪≫
      ProEtale.DualizingLocality.restriction P (f ≫ g) h0 U.ι S.ι sq ≪≫
      NestedAffineCoordinates.chartDualizingUnit P h0
    let lhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (orientation P (d + e) (f ≫ g) aZ) ≫ r.hom
    let rhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (tensorRoute P d e f g aZ ≫
          (finiteExceptionalComposition P.Coefficient f g).inv.app
            (Etale.ordinaryFiniteUnit P.Coefficient Z)) ≫ r.hom
    let aff := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (total P S.toScheme (S.ι ≫ aZ) d e N)
    let it := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (iterated P S.toScheme (S.ι ≫ aZ) d e)
    lhs = aff ∧ rhs = it ∧
      total P S.toScheme (S.ι ≫ aZ) d e N =
        iterated P S.toScheme (S.ι ≫ aZ) d e ∧
      aff = it ∧ lhs = rhs ∧ NormalizedInputs P ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        Y (P.diagonalOrdinaryDualizing g) ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        X ((Etale.ordinaryFinitePullback P.Coefficient f).obj
          (P.diagonalOrdinaryDualizing g)) ∧
      (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1

```

## New

The same declarations, with exactly the signatures, visibility and bodies above,
are in `Sheaf.SecSmoothPurity.NestedAffineFormulaData`:

```lean
variable (P : PurityFiniteSetting.{u})

/-- The canonical Tate pullback, with its even shifts already included.
Source: proof (1), canonical source comparisons
(blueprint: lem-sp-nested-affine-orientation). -/
def twistPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) (m : ℕ) :
    (Etale.ordinaryFinitePullback P.Coefficient f).obj (P.diagonalTwistEtale Y m) ≅
      P.diagonalTwistEtale X m :=
  Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)
    f (P.diagonalExponent_isUnit aY) m

/-- The ordered affine integration transpose at the coefficient object.
Source: proof (1), Gamma at R (blueprint: lem-sp-nested-affine-orientation). -/
def gammaUnit (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (m : ℕ) :=
  P.diagonalAffineMate
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)
    (fun T _ hT => Etale.projectiveLineTraceDatum P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates T hT)
    S (P.diagonalExponent_isUnit aS) m

/-- Gamma at an arbitrary coefficient complex is the actual integration transpose.
Source: proof (1), Gamma at H (blueprint: lem-sp-nested-affine-orientation). -/
def gamma (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (m : ℕ)
    (H : Etale.DerivedCategoryModule P.Coefficient S) :=
  DiagonalAffineTrace.ordinaryTranspose P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) m H

/-- The source comparison to the e-block followed by the d-block. The symmetry
is precisely the even-block interchange in the source statement.
Source: proof (1), tensor and shift reassociation
(blueprint: lem-sp-nested-affine-orientation). -/
def source {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) (d e : ℕ) :
    P.diagonalTwistEtale X (d + e) ≅
      ((Etale.ordinaryFiniteTensor P.Coefficient X).obj
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj
          (P.diagonalTwistEtale Y e))).obj (P.diagonalTwistEtale X d) :=
  NestedAffineCoordinates.compositionEtalePowerAdd P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates X d e ≪≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.diagonalTwistEtale X d)).app (P.diagonalTwistEtale X e) ≪≫
    ((Etale.ordinaryFiniteTensor P.Coefficient X).mapIso
      (twistPull P f aY e).symm).app (P.diagonalTwistEtale X d)

/-- The specified inverse diagonal orientation in ordinary coefficient coordinates.
Source: proof (1), a_w (blueprint: lem-sp-nested-affine-orientation). -/
def orientation {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  (NestedAffineCoordinates.chartOrdinaryOrientation P d f aY).inv

/-- The tensor route before the inverse exceptional compositor.
Source: proof (1), second displayed global arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def tensorRoute {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :=
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  (source P f (g ≫ aZ) d e).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.ordinaryFinitePullback P.Coefficient f).map (orientation P e g aZ))
      (orientation P d f (g ≫ aZ)) ≫
    smoothPurityEtaleTheta P.Coefficient f (P.diagonalOrdinaryDualizing g)

/-- Ordered flattening keeps every coordinate, including empty blocks.
Source: proof (1), affine-space coordinate identification
(blueprint: lem-sp-nested-affine-orientation).
Proof: induction on d. For d=0 this is the identity on the e-fold tower.
A successor applies the affine-line functor to the induction equality; rewrite
addition associativity to obtain the total rank d+e. -/
theorem blockEq (S : Scheme.{u}) (d e : ℕ) :
    affineTraceTower (affineTraceTower S e) d = affineTraceTower S (d + e) := by
  induction d with
  | zero => simp only [Nat.zero_add, affineTraceTower]
  | succ d ih =>
    simpa only [Nat.succ_add, affineTraceTower] using
      congrArg (AffineSpace PUnit.{u + 1}) ih

/-- Flattening respects the actual projections.
Source: proof (1), affine-space coordinate identification
(blueprint: lem-sp-nested-affine-orientation).
Proof: induct on d in blockEq. The zero step is the identity unitor. At a
successor the affine-line projection is natural for the preceding equality;
compose its projection with the induction equation and reassociate. -/
theorem blockProjection (S : Scheme.{u}) (d e : ℕ) :
    (eqToIso (blockEq S d e)).hom ≫ affineTraceProjection S (d + e) =
      affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e := by
  let tower (n : ℕ) : Σ T : Scheme.{u}, T ⟶ S :=
    ⟨affineTraceTower S n, affineTraceProjection S n⟩
  let step (q : Σ T : Scheme.{u}, T ⟶ S) : Σ T : Scheme.{u}, T ⟶ S :=
    ⟨AffineSpace PUnit.{u + 1} q.1, (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩
  have hp :
      (⟨affineTraceTower (affineTraceTower S e) d,
        affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e⟩ :
          Σ T : Scheme.{u}, T ⟶ S) = tower (d + e) := by
    induction d with
    | zero =>
      rw [Nat.zero_add]
      simp only [tower, affineTraceTower, affineTraceProjection, Category.id_comp]
    | succ d ih =>
      rw [Nat.succ_add]
      calc
        _ = step ⟨affineTraceTower (affineTraceTower S e) d,
            affineTraceProjection (affineTraceTower S e) d ≫
              affineTraceProjection S e⟩ := by
          simp only [step, affineTraceTower, affineTraceProjection, Category.assoc]
        _ = step (tower (d + e)) := congrArg step ih
        _ = tower ((d + e) + 1) := rfl
  have transport {A B : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S)
      (h : (⟨A, f⟩ : Σ T : Scheme.{u}, T ⟶ S) = ⟨B, g⟩) (w : A = B) :
      (eqToIso w).hom ≫ g = f := by
    cases h
    simp
  exact transport _ _ hp (blockEq S d e)

/-- Total ordered affine integration, transported through coordinate flattening.
Source: proof (1), first affine arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def total (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  letI := affineTraceNoetherian S (d + e)
  let i := (eqToIso (blockEq S d e)).hom
  let p := affineTraceProjection S (d + e)
  (twistPull P i (p ≫ aS) (d + e)).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient i).map (gammaUnit P S aS (d + e)) ≫
    (P.diagonalEtaleLocality N i p).hom ≫
    (P.diagonalDualizingCongr (blockProjection S d e)).hom

/-- The iterated ordered integrations, with the same exceptional compositor.
Source: proof (1), second affine arrow
(blueprint: lem-sp-nested-affine-orientation). -/
def iterated (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  let p := affineTraceProjection S e
  let q := affineTraceProjection (affineTraceTower S e) d
  (source P q (p ≫ aS) d e).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.ordinaryFinitePullback P.Coefficient q).map (gammaUnit P S aS e))
      (𝟙 (P.diagonalTwistEtale (affineTraceTower (affineTraceTower S e) d) d)) ≫
    gamma P (affineTraceTower S e) (p ≫ aS) d (P.diagonalOrdinaryDualizing p) ≫
    (finiteExceptionalComposition P.Coefficient q p).inv.app
      (Etale.ordinaryFiniteUnit P.Coefficient S)

/-- The affine base change of an etale map is etale.
Source: proof (1), Cartesian affine square
(blueprint: lem-sp-nested-affine-orientation).
Proof: the polynomial-coordinate square is the Cartesian square
`affineTraceMap_isPullback`; apply stability of etaleness under base change. -/
theorem mapEtale {V T : Scheme.{u}} (v : V ⟶ T) [Etale v] (d : ℕ) :
    Etale (affineTraceMap v d) := by
  exact MorphismProperty.of_isPullback (affineTraceMap_isPullback v d).flip
    (inferInstanceAs (Etale v))

/-- The composite chart lies over the restricted composite, in the stated order.
Source: proof (1), the Cartesian square and nested coordinates
(blueprint: lem-sp-nested-affine-orientation).
Proof: the affine map square commutes. Precompose by u, postcompose by the
rank-e projection, substitute the two chart equations and reassociate. -/
theorem chartComposite {U V S : Scheme.{u}} (d e : ℕ)
    (u : U ⟶ affineTraceTower V d) (v : V ⟶ affineTraceTower S e)
    (f : U ⟶ V) (g : V ⟶ S)
    (hu : u ≫ affineTraceProjection V d = f)
    (hv : v ≫ affineTraceProjection S e = g) :
    (u ≫ affineTraceMap v d) ≫
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e) =
      f ≫ g := by
  calc
    (u ≫ affineTraceMap v d) ≫
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e) =
        (u ≫ affineTraceProjection V d) ≫ (v ≫ affineTraceProjection S e) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ u ≫ z ≫ affineTraceProjection S e) (affineTraceMap_isPullback v d).w
    _ = f ≫ g := by rw [hu, hv]

/-- Pull an affine arrow back to the chart, using actual source-etale locality.
Source: proof (1), common target identification for the two displayed arrows
(blueprint: lem-sp-nested-affine-orientation). -/
def chartPull (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of P.field.k)) (d e : ℕ)
    {U : Scheme.{u}} [IsNoetherian U]
    (k : U ⟶ affineTraceTower (affineTraceTower S e) d)
    [Etale k] [IsSeparated k] [LocallyOfFiniteType k] [QuasiCompact k]
    (h : U ⟶ S) [HasCompactification h]
    (w : k ≫ (affineTraceProjection (affineTraceTower S e) d ≫
      affineTraceProjection S e) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (phi : P.diagonalTwistEtale
        (affineTraceTower (affineTraceTower S e) d) (d + e) ⟶
      P.diagonalOrdinaryDualizing
        (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e)) :=
  letI := affineTraceNoetherian S e
  letI := affineTraceNoetherian (affineTraceTower S e) d
  letI : HasCompactification
      (k ≫ (affineTraceProjection (affineTraceTower S e) d ≫
        affineTraceProjection S e)) := HasCompactification.of_eq w.symm
  (twistPull P k
    ((affineTraceProjection (affineTraceTower S e) d ≫
      affineTraceProjection S e) ≫ aS) (d + e)).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient k).map phi ≫
    (P.diagonalEtaleLocality N k
      (affineTraceProjection (affineTraceTower S e) d ≫ affineTraceProjection S e)).hom ≫
    (P.diagonalDualizingCongr w).hom

/-- Source of rank-zero Gamma, through identity pullback and the tensor unit.
Source: proof (1), empty coordinate block
(blueprint: lem-sp-nested-affine-orientation). -/
def zeroSource (B : Scheme.{u}) (H : Etale.DerivedCategoryModule P.Coefficient B) :=
  ((Etale.ordinaryFiniteTensor P.Coefficient B).mapIso
    ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app H)).app
      (Etale.ordinaryFiniteUnit P.Coefficient B) ≪≫
  ((Etale.ordinaryFiniteTensor P.Coefficient B).obj H).mapIso
    (smoothPurityUnitIso P.Coefficient B) ≪≫
  Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} P.Coefficient) B H

/-- All coefficient-domain and normalization clauses used by the nested charts.
Source: proof (1), Gamma normalization and domain checks
(blueprint: lem-sp-nested-affine-orientation). -/
def NormalizedInputs : Prop :=
  ∀ (B : Scheme.{u}) [IsAffine B]
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (m : ℕ),
    letI := P.noetherian aB
    letI := NestedAffineCoordinates.chartTraceProjection_smooth B m
    orientation P m (affineTraceProjection B m) aB = gammaUnit P B aB m ∧
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
      (affineTraceTower B m) (P.diagonalOrdinaryDualizing (affineTraceProjection B m)) ∧
    (∀ H : Etale.DerivedCategoryModule P.Coefficient B,
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) B H →
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceTower B m)
        (DiagonalAffineTrace.OrdinarySource P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates B m H) ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceTower B m)
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
          (affineTraceProjection B m)).obj H) ∧
      gamma P B aB m H =
        Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
          (𝟙 ((Etale.ordinaryFinitePullback P.Coefficient
            (affineTraceProjection B m)).obj H)) (gammaUnit P B aB m) ≫
          smoothPurityEtaleTheta P.Coefficient (affineTraceProjection B m) H ∧
      gamma P B aB 0 H ≫
          ((Etale.rightDerivedUpperShriekIsoOfIso
            (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app H).hom ≫
          ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app H).hom =
        (zeroSource P B H).hom) ∧
    gammaUnit P B aB 0 =
      (((Etale.rightDerivedUpperShriekIsoOfIso
        (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)) ≪≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)).inv


/-- The two nested-chart formulas, read in the common exceptional-composite
coordinates. Source: blueprint composition factors, proof (1)
(blueprint: lem-sp-nested-affine-orientation). -/
def Statement
    (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (S : Z.Opens) (V : Y.Opens) (U : X.Opens)
    [IsAffine S.toScheme] [IsAffine V.toScheme] [IsAffine U.toScheme]
    (hV : V ≤ g ⁻¹ᵁ S) (hU : U ≤ f ⁻¹ᵁ V)
    (v : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin e)) S.toScheme)
    (u : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme)
    [Etale v] [Etale u]
    (hv : (v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv) ≫
      affineTraceProjection S.toScheme e = g.resLE S V hV)
    (hu : (u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv) ≫
      affineTraceProjection V.toScheme d = f.resLE V U hU) : Prop :=
  letI := P.noetherian aZ
  letI := P.noetherian (g ≫ aZ)
  letI := P.noetherian (f ≫ g ≫ aZ)
  letI := isNoetherian_of_locallyOfFiniteType S.ι
  letI := isNoetherian_of_locallyOfFiniteType V.ι
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian S.toScheme e
  letI := affineTraceNoetherian (affineTraceTower S.toScheme e) d
  letI : SmoothOfRelativeDimension (d + e) (f ≫ g) :=
    smoothOfRelativeDimension_comp (n := d) (m := e) f g
  letI := Dnc.compactifiable P f (g ≫ aZ)
  letI := Dnc.compactifiable P g aZ
  letI := Dnc.compactifiable P (f ≫ g) aZ
  let fU := f.resLE V U hU
  let gV := g.resLE S V hV
  let h0 := fU ≫ gV
  let vt := v ≫ (affineTraceAffineSpaceIso S.toScheme e).inv
  let ut := u ≫ (affineTraceAffineSpaceIso V.toScheme d).inv
  let k := ut ≫ affineTraceMap vt d
  letI : Etale (affineTraceMap vt d) := mapEtale vt d
  letI : Etale k := inferInstance
  let wk := chartComposite d e ut vt fU gV hu hv
  letI : IsSeparated
      (k ≫ (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
        affineTraceProjection S.toScheme e)) := wk.symm ▸ inferInstanceAs (IsSeparated h0)
  letI := IsSeparated.of_comp k
    (affineTraceProjection (affineTraceTower S.toScheme e) d ≫
      affineTraceProjection S.toScheme e)
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  letI : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  letI : U.toScheme.Over (Spec (.of P.field.k)) := ⟨U.ι ≫ f ≫ g ≫ aZ⟩
  letI : S.toScheme.Over (Spec (.of P.field.k)) := ⟨S.ι ≫ aZ⟩
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ aZ))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aZ)
  letI : QuasiCompact (Z ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aZ)
  letI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ f ≫ g ≫ aZ))
  letI : QuasiCompact (U.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ f ≫ g ≫ aZ))
  letI : LocallyOfFiniteType (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (S.ι ≫ aZ))
  letI : QuasiCompact (S.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (S.ι ≫ aZ))
  letI : (f ≫ g).IsOver (Spec (.of P.field.k)) := ⟨by
      change (f ≫ g) ≫ aZ = f ≫ g ≫ aZ
      simp [Category.assoc]⟩
  letI : U.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : S.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h0.IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change h0 ≫ (S.ι ≫ aZ) = U.ι ≫ f ≫ g ≫ aZ
      simp [h0, fU, gV, Category.assoc]⟩
  let sq : CommSq U.ι h0 (f ≫ g) S.ι :=
    ⟨by simp [h0, fU, gV, Category.assoc]⟩
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    let r :=
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).mapIso
        (NestedAffineCoordinates.chartDualizingUnit P (f ≫ g)).symm ≪≫
      ProEtale.DualizingLocality.restriction P (f ≫ g) h0 U.ι S.ι sq ≪≫
      NestedAffineCoordinates.chartDualizingUnit P h0
    let lhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (orientation P (d + e) (f ≫ g) aZ) ≫ r.hom
    let rhs := (twistPull P U.ι (f ≫ g ≫ aZ) (d + e)).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient U.ι).map
        (tensorRoute P d e f g aZ ≫
          (finiteExceptionalComposition P.Coefficient f g).inv.app
            (Etale.ordinaryFiniteUnit P.Coefficient Z)) ≫ r.hom
    let aff := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (total P S.toScheme (S.ι ≫ aZ) d e N)
    let it := chartPull P S.toScheme (S.ι ≫ aZ) d e k h0 wk N
      (iterated P S.toScheme (S.ι ≫ aZ) d e)
    lhs = aff ∧ rhs = it ∧
      total P S.toScheme (S.ι ≫ aZ) d e N =
        iterated P S.toScheme (S.ι ≫ aZ) d e ∧
      aff = it ∧ lhs = rhs ∧ NormalizedInputs P ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        Y (P.diagonalOrdinaryDualizing g) ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
        X ((Etale.ordinaryFinitePullback P.Coefficient f).obj
          (P.diagonalOrdinaryDualizing g)) ∧
      (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1

```

`NestedAffineOrientation` publicly imports that module, which also retains the
original public imports. The original theorem keeps its exact signature. The
three new theorem modules state only normalization, affine regrouping and the
two restriction formulas, respectively. The original node retains the assigned
theorem attachment; the new data node owns the moved declarations.

## Users

The source scan with `tools/downstream.py` finds zero current Lean importers of
the assigned module, and no external textual uses of its qualified declarations.
This does not justify withdrawal: unfinished DAG parents still need the theorem.
All existing names remain publicly available at the original import path.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | A9 | Publicly reexports every moved declaration; theorem signature identical. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | A9 (new) | Owns the unchanged constructions. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | A9 (new) | Imports the shared data to state normalization only. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | A9 (new) | Imports the shared data to state affine regrouping only. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | A9 (new) | Imports the shared data to state the two restriction identities only. |

No consumer needs adaptation and no target statement changes meaning. No forced
adaptation of a module held by another group is included.

## Status

landed 20261026T065133-L-2707807 2026-10-26 (merge of deliver/A9/Sheaf.SecSmoothPurity.NestedAffineOrientation)
