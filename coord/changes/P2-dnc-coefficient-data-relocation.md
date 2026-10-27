# WeilConjectures.DncCoefficientTransport data declarations

## Reason

Landing repair after returned head `54acfcee1b8`: the new data module no longer copies
the unused `set_option warn.sorry false` header command. The hole ledger treated the
option's final name component as an unattributed hole. No declaration changes in this
repair; the data module has zero holes.

The two missing coefficient-coherence lemmas must name the actual section maps. They cannot
import the main theorem module when that theorem imports them. Move its existing data into
Sheaf.SecSmoothPurity.DncCoefficientTransportData and publicly reexport that module from the
original module. All data signatures, values, visibility and attributes are retained. The
existing geometry theorem remains in the original module with the identical signature and
proof. The main theorem signature and all target signatures remain unchanged.

This is an import-cycle separation for mathematical interfaces, not a compilation-time split.
The packet creates no axiom, arbitrary object, replacement deformation, or coefficient
orientation. The definition node for dualizingMap/sectionMap has its Lean attachment updated.
A new data-ownership node records the other relocated definitions and assertion predicates.

## Old

In lean/Sheaf/SecSmoothPurity/PurityDncCoefficientTransport.lean:

```lean
namespace DncCoefficientTransport

/-- The coefficient ring Z/(ell^n), lifted only for size.
Source: Proof (2), R=Z/ell^n (blueprint: lem-pur-dnc-coefficient-transport). -/
abbrev BaseRing (ell n : ℕ) : Type u := ULift.{u} (ZMod (ell ^ n))

/-- The positive prime-power coefficient ring is finite, including n=0.
Source: Proof (2), finite coefficient convention
(blueprint: lem-pur-dnc-coefficient-transport). -/
instance baseRingFinite (ell n : ℕ) [Fact ell.Prime] : Finite (BaseRing.{u} ell n) :=
  letI : NeZero (ell ^ n) := ⟨ne_of_gt (pow_pos (Fact.out : ell.Prime).pos n)⟩
  inferInstance

/-- The canonical coefficient map on relative dualizing objects: transpose the
scalar-extended counit, then identify the extended unit with the B-unit.
Source: Proof (2), Step 1; det-sp-reduction-exceptional
(blueprint: lem-pur-dnc-coefficient-transport). -/
def dualizingMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] :
    (Etale.scalarExtension φ V).obj (Etale.dualizingComplex (ModuleCat.{u + 1} A) g) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} B) g :=
  Etale.ExceptionalCoefficients.mateMap φ g (𝟙_ _) ≫
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g).map
      (Etale.ExceptionalCoefficients.unitIso φ S).hom

/-- The actual section coefficient map: balancing for Ls* followed by Ls*(c_g).
Source: Proof (2), Step 1 (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (Etale.scalarExtension φ S).obj (Etale.sectionInvariant A g s) ⟶
      Etale.sectionInvariant B g s :=
  (Etale.scalarPullbackIso φ s).inv.app _ ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) s).leftDerivedFunctor.map (dualizingMap φ g)

/-- The genuine B-coefficient section object in the uncompleted pro-etale category.
This is the canonical site realization of Ls* g_B^! B_S, formed using g_B^!.
Source: Proof (2), definition of C_D (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionObject (A : Type u) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) :
    proEtaleDerivedCategory S A :=
  (ProEtale.reductionSite A S).obj (Etale.sectionInvariant (ULift.{u + 1, u} A) g s)

/-- The actual pro-etale coefficient map, with the fixed site/scalar comparison.
Source: Proof (2), q_(g,s) (blueprint: lem-pur-dnc-coefficient-transport). -/
def realizedSectionMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (ProEtale.scalarExtensionFunctor φ S).obj (sectionObject A g s) ⟶
      sectionObject B g s :=
  (ProEtale.reductionSiteScalarIso φ S).hom.app _ ≫
    (ProEtale.reductionSite B S).map (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s)

/-- Scalar compatibility with both canonical exceptional fibre mates of the Rees family.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def FibreCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ((Etale.scalarPullbackIso φ (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atOne B g s hs =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atOne A g s hs) ≫
      sectionMap φ g s) ∧
  ((Etale.scalarPullbackIso φ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atZero B g s =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atZero A g s) ≫
      sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Naturality for etale localization of pairs, using the specified exceptional mate.
Source: Proof (2), Steps 2--3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def LocalizationCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) : Prop :=
  ∀ {V' S' : Scheme.{u}} (g' : V' ⟶ S') [HasCompactification g'] [QuasiCompact g']
    (b : S' ⟶ S) [AlgebraicGeometry.Etale b] (v : V' ⟶ V)
    (sq : IsPullback v g' g b) (s' : S' ⟶ V') (hsection : s' ≫ v = b ≫ s),
    (Etale.scalarPullbackIso φ b).inv.app (Etale.sectionInvariant A g s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map (sectionMap φ g s) ≫
        Etale.NoetherianSectionSpecialization.sectionMap B g g' b v sq s s' hsection =
      (Etale.scalarExtension φ S').map
          (Etale.NoetherianSectionSpecialization.sectionMap A g g' b v sq s s' hsection) ≫
        sectionMap φ g' s'

/-- The direct constant-family coordinate comparison. After restriction to any etale
base chart on which the family has a constant model, the normalized global comparison
is the identity on that model, read through its value at one.
Source: Proof (2), Step 6 (blueprint: lem-pur-dnc-coefficient-transport). -/
def CoordinateNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne A g s hs))
    (κ : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s)) : Prop :=
  ∀ {S' : Scheme.{u}} (b : S' ⟶ S) [AlgebraicGeometry.Etale b]
    [IsSeparated b] [QuasiCompact b] (C0 : Etale.DerivedCategoryModule A S')
    (e : (Etale.upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        (Etale.NoetherianSectionSpecialization.family A g s) ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj C0),
    (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.map κ.hom ≫
      (Etale.NoetherianSectionSpecialization.linePullback A b
        (Etale.sectionInvariant A g s)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (Etale.sectionRestrictionIso (ModuleCat.{u + 1} A) b
            (AffineSpace.map (ULift.{u} (Fin 1)) b)
            (AffineSpace.oneSection_comp_map b)
            (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S')
            (@asIso _ _ _ _ (Etale.NoetherianSectionSpecialization.atOne A g s hs) h1)
            e).hom = e.hom

/-- The normalized B-family comparison and its specialization equation, with uniqueness
among all normalized isomorphisms, not just among coefficient-compatible choices.
Source: Proof (2), Steps 4--7 (blueprint: lem-pur-dnc-coefficient-transport). -/
def NormalizedTransport {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ∀ κR : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s),
    Etale.NoetherianSectionSpecialization.Normalized A g s hs κR →
    ∃ κB : Etale.NoetherianSectionSpecialization.family B g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} B)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant B g s),
      Etale.NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      (∀ κ, Etale.NoetherianSectionSpecialization.Normalized B g s hs κ → κ = κB) ∧
      (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection ≫ κB.hom =
        (Etale.scalarExtension φ (AffineSpace (ULift.{u} (Fin 1)) S)).map κR.hom ≫
          (Etale.scalarPullbackIso φ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).inv.app _ ≫
          (Etale.upperStar (ModuleCat.{u + 1} B)
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map (sectionMap φ g s)) ∧
      (∀ h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne B g s hs),
        CoordinateNormalization B g s hs h1 κB) ∧
      IsIso (Etale.NoetherianSectionSpecialization.specialization B g s κB) ∧
      (sectionMap φ g s ≫ Etale.NoetherianSectionSpecialization.specialization B g s κB =
        (Etale.scalarExtension φ S).map
            (Etale.NoetherianSectionSpecialization.specialization A g s κR) ≫
          sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Arbitrary-base-change coefficient square, without imposing any section on g0.
All morphisms remain in the separated finite-type k-setting.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def MixedBaseChange (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) : Prop :=
  ∀ (V S S' : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S'.hom] [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom]
    (g : V ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r g.left]
    [HasCompactification g.left] [QuasiCompact g.left] (h : S' ⟶ S),
    IsIso (Etale.smoothDualizingBaseChangeMap A g.left h.left) ∧
      IsIso (Etale.smoothDualizingBaseChangeMap B g.left h.left) ∧
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g.left h.left (𝟙_ _)

/-- The counit-normalized chart equation, including the standard coordinate pair.
The right-adjoint comparisons are fixed by etale summation and ordered affine trace;
the model coefficient map is the canonical root-normalized Tate reassociation.
Source: Proof (2), Step 3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def ChartCompatibility (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) : Prop :=
  ∀ (V S : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsNoetherian V.left] [IsNoetherian S.left]
    (g : V ⟶ S) [HasCompactification g.left] (d : ℕ)
    [SmoothOfRelativeDimension d g.left]
    {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V.left) [IsOpenImmersion i]
    (e : U ⟶ affineTraceTower S.left d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g.left = e ≫ affineTraceProjection S.left d)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hS : IsUnit (N : Γ(S.left, ⊤))),
    (Etale.scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g.left i d e he
          (HasCompactification.compactification g.left)
          (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g.left)
          (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g.left)
          N hA tA PA hS).hom.app (𝟙_ _)) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
      (Etale.affineTraceRight B N hB S.left d ⋙ Etale.ordinaryFinitePullback B e).map
        (Etale.ExceptionalCoefficients.unitIso φ S.left).hom =
    (Etale.scalarPullbackIso φ i).inv.app
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) g.left) ≫
      (Etale.ordinaryFinitePullback B i).map (dualizingMap φ g.left) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g.left i d e he
        (HasCompactification.compactification g.left)
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g.left)
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g.left)
        N hB tB PB hS).hom.app (𝟙_ _)

/-- Geometric domain facts for the actual Rees family and its actual normal cone.
These are proof data only; no replacement deformation space is selected.
Source: sk-lem-geometry, Proof (2) Step 1
(blueprint: lem-pur-dnc-coefficient-transport). -/
structure Geometry {V S : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V) : Prop where
  compact : HasCompactification g
  compactFamily : HasCompactification (Scheme.Hom.deformationSpaceProj g s)
  compactNormal : HasCompactification (Scheme.Hom.normalConeProj g s)
  quasiCompactNormal : QuasiCompact (Scheme.Hom.normalConeProj g s)

/-- The domain facts follow from the source hypotheses, rather than being additional
hypotheses of the coefficient theorem.
Source: Proof (2) Step 1, sk-lem-geometry (blueprint: lem-pur-dnc-coefficient-transport).
Proof: finite type over the field makes S and V Noetherian. A closed section of a
smooth relative-dimension d map is regular of codimension d. On its extended-Rees
charts x_i=t*u_i the deformation projection is smooth of dimension d; its zero
fibre is the actual rank-d normal bundle. The projections are separated finite type,
and Nagata gives the three coefficient-independent compactifications. -/
theorem geometry (D : FiniteFieldDatum.{u}) {V S : Scheme.{u}}
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of D.k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) : Geometry g s := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have := SmoothOfRelativeDimension.smooth d g
  have : HasCompactification g := (NagataCompactification g).hasCompactification
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  exact ⟨inferInstance, Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs,
    (NagataCompactification (Scheme.Hom.normalConeProj g s)).hasCompactification,
    inferInstance⟩

/-- The complete finite coefficient transport assertion in canonical coordinates.
Source: Proof (2), all clauses (blueprint: lem-pur-dnc-coefficient-transport). -/
def Assertions (D : FiniteFieldDatum.{u}) (ell n : ℕ) [Fact ell.Prime]
    {V S : Scheme.{u}} (g : V ⟶ S) [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (G : Geometry g s) {B : Type u} [CommRing B] [Finite B]
    (φ : BaseRing.{u} ell n →+* B) : Prop := by
  letI := G.compact
  letI := G.compactFamily
  letI := G.compactNormal
  letI := G.quasiCompactNormal
  exact
    IsIso (realizedSectionMap φ g s) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.normalConeProj g s)
      s.normalConeZeroSection) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne (ULift.{u + 1, u} B) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero (ULift.{u + 1, u} B) g s) ∧
    (∃! κR : Etale.NoetherianSectionSpecialization.family
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (BaseRing.{u} ell n)))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s),
      Etale.NoetherianSectionSpecialization.Normalized
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs κR) ∧
    FibreCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs ∧
    LocalizationCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s ∧
    MixedBaseChange D (RingHom.ulift.{u + 1, u + 1, u, u} φ) ∧
    ChartCompatibility D (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n) ∧
    NormalizedTransport (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs

end DncCoefficientTransport
```

## New

The original module publicly imports Sheaf.SecSmoothPurity.DncCoefficientTransportData.
Its geometry theorem remains where it was. The new data module contains:

```lean
namespace DncCoefficientTransport

/-- The coefficient ring Z/(ell^n), lifted only for size.
Source: Proof (2), R=Z/ell^n (blueprint: lem-pur-dnc-coefficient-transport). -/
abbrev BaseRing (ell n : ℕ) : Type u := ULift.{u} (ZMod (ell ^ n))

/-- The positive prime-power coefficient ring is finite, including n=0.
Source: Proof (2), finite coefficient convention
(blueprint: lem-pur-dnc-coefficient-transport). -/
instance baseRingFinite (ell n : ℕ) [Fact ell.Prime] : Finite (BaseRing.{u} ell n) :=
  letI : NeZero (ell ^ n) := ⟨ne_of_gt (pow_pos (Fact.out : ell.Prime).pos n)⟩
  inferInstance

/-- The canonical coefficient map on relative dualizing objects: transpose the
scalar-extended counit, then identify the extended unit with the B-unit.
Source: Proof (2), Step 1; det-sp-reduction-exceptional
(blueprint: lem-pur-dnc-coefficient-transport). -/
def dualizingMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] :
    (Etale.scalarExtension φ V).obj (Etale.dualizingComplex (ModuleCat.{u + 1} A) g) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} B) g :=
  Etale.ExceptionalCoefficients.mateMap φ g (𝟙_ _) ≫
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g).map
      (Etale.ExceptionalCoefficients.unitIso φ S).hom

/-- The actual section coefficient map: balancing for Ls* followed by Ls*(c_g).
Source: Proof (2), Step 1 (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (Etale.scalarExtension φ S).obj (Etale.sectionInvariant A g s) ⟶
      Etale.sectionInvariant B g s :=
  (Etale.scalarPullbackIso φ s).inv.app _ ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) s).leftDerivedFunctor.map (dualizingMap φ g)

/-- The genuine B-coefficient section object in the uncompleted pro-etale category.
This is the canonical site realization of Ls* g_B^! B_S, formed using g_B^!.
Source: Proof (2), definition of C_D (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionObject (A : Type u) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) :
    proEtaleDerivedCategory S A :=
  (ProEtale.reductionSite A S).obj (Etale.sectionInvariant (ULift.{u + 1, u} A) g s)

/-- The actual pro-etale coefficient map, with the fixed site/scalar comparison.
Source: Proof (2), q_(g,s) (blueprint: lem-pur-dnc-coefficient-transport). -/
def realizedSectionMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (ProEtale.scalarExtensionFunctor φ S).obj (sectionObject A g s) ⟶
      sectionObject B g s :=
  (ProEtale.reductionSiteScalarIso φ S).hom.app _ ≫
    (ProEtale.reductionSite B S).map (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s)

/-- Scalar compatibility with both canonical exceptional fibre mates of the Rees family.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def FibreCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ((Etale.scalarPullbackIso φ (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atOne B g s hs =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atOne A g s hs) ≫
      sectionMap φ g s) ∧
  ((Etale.scalarPullbackIso φ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atZero B g s =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atZero A g s) ≫
      sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Naturality for etale localization of pairs, using the specified exceptional mate.
Source: Proof (2), Steps 2--3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def LocalizationCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) : Prop :=
  ∀ {V' S' : Scheme.{u}} (g' : V' ⟶ S') [HasCompactification g'] [QuasiCompact g']
    (b : S' ⟶ S) [AlgebraicGeometry.Etale b] (v : V' ⟶ V)
    (sq : IsPullback v g' g b) (s' : S' ⟶ V') (hsection : s' ≫ v = b ≫ s),
    (Etale.scalarPullbackIso φ b).inv.app (Etale.sectionInvariant A g s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map (sectionMap φ g s) ≫
        Etale.NoetherianSectionSpecialization.sectionMap B g g' b v sq s s' hsection =
      (Etale.scalarExtension φ S').map
          (Etale.NoetherianSectionSpecialization.sectionMap A g g' b v sq s s' hsection) ≫
        sectionMap φ g' s'

/-- The direct constant-family coordinate comparison. After restriction to any etale
base chart on which the family has a constant model, the normalized global comparison
is the identity on that model, read through its value at one.
Source: Proof (2), Step 6 (blueprint: lem-pur-dnc-coefficient-transport). -/
def CoordinateNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne A g s hs))
    (κ : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s)) : Prop :=
  ∀ {S' : Scheme.{u}} (b : S' ⟶ S) [AlgebraicGeometry.Etale b]
    [IsSeparated b] [QuasiCompact b] (C0 : Etale.DerivedCategoryModule A S')
    (e : (Etale.upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        (Etale.NoetherianSectionSpecialization.family A g s) ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj C0),
    (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.map κ.hom ≫
      (Etale.NoetherianSectionSpecialization.linePullback A b
        (Etale.sectionInvariant A g s)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (Etale.sectionRestrictionIso (ModuleCat.{u + 1} A) b
            (AffineSpace.map (ULift.{u} (Fin 1)) b)
            (AffineSpace.oneSection_comp_map b)
            (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S')
            (@asIso _ _ _ _ (Etale.NoetherianSectionSpecialization.atOne A g s hs) h1)
            e).hom = e.hom

/-- The normalized B-family comparison and its specialization equation, with uniqueness
among all normalized isomorphisms, not just among coefficient-compatible choices.
Source: Proof (2), Steps 4--7 (blueprint: lem-pur-dnc-coefficient-transport). -/
def NormalizedTransport {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ∀ κR : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s),
    Etale.NoetherianSectionSpecialization.Normalized A g s hs κR →
    ∃ κB : Etale.NoetherianSectionSpecialization.family B g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} B)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant B g s),
      Etale.NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      (∀ κ, Etale.NoetherianSectionSpecialization.Normalized B g s hs κ → κ = κB) ∧
      (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection ≫ κB.hom =
        (Etale.scalarExtension φ (AffineSpace (ULift.{u} (Fin 1)) S)).map κR.hom ≫
          (Etale.scalarPullbackIso φ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).inv.app _ ≫
          (Etale.upperStar (ModuleCat.{u + 1} B)
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map (sectionMap φ g s)) ∧
      (∀ h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne B g s hs),
        CoordinateNormalization B g s hs h1 κB) ∧
      IsIso (Etale.NoetherianSectionSpecialization.specialization B g s κB) ∧
      (sectionMap φ g s ≫ Etale.NoetherianSectionSpecialization.specialization B g s κB =
        (Etale.scalarExtension φ S).map
            (Etale.NoetherianSectionSpecialization.specialization A g s κR) ≫
          sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Arbitrary-base-change coefficient square, without imposing any section on g0.
All morphisms remain in the separated finite-type k-setting.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def MixedBaseChange (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) : Prop :=
  ∀ (V S S' : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S'.hom] [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom]
    (g : V ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r g.left]
    [HasCompactification g.left] [QuasiCompact g.left] (h : S' ⟶ S),
    IsIso (Etale.smoothDualizingBaseChangeMap A g.left h.left) ∧
      IsIso (Etale.smoothDualizingBaseChangeMap B g.left h.left) ∧
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g.left h.left (𝟙_ _)

/-- The counit-normalized chart equation, including the standard coordinate pair.
The right-adjoint comparisons are fixed by etale summation and ordered affine trace;
the model coefficient map is the canonical root-normalized Tate reassociation.
Source: Proof (2), Step 3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def ChartCompatibility (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) : Prop :=
  ∀ (V S : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsNoetherian V.left] [IsNoetherian S.left]
    (g : V ⟶ S) [HasCompactification g.left] (d : ℕ)
    [SmoothOfRelativeDimension d g.left]
    {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V.left) [IsOpenImmersion i]
    (e : U ⟶ affineTraceTower S.left d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g.left = e ≫ affineTraceProjection S.left d)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hS : IsUnit (N : Γ(S.left, ⊤))),
    (Etale.scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g.left i d e he
          (HasCompactification.compactification g.left)
          (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g.left)
          (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g.left)
          N hA tA PA hS).hom.app (𝟙_ _)) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
      (Etale.affineTraceRight B N hB S.left d ⋙ Etale.ordinaryFinitePullback B e).map
        (Etale.ExceptionalCoefficients.unitIso φ S.left).hom =
    (Etale.scalarPullbackIso φ i).inv.app
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) g.left) ≫
      (Etale.ordinaryFinitePullback B i).map (dualizingMap φ g.left) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g.left i d e he
        (HasCompactification.compactification g.left)
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g.left)
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g.left)
        N hB tB PB hS).hom.app (𝟙_ _)

/-- Geometric domain facts for the actual Rees family and its actual normal cone.
These are proof data only; no replacement deformation space is selected.
Source: sk-lem-geometry, Proof (2) Step 1
(blueprint: lem-pur-dnc-coefficient-transport). -/
structure Geometry {V S : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V) : Prop where
  compact : HasCompactification g
  compactFamily : HasCompactification (Scheme.Hom.deformationSpaceProj g s)
  compactNormal : HasCompactification (Scheme.Hom.normalConeProj g s)
  quasiCompactNormal : QuasiCompact (Scheme.Hom.normalConeProj g s)

/-- The complete finite coefficient transport assertion in canonical coordinates.
Source: Proof (2), all clauses (blueprint: lem-pur-dnc-coefficient-transport). -/
def Assertions (D : FiniteFieldDatum.{u}) (ell n : ℕ) [Fact ell.Prime]
    {V S : Scheme.{u}} (g : V ⟶ S) [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (G : Geometry g s) {B : Type u} [CommRing B] [Finite B]
    (φ : BaseRing.{u} ell n →+* B) : Prop := by
  letI := G.compact
  letI := G.compactFamily
  letI := G.compactNormal
  letI := G.quasiCompactNormal
  exact
    IsIso (realizedSectionMap φ g s) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.normalConeProj g s)
      s.normalConeZeroSection) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne (ULift.{u + 1, u} B) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero (ULift.{u + 1, u} B) g s) ∧
    (∃! κR : Etale.NoetherianSectionSpecialization.family
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (BaseRing.{u} ell n)))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s),
      Etale.NoetherianSectionSpecialization.Normalized
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs κR) ∧
    FibreCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs ∧
    LocalizationCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s ∧
    MixedBaseChange D (RingHom.ulift.{u + 1, u + 1, u, u} φ) ∧
    ChartCompatibility D (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n) ∧
    NormalizedTransport (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs

end DncCoefficientTransport
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | P2 | Public reexport; unchanged geometry and theorem signatures. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicNormalizedPurityLift | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicPurityScalarNaturality | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceConstruction | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.FiniteReductionOfPurity | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.PurAdicReconstruction | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalExceptionalFinalEquations | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalPurityCoherenceDescent | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalPurityComparisonDescent | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalPurityScalarLocalization | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalPuritySourceLocalization | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalScalarComparisonData | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.RationalScalarComparisonIdentification | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackPbcPullback | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackPbcTwist | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackScalarShifts | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackSquareMaps | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackSquareScalars | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | Not adapted; claim immaterial | Identical public declarations and data through original reexport; no edit. |

## Status

landed 20261026T002119-L-58326 2026-10-26 (merge of deliver/P2/Sheaf.SecSmoothPurity.PurityDncCoefficientTransport)
