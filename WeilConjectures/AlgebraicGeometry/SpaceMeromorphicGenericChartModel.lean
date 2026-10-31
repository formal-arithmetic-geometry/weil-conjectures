/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceDivisorDefinitions
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.MeromorphicModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.CategoryTheory.Limits.Final.Type
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen
import WeilConjectures.AlgebraicGeometry.InvertibleModuleGenericStalk
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions

/-! # Meromorphic sections on regular algebraic spaces

Source: Stacks Project, Spaces Divisors, Tags 0EN3, 0EN6, 0EN7 and 0ENA;
Properties, Tag 033M; Properties of Spaces, Tag 0BGT
(blueprint: lem-sfb-space-meromorphic-generic-chart-model).

The meromorphic module is transported from the existing small affine basis. Generic
fields are the actual local rings in a dense schematic open, with their canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The underlying O-module of the existing scalar extension on the affine basis.
Source: Stacks, Tags 0EN3 and 0EN7
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicSmallModule (X : AlgebraicSpace S) (M : X.Modules) : X.SmallModules :=
  (SheafOfModules.pushforward (F := 𝟭 X.SmallEtaleModel)
    (spaceToTotalFractions X)).obj
      ((spaceMeromorphicLocalization X).obj (X.smallModuleRestriction.obj M))

/-- The same meromorphic module on the original small étale site, using the fixed
restriction equivalence, not a second localization construction.
Source: Stacks, Tags 0EN3 and 0EN7
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicSpaceModule (X : AlgebraicSpace S) (M : X.Modules) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj (meromorphicSmallModule X M)

/-- The canonical map m ↦ m/1, transported with the fixed equivalence unit.
Source: Stacks, Tags 0EN3 and 0EN7
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def toMeromorphicSpaceModule (X : AlgebraicSpace S) (M : X.Modules) :
    M ⟶ meromorphicSpaceModule X M :=
  X.smallModuleEquivalence.unitIso.hom.app M ≫
    X.smallModuleEquivalence.inverse.map
      ((SheafOfModules.pullbackPushforwardAdjunction
        (F := 𝟭 X.SmallEtaleModel) (S := X.smallStructureRings)
        (R := spaceTotalFractionRings X) (spaceToTotalFractions X)).unit.app
          (X.smallModuleRestriction.obj M))

/-- Charts contained in a subset of the underlying point space. For an open subset,
this is precisely its small étale site expressed as a full subcategory of X_et.
Source: Stacks, Tag 03BZ and 0ENA
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicOpenCharts (X : AlgebraicSpace S) (W : Set (Point X.obj.obj)) :=
  ObjectProperty.FullSubcategory (fun T : X.EtaleSite ↦
    ∀ y : X.etaleForget.obj T, schemePointMap T.obj.hom y ∈ W)

/-- Restrict compatible global sections to all charts contained in the open.
Source: Stacks, Tag 0ENA
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicOpenRestriction (X : AlgebraicSpace S) (M : X.Modules)
    (W : Set (Point X.obj.obj)) : M.sections →
      ((ObjectProperty.ι (fun T : X.EtaleSite ↦
        ∀ y : X.etaleForget.obj T, schemePointMap T.obj.hom y ∈ W)).op ⋙
          M.val.presheaf ⋙ forget AddCommGrpCat).sections :=
  Functor.sectionsPrecomp _

/-- The canonical map from the spectrum of a chart local ring to the space.
Source: Stacks, Tag 0ENA; Schemes, canonical local spectrum
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicLocalSpectrum (X : AlgebraicSpace S) (T : X.EtaleSite)
    (x : X.etaleForget.obj T) : Over S :=
  Over.mk ((X.etaleForget.obj T).fromSpecStalk x ≫ T.obj.left.hom)

/-- The generic-point inclusion uses fromSpecStalk followed by the given schematic open.
Source: Stacks, Tag 0ENA
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicGenericInclusion (X : AlgebraicSpace S) (T : X.EtaleSite)
    (x : X.etaleForget.obj T) : schemeSpace (meromorphicLocalSpectrum X T x) ⟶ X :=
  ObjectProperty.homMk ⟨yoneda.map
    (Over.homMk ((X.etaleForget.obj T).fromSpecStalk x) rfl) ≫ T.obj.hom⟩

/-- The generic factor of a line: direct image of its actual tensor pullback to
Spec O_(X,eta). Its adjunction unit fixes its identification with the generic stalk.
Source: Stacks, Tag 0ENA
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicGenericFactor (X : AlgebraicSpace S) (T : X.EtaleSite)
    (x : X.etaleForget.obj T) (M : X.Modules) : X.Modules :=
  (moduleDirectImage (meromorphicGenericInclusion X T x)).obj
    ((moduleTensorPullback (meromorphicGenericInclusion X T x)).obj M)

/-- A regular global section has its usual germ in the ordinary chart module.
The chart of the top open is the canonical open subscheme, so its scalar transport
is exactly schemeOpensRingHom, already used by schemeRestriction.
Source: Stacks, Tags 03FH and 0ENA
(blueprint: lem-sfb-space-meromorphic-generic-chart-model). -/
def meromorphicRegularGerm (X : AlgebraicSpace S) (T : X.EtaleSite)
    (M : X.Modules) (x : X.etaleForget.obj T) (s : M.sections) :
    ((X.schemeRestriction T).obj M).presheaf.stalk x :=
  ((X.schemeRestriction T).obj M).presheaf.germ ⊤ x trivial
    (s.val (op ((schemeOpens X T).obj ⊤)))

/-- The regular-space meromorphic model, with canonical normalization of the sheaf
products by the adjunction units. The schematic open contains every generic point;
its local rings and ordinary line stalks specify the fields and one-dimensional fibres.
The affine comparison is the actual sheafification map, and the ordinary chart comparison
is normalized by m ↦ m/1. Both use all charts, including the empty chart.

Source: Stacks, Tags 0EN3, 0EN6, 0EN7, 0ENA, 0BGT and 033M
(blueprint: lem-sfb-space-meromorphic-generic-chart-model).

Proof:
1. Apply rem-pc-regular-normal to every regular chart. It is reduced and normal;
   each Noetherian chart is the finite disjoint union of its clopen integral components.
   Affine localizations identify a connected nonempty chart ring with a normal domain.
2. Use lem-sfb-noetherian-space-topology, finite irreducible components, sobriety and
   lem-sfb-quasiseparated-space-dense-scheme-open. Every generic point belongs to the
   dense scheme open. Its local ring is a field by the integral function-field lemma;
   lem-sc-invertible-module-generic-stalk gives rank one for line stalks.
3. The specialization lifting and noncollapse lemma identifies chart generic points
   with points over the generic points of X. Local-spectrum base change identifies
   their local rings; étale field fibres are disjoint unions of their field spectra.
4. On affine charts glue Q(A) using lem-sfb-etale-total-fraction-base-change and
   lem-sfb-space-qcoh-cartesian-chart-family. Restrictions send a/s to f(a)/f(s), and
   satisfy the identity and cocycle equations. Affine opens form a basis.
5. The regular denominators are exactly the non-zero-divisors on affine charts.
   Therefore this glued sheaf has the sheafification universal property of 0EN3.
   Ordinary-to-étale quasi-coherent comparison identifies its scheme restrictions
   with def-sc-meromorphic-module; tensoring a local line frame gives the twist.
   All these maps preserve fractions and local frames, hence commute with further
   étale restrictions (lem-trf-scheme-etale-invertible-comparison).
6. Étale base change computes the generic direct images on a chart. The reduced
   Noetherian total-fraction decomposition identifies Q(A) with the product of the
   generic local rings. The maps are the canonical localization maps, so they glue.
   Trivializing the line and changing frames yields its generic product and the
   global-section product with the same germ normalization.
7. Localization at non-zero-divisors is injective. A line frame gives the same
   assertion for L. Every dense open contains every generic point, so restriction
   on meromorphic sections is the identity on the generic product and is bijective.
   The injective map into that product gives injectivity for regular line sections. -/
theorem space_meromorphic_generic_chart_model
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (hX : IsRegularNoetherianSeparated X) :
    (∀ T : X.EtaleSite,
      IsReduced (X.etaleForget.obj T) ∧
        ∀ x : X.etaleForget.obj T,
          IsDomain ((X.etaleForget.obj T).presheaf.stalk x) ∧
            IsIntegrallyClosed ((X.etaleForget.obj T).presheaf.stalk x)) ∧
    (∀ T : X.EtaleSite, IsNoetherian (X.etaleForget.obj T) →
      ∃ (n : ℕ) (U : Fin n → (X.etaleForget.obj T).Opens),
        Set.range (fun i : Fin n ↦ (U i : Set (X.etaleForget.obj T))) =
          irreducibleComponents (X.etaleForget.obj T) ∧
        (∀ i : Fin n, IsClosed (U i : Set (X.etaleForget.obj T))) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)) ∧
        (⨆ i : Fin n, U i) = ⊤ ∧
        (∀ i : Fin n, IsIntegral (U i).toScheme ∧ IsRegularScheme (U i).toScheme ∧
          ∀ x : (U i).toScheme,
            IsDomain ((U i).toScheme.presheaf.stalk x) ∧
              IsIntegrallyClosed ((U i).toScheme.presheaf.stalk x)) ∧
        Nonempty (IsColimit (Cofan.mk (X.etaleForget.obj T)
          (fun i : Fin n ↦ (U i).ι)))) ∧
    (∀ T : X.EtaleSite, IsAffine (X.etaleForget.obj T) →
      Nonempty (X.etaleForget.obj T) → PreconnectedSpace (X.etaleForget.obj T) →
        IsNoetherianRing Γ(X.etaleForget.obj T, ⊤) ∧
          IsDomain Γ(X.etaleForget.obj T, ⊤) ∧
            IsIntegrallyClosed Γ(X.etaleForget.obj T, ⊤)) ∧
    (genericPoints (Point X.obj.obj)).Finite ∧
    (∀ Z : Set (Point X.obj.obj), Z ∈ irreducibleComponents (Point X.obj.obj) →
      ∃! η : Point X.obj.obj, IsGenericPoint η Z) ∧
    (∀ U : X.SmallEtaleModel,
      IsIso ((toSheafify X.smallEtaleModelTopology
        (spaceTotalFractionPresheaf X)).app (op U))) ∧
    (∀ (L : X.Modules), X.IsLineModule L → Mono (toMeromorphicSpaceModule X L)) ∧
    Mono (spaceToTotalFractions X) ∧
    (∀ (L : X.Modules), X.IsLineModule L →
      (∀ (W : Set (Point X.obj.obj)), IsOpen W → Dense W →
        Function.Bijective (meromorphicOpenRestriction X (meromorphicSpaceModule X L) W) ∧
          Function.Injective (meromorphicOpenRestriction X L W)) ∧
      ∃ c : ∀ T : X.EtaleSite,
          (X.schemeRestriction T).obj (meromorphicSpaceModule X L) ≅
            Scheme.Modules.meromorphicModule (X.etaleForget.obj T)
              ((X.schemeRestriction T).obj L),
        (∀ T : X.EtaleSite,
          (X.schemeRestriction T).map (toMeromorphicSpaceModule X L) ≫ (c T).hom =
            Scheme.Modules.toMeromorphicModule (X.etaleForget.obj T)
              ((X.schemeRestriction T).obj L)) ∧
        ∀ (T U : X.EtaleSite) (f : T ⟶ U) (W : (X.etaleForget.obj U).Opens)
          (a : (schemeOpens X T).obj ((X.etaleForget.map f) ⁻¹ᵁ W) ⟶
            (schemeOpens X U).obj W),
          X.etaleForget.map a = (X.etaleForget.map f) ∣_ W →
          ∀ (m : Γ((X.schemeRestriction U).obj L, W))
            (b : Scheme.Modules.meromorphicDenominators (X.etaleForget.obj U) W)
            (d : Scheme.Modules.meromorphicDenominators (X.etaleForget.obj T)
              ((X.etaleForget.map f) ⁻¹ᵁ W)),
            d.val = (X.etaleForget.map f).app W b.val →
            (c T).hom.app ((X.etaleForget.map f) ⁻¹ᵁ W)
              ((meromorphicSpaceModule X L).val.map a.op
                ((c U).inv.app W
                  (Scheme.Modules.meromorphicFraction (X.etaleForget.obj U)
                    ((X.schemeRestriction U).obj L) W (LocalizedModule.mk m b)))) =
              Scheme.Modules.meromorphicFraction (X.etaleForget.obj T)
                ((X.schemeRestriction T).obj L) ((X.etaleForget.map f) ⁻¹ᵁ W)
                  (LocalizedModule.mk (L.val.map a.op m) d)) ∧
    ∃ T : X.EtaleSite,
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) T.obj.hom ∧
      Topology.IsOpenEmbedding (schemePointMap T.obj.hom) ∧
      DenseRange (schemePointMap T.obj.hom) ∧
      schemePointMap T.obj.hom '' genericPoints (X.etaleForget.obj T) =
        genericPoints (Point X.obj.obj) ∧
      (∀ x : X.etaleForget.obj T, x ∈ genericPoints (X.etaleForget.obj T) →
        IsField ((X.etaleForget.obj T).presheaf.stalk x)) ∧
      (∃ e : meromorphicSpaceModule X (SheafOfModules.unit X.structureSheaf) ≅
          ∏ᶜ (fun η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)} ↦
            (moduleDirectImage (meromorphicGenericInclusion X T η.val)).obj
              (SheafOfModules.unit (schemeSpace
                (meromorphicLocalSpectrum X T η.val)).structureSheaf)),
        ∀ η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)},
          toMeromorphicSpaceModule X (SheafOfModules.unit X.structureSheaf) ≫
            e.hom ≫ Pi.π _ η = moduleStructureMap (meromorphicGenericInclusion X T η.val)) ∧
      ∀ (L : X.Modules), X.IsLineModule L →
        (∀ η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)},
          Module.finrank ((X.etaleForget.obj T).presheaf.stalk η.val)
            (((X.schemeRestriction T).obj L).presheaf.stalk η.val) = 1) ∧
        (∃ e : meromorphicSpaceModule X L ≅
            ∏ᶜ (fun η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)} ↦
              meromorphicGenericFactor X T η.val L),
          ∀ η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)},
            toMeromorphicSpaceModule X L ≫ e.hom ≫ Pi.π _ η =
              (moduleTensorAdjunction (meromorphicGenericInclusion X T η.val)).unit.app L) ∧
        ∃ g : (meromorphicSpaceModule X L).sections ≃
            (∀ η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)},
              ((X.schemeRestriction T).obj L).presheaf.stalk η.val),
          (∀ (s : L.sections)
            (η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)}),
            g (SheafOfModules.sectionsMap (toMeromorphicSpaceModule X L) s) η =
              meromorphicRegularGerm X T L η.val s) ∧
          ∀ (s : (meromorphicSpaceModule X L).sections)
            (η : {x : X.etaleForget.obj T // x ∈ genericPoints (X.etaleForget.obj T)})
            (W : (X.etaleForget.obj T).Opens) (hη : η.val ∈ W)
            (a : Γ(X.etaleForget.obj T, W)) (m : Γ((X.schemeRestriction T).obj L, W)),
            (toMeromorphicSpaceModule X L).val.app (op ((schemeOpens X T).obj W)) m =
              (schemeOpensRingHom X T).app (op W) a •
                @id ((meromorphicSpaceModule X L).val.obj (op ((schemeOpens X T).obj W)))
                  (s.val (op ((schemeOpens X T).obj W))) →
            ((X.schemeRestriction T).obj L).presheaf.germ W η.val hη m =
              (X.etaleForget.obj T).presheaf.germ W η.val hη a • g s η := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
