/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizedTopChern
public import Sheaf.Paper.PurityVectorBundleZeroSection
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ProjectiveBundleFormula
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Sheaf.Paper.FiniteDirectImageComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
import Sheaf.Paper.KummerAdditivity
import Sheaf.Paper.PurityFiniteSetting
import Sheaf.Paper.SupportedCup
import Sheaf.Paper.SupportedCupFunctoriality

/-!
# Thom classes of vector bundles

Source: blueprint main-20261015, `sec-smooth-purity/sk-prop-an`, definition
`def-pur-vector-bundle-thom-class` (blueprint: def-pur-vector-bundle-thom-class).

The bundle is Spec Sym(M), its vectors are M dual, and the tautological section is
specified by the actual degree-one generators. The supported class uses the existing
localized Chern family. Compact support uses the canonical origin compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace WeilConjectures.PurityFiniteSetting

variable {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
  {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

/-- The module of vectors is the ordinary sheaf dual of the symmetric-algebra generators.
Source: blueprint definition, dual convention (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleVectors (V : PurityVectorBundle P B hB r) : B.Modules :=
  Scheme.Modules.dual V.𝓔

/-- The tautological section takes values in the tensor pullback of M dual.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleTautologicalModule (V : PurityVectorBundle P B hB r) : V.E.Modules :=
  (Scheme.Modules.tensorPullback V.p).obj (vectorBundleVectors V)

/-- Dualization and tensor pullback preserve the rank, including zero.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: on a frame M=O^r its dual is O^r and tensor pullback is O^r; these opens cover E. -/
theorem vectorBundleTautologicalModule_rank (V : PurityVectorBundle P B hB r) :
    (vectorBundleTautologicalModule V).IsFiniteLocallyFreeOfRank r := by
  sorry

attribute [instance] vectorBundleTautologicalModule_rank

/-- A frame vector on an open, using the literal free-module inclusion.
Source: blueprint coordinate verification (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleFrameVector (M : B.Modules) (U : B.Opens)
    (e : M.over U ≅ SheafOfModules.free
      (R := B.ringCatSheaf.over U) (ULift.{u} (Fin r))) (i : Fin r) :
    M.val.obj (op U) :=
  e.inv.val.app (op (Over.mk (𝟙 U)))
    ((SheafOfModules.ιFree (R := B.ringCatSheaf.over U) (ULift.up i)).val.app
      (op (Over.mk (𝟙 U))) (1 : B.presheaf.obj (op U)))

/-- A degree-one generator on the canonical total space, transported through phi.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleGenerator (V : PurityVectorBundle P B hB r)
    (U : B.Opens) (m : V.𝓔.val.obj (op U)) : V.E.presheaf.obj (op (V.p ⁻¹ᵁ U)) :=
  V.E.presheaf.map (eqToHom (congrArg (fun f ↦ op (f ⁻¹ᵁ U)) V.over_commutes))
    (V.phi.hom.c.app (op ((@VectorBundleZeroSection.π B
      (isNoetherian_of_locallyOfFiniteType hB) r V.𝓔 V.locallyFree) ⁻¹ᵁ U))
      ((@VectorBundleZeroSection.algebraIso B (isNoetherian_of_locallyOfFiniteType hB)
        r V.𝓔 V.locallyFree).hom.right.hom.app (op U)
          ((SymmetricAlgebraSheaf.inclusion V.𝓔).val.app (op U) m)))

/-- In every affine frame the section is sum x_i e_i dual, with x_i the actual
symmetric-algebra generators. This fixes the section, without a regularity hypothesis.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def VectorBundleTautologicalSectionSpec (V : PurityVectorBundle P B hB r)
    (s : (vectorBundleTautologicalModule V).sections) : Prop :=
  ∀ (U : B.affineOpens) (e : V.𝓔.over U.1 ≅ SheafOfModules.free
      (R := B.ringCatSheaf.over U.1) (ULift.{u} (Fin r))),
    s.val (op (V.p ⁻¹ᵁ U.1)) = ∑ i : Fin r,
      vectorBundleGenerator V U.1 (vectorBundleFrameVector V.𝓔 U.1 e i) •
        Scheme.Modules.tensorPullbackSection V.p (vectorBundleVectors V) U.1
          (vectorBundleFrameVector (vectorBundleVectors V) U.1
            (regularSectionDualFrame V.𝓔 r U.1 e) i)

/-- The coordinate prescription glues to exactly one global section.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: on a trivializing affine write sum x_i e_i dual. A frame change e'=eG
changes x to G transpose x and the dual frame by G inverse transpose. The sums
therefore agree on overlaps and glue. Their values on the covering opens determine
any global section uniquely. The empty sum handles rank zero and empty opens. -/
theorem vectorBundleTautologicalSection_existsUnique (V : PurityVectorBundle P B hB r) :
    ∃! s : (vectorBundleTautologicalModule V).sections,
      VectorBundleTautologicalSectionSpec V s := by
  sorry

/-- The actual tautological section, chosen only from its unique generator prescription.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleTautologicalSection (V : PurityVectorBundle P B hB r) :
    (vectorBundleTautologicalModule V).sections :=
  (vectorBundleTautologicalSection_existsUnique V).choose

/-- The total space has the finite-type domain needed by the localized Chern construction.
Source: blueprint proof Step 2 (blueprint: def-pur-vector-bundle-thom-class).
Proof: relative Spec makes pi affine, hence separated and quasi-compact. On frames
its ring is a polynomial algebra on r generators, hence finite type over the base.
Compose these properties with those of hB. The zero section is closed by its augmentation. -/
theorem vectorBundleThom_geometry (V : PurityVectorBundle P B hB r) :
    IsSeparated (V.p ≫ hB) ∧ LocallyOfFiniteType (V.p ≫ hB) ∧
      QuasiCompact (V.p ≫ hB) ∧ QuasiCompact V.p ∧
      HasCompactification V.p ∧ IsClosedImmersion V.zeroSection := by
  sorry

/-- Separatedness of the total space over k, supplied by the preceding geometry.
Source: blueprint domain (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_separated (V : PurityVectorBundle P B hB r) :
    IsSeparated (V.p ≫ hB) := (vectorBundleThom_geometry V).1

/-- Local finite type of the total space over k.
Source: blueprint domain (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_lft (V : PurityVectorBundle P B hB r) :
    LocallyOfFiniteType (V.p ≫ hB) := (vectorBundleThom_geometry V).2.1

/-- Quasi-compactness of the total space over k.
Source: blueprint domain (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_qc (V : PurityVectorBundle P B hB r) :
    QuasiCompact (V.p ≫ hB) := (vectorBundleThom_geometry V).2.2.1

/-- Quasi-compactness of the bundle projection.
Source: blueprint domain (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_projection_qc (V : PurityVectorBundle P B hB r) :
    QuasiCompact V.p := (vectorBundleThom_geometry V).2.2.2.1

/-- Compactifiability of the projection, with no extra choice in the bundle data.
Source: blueprint compact supports (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_compactifiable (V : PurityVectorBundle P B hB r) :
    HasCompactification V.p := (vectorBundleThom_geometry V).2.2.2.2.1

/-- The augmentation zero section is closed.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_zero_closed (V : PurityVectorBundle P B hB r) :
    IsClosedImmersion V.zeroSection := (vectorBundleThom_geometry V).2.2.2.2.2

/-- The tautological section is regular over every base in the conventions.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: its components are x_1,...,x_r on every polynomial chart. After quotienting
by earlier coordinates the ring remains polynomial in the remaining ones;
multiplication by the next coordinate is injective by coefficient comparison.
Check this at the zero scheme's points. The empty tuple gives rank zero. -/
theorem vectorBundleTautologicalSection_regular (V : PurityVectorBundle P B hB r) :
    IsRegularSection P V.E (V.p ≫ hB) (vectorBundleTautologicalModule V) r
      (vectorBundleTautologicalSection V) := by
  sorry

/-- The zero scheme is uniquely identified with B over E, not merely equal as a set.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: on every chart the zero quotient is R[x_1,...,x_r]/(x_1,...,x_r)=R,
with augmentation structure map. Glue these identifications. Closed immersions
are monic, so the identification over E is unique, also for r=0. -/
theorem vectorBundleTautologicalZero_existsUnique (V : PurityVectorBundle P B hB r) :
    ∃! e : B ≅ regularSectionZeroScheme P V.E (V.p ≫ hB)
        (vectorBundleTautologicalModule V) r (vectorBundleTautologicalSection V),
      e.hom ≫ regularSectionZeroProjection P V.E (V.p ≫ hB)
        (vectorBundleTautologicalModule V) r (vectorBundleTautologicalSection V) =
          V.zeroSection := by
  sorry

/-- The prescribed zero-scheme identification, fixed by its map into E.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleTautologicalZero (V : PurityVectorBundle P B hB r) :=
  (vectorBundleTautologicalZero_existsUnique V).choose

/-- The inverse zero-scheme identification is also over E.
Source: blueprint first paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: compose the defining equation with the inverse isomorphism and cancel. -/
theorem vectorBundleTautologicalZero_inv (V : PurityVectorBundle P B hB r) :
    (vectorBundleTautologicalZero V).inv ≫ V.zeroSection =
      regularSectionZeroProjection P V.E (V.p ≫ hB) (vectorBundleTautologicalModule V)
        r (vectorBundleTautologicalSection V) := by
  sorry

/-- The supported Thom class has source z_* A_B and is the localized top Chern class
of the tautological section at T=E, transported by the zero-scheme identification.
Source: blueprint first display (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomClass (V : PurityVectorBundle P B hB r) :
    P.FunctorialCupH true V.zeroSection (2 * (r : ℤ)) r :=
  let F := vectorBundleTautologicalModule V
  let s := vectorBundleTautologicalSection V
  letI := (regularSectionZeroIdeal_spec P V.E (V.p ≫ hB) F r s).1
  P.functorialCupChangeSupport true V.zeroSection
    (regularSectionZeroProjection P V.E (V.p ≫ hB) F r s)
    (vectorBundleTautologicalZero V).inv
    (vectorBundleTautologicalZero_inv V)
    (2 * (r : ℤ)) r
    ((localized_top_chern P).choose (V.p ≫ hB) F r s
      (vectorBundleTautologicalSection_regular V))

/-- The finite positive-level coefficient ring, with its existing quotient construction.
Source: blueprint finite coefficients (blueprint: def-pur-vector-bundle-thom-class). -/
instance vectorBundleThom_coefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm

/-- The constant complex has bounded-below etale origin, as needed by the compositor.
Source: blueprint proof Step 3 (blueprint: def-pur-vector-bundle-thom-class).
Proof: use the degree-zero constant etale A-module complex. Exact comparison inverse
image commutes with the degree-zero embedding, giving precisely the constant pro-etale
complex. Its sole nonzero degree is zero. -/
theorem vectorBundleThom_unitOrigin (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T
      ((P.functorialCupSingle true T).obj (P.constant T)) := by
  sorry

/-- The coefficient unit in the compositor's full origin subcategory.
Source: blueprint second display (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomOriginUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory :=
  ⟨(P.functorialCupSingle true T).obj (P.constant T), vectorBundleThom_unitOrigin P T⟩

/-- Closed direct image is exact in this finite-type pro-etale situation.
Source: blueprint proof Step 3 (blueprint: def-pur-vector-bundle-thom-class).
Proof: apply the exact closed pushforward clause of
lem-weil-pbc-proetale-ringed-open-closed, using the canonical equivalence of fixed
A-module sheaves with modules over the constant A-ring sheaf. E is Noetherian,
so the open complement is quasi-compact. -/
theorem vectorBundleThom_zeroPushforward_exact (V : PurityVectorBundle P B hB r) :
    PreservesFiniteColimits (ProEtale.lowerStar
      (ModuleCat.{u + 1} P.Coefficient) V.zeroSection) := by
  sorry

attribute [instance] vectorBundleThom_zeroPushforward_exact

/-- The canonical proper and exact comparisons Rz_! A_B = Rz_* A_B = z_* A_B.
Source: blueprint proof Step 3 (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomClosedIso (V : PurityVectorBundle P B hB r) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj ((P.functorialCupSingle true B).obj (P.constant B)) ≅
        (P.functorialCupSingle true V.E).obj (P.functorialCupSource true V.zeroSection) :=
  (ProEtale.rightDerivedLowerShriekIsoOfIsProper
    (ModuleCat.{u + 1} P.Coefficient) V.zeroSection).app _ ≪≫
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
  ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection).mapDerivedCategorySingleFunctor 0).app (P.constant B)

/-- The zero-section/projection composite is compactifiable because it is the identity.
Source: blueprint proof Step 3 (blueprint: def-pur-vector-bundle-thom-class).
Proof: transport the identity compactification along zeroSection_spec.1. -/
theorem vectorBundleThom_zeroComposite_compactifiable (V : PurityVectorBundle P B hB r) :
    HasCompactification (V.zeroSection ≫ V.p) := by
  sorry

attribute [instance] vectorBundleThom_zeroComposite_compactifiable

/-- The source identification is the recorded compositor, the section equality, and
its identity normalization, after replacing Rz_! A_B by the exact closed image.
Source: blueprint second display (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomSourceIso (V : PurityVectorBundle P B hB r) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      ((P.functorialCupSingle true V.E).obj (P.functorialCupSource true V.zeroSection)) ≅
        (P.functorialCupSingle true B).obj (P.constant B) :=
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).mapIso
    (vectorBundleThomClosedIso V).symm ≪≫
  (ProEtale.originCompositionAmbient P.Coefficient V.zeroSection V.p).app
    (vectorBundleThomOriginUnit P B) ≪≫
  (ProEtale.rightDerivedLowerShriekCongr (ModuleCat.{u + 1} P.Coefficient)
    (V.zeroSection_spec).1).app _ ≪≫
  (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B).ι.mapIso
    ((ProEtale.originCompactSupportId P.Coefficient B).app (vectorBundleThomOriginUnit P B))

/-- Apply compact support to thom(E) after the inverse of the specified source comparison.
No invertibility of tau is asserted here: that belongs to the separate Thom theorem.
Source: blueprint second display (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomTau (V : PurityVectorBundle P B hB r) :
    (P.functorialCupSingle true B).obj (P.constant B) ⟶
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (((P.functorialCupSingle true V.E).obj
          (P.functorialCupTwist true V.E r))⟦2 * (r : ℤ)⟧) :=
  (vectorBundleThomSourceIso V).inv ≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).map
      (vectorBundleThomClass V)

/-- The fiber calculation supplied by projective completion, for positive rank only.
Source: blueprint third display (blueprint: def-pur-vector-bundle-thom-class).
Proof: form P_B(M plus O) and H=P_B(M) using
lem-pur-projective-bundle-tautological-geometry. The complement D_+(t) has affine
rings R[x_1/t,...,x_r/t], so is E. Push the finite-coefficient localization triangle
of prop-sf-open-closed-triangle-all-stages by the proper projection. Its first term
is Rpi_! A_E by def-compact-support-direct-image-detailed. The two decompositions
of thm-pur-projective-bundle-formula identify the restriction with [1_S v] from
S plus A_B(-r)[-2r] to S. Restriction of O(1) and cup naturality identify the first
r columns; the last column need not vanish. The automorphism (s,c) to (s-vc,c)
changes this to projection. Its cone shifted by -1 is A_B(-r)[-2r] plus the
acyclic shifted cone of the identity of S, proving the asserted isomorphism. -/
theorem vectorBundleThom_fiber (V : PurityVectorBundle P B hB r) (_hr : 1 ≤ r) :
    Nonempty ((ProEtale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        ((P.functorialCupSingle true V.E).obj (P.constant V.E)) ≅
      ((P.functorialCupSingle true B).obj
        (P.functorialCupTwist true B (-(r : ℤ))))⟦-2 * (r : ℤ)⟧) := by
  sorry

/-- Rank zero identifies the total space with B through pi, with inverse z.
Source: blueprint rank-zero clause (blueprint: def-pur-vector-bundle-thom-class).
Proof: Sym(0)=O on each affine chart, so pi is an isomorphism. The augmentation
is its inverse; equivalently both maps are identity on each affine ring. -/
theorem vectorBundleThom_rankZero_geometry (V : PurityVectorBundle P B hB 0) :
    IsIso V.p ∧ V.p ≫ V.zeroSection = 𝟙 V.E := by
  sorry

/-- In rank zero the supported class is the identity, under the canonical
restriction A_E = z_* A_B and the zero-shift comparison; this is the empty cup unit.
Source: blueprint rank-zero clause (blueprint: def-pur-vector-bundle-thom-class).
Proof: the tautological section is the empty sum and its zero scheme is the entire
base. Its localized degree-zero top Chern class is the coefficient unit, so after
the zero-scheme transport and shift-zero comparison the composite is the identity. -/
theorem vectorBundleThomClass_rankZero (V : PurityVectorBundle P B hB 0) :
    (P.functorialCupSingle true V.E).map
        (P.functorialCupRestriction true V.zeroSection) ≫
      vectorBundleThomClass V ≫
        (shiftFunctorZero (P.FunctorialCupDerived true V.E) ℤ).hom.app
          ((P.functorialCupSingle true V.E).obj (P.constant V.E)) = 𝟙 _ := by
  sorry

/-- In rank zero tau is the identity after the same coefficient and source
identifications. No projective bundle of negative rank occurs.
Source: blueprint rank-zero clause (blueprint: def-pur-vector-bundle-thom-class).
Proof: apply Rpi_! to the preceding empty-product identity. Compose with the
source comparison and its inverse; the identity normalization of
thm-sf-comp-composition makes the remaining composite the identity of A_B. -/
theorem vectorBundleThomTau_rankZero (V : PurityVectorBundle P B hB 0) :
    vectorBundleThomTau V ≫
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).map
        ((shiftFunctorZero (P.FunctorialCupDerived true V.E) ℤ).hom.app
            ((P.functorialCupSingle true V.E).obj (P.constant V.E)) ≫
          (P.functorialCupSingle true V.E).map
            (P.functorialCupRestriction true V.zeroSection)) ≫
      (vectorBundleThomSourceIso V).hom = 𝟙 _ := by
  sorry

/-- The generator prescription for the contravariant linear total-space map.
Source: blueprint direct-sum projections (blueprint: def-pur-vector-bundle-thom-class). -/
def VectorBundleLinearMapSpec {s : ℕ} (V : PurityVectorBundle P B hB r)
    (W : PurityVectorBundle P B hB s) (a : W.𝓔 ⟶ V.𝓔)
    (f : {f : V.E ⟶ W.E // f ≫ W.p = V.p}) : Prop :=
  ∀ (U : B.Opens) (m : W.𝓔.val.obj (op U)),
    V.E.presheaf.map (eqToHom (congrArg (fun g ↦ op (g ⁻¹ᵁ U)) f.property))
      (f.val.c.app (op (W.p ⁻¹ᵁ U)) (vectorBundleGenerator W U m)) =
        vectorBundleGenerator V U (a.val.app (op U) m)

/-- A map of generator modules determines exactly one linear map of total spaces.
Source: blueprint direct-sum projections (blueprint: def-pur-vector-bundle-thom-class).
Proof: extend a by the symmetric-algebra universal property and apply relative Spec
contravariantly. On each affine chart the ring map sends m to a(m). These maps
agree on overlaps and glue. A ring map out of Sym is determined by its generators,
which proves uniqueness. Transport through the two specified phi isomorphisms. -/
theorem vectorBundleLinearMap_existsUnique {s : ℕ} (V : PurityVectorBundle P B hB r)
    (W : PurityVectorBundle P B hB s) (a : W.𝓔 ⟶ V.𝓔) :
    ∃! f : {f : V.E ⟶ W.E // f ≫ W.p = V.p}, VectorBundleLinearMapSpec V W a f := by
  sorry

/-- The uniquely generator-normalized linear map of total spaces.
Source: blueprint direct-sum projections (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleLinearMap {s : ℕ} (V : PurityVectorBundle P B hB r)
    (W : PurityVectorBundle P B hB s) (a : W.𝓔 ⟶ V.𝓔) :=
  (vectorBundleLinearMap_existsUnique V W a).choose

/-- Linear total-space maps preserve the augmentation zero sections.
Source: blueprint direct-sum projections (blueprint: def-pur-vector-bundle-thom-class).
Proof: compose the generator prescription with augmentation; both composites kill
all generators and fix constants, so their spectra are equal. -/
theorem vectorBundleLinearMap_zero {s : ℕ} (V : PurityVectorBundle P B hB r)
    (W : PurityVectorBundle P B hB s) (a : W.𝓔 ⟶ V.𝓔) :
    V.zeroSection ≫ (vectorBundleLinearMap V W a).val = W.zeroSection := by
  sorry

/-- The literal Cartesian square for the pulled-back zero section.
Source: blueprint supported pullbacks (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomPullbackSquare {s : ℕ} (W : PurityVectorBundle P B hB s)
    {T : Scheme.{u}} (p : T ⟶ W.E) :
    ChosenCartesianSquare (pullback.fst W.zeroSection p)
      (pullback.snd W.zeroSection p) W.zeroSection p where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- Pull back a Thom class to the scheme-theoretic inverse image of its zero section.
Source: blueprint local cup-product clause (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomPullback {s : ℕ} (W : PurityVectorBundle P B hB s)
    {T : Scheme.{u}} (p : T ⟶ W.E) :
    P.FunctorialCupH true (pullback.snd W.zeroSection p) (2 * (s : ℤ)) s :=
  P.functorialCupPullback true W.zeroSection (pullback.snd W.zeroSection p)
    p (pullback.fst W.zeroSection p) (vectorBundleThomPullbackSquare W p)
    (W.p ≫ hB) (2 * (s : ℤ)) s (vectorBundleThomClass W)

/-- The first projection of a direct sum, via the inclusion of its generators.
Source: blueprint local decomposition (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomProjection₁ {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
    (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
    (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔) : V.E ⟶ V₁.E :=
  (vectorBundleLinearMap V V₁ (prod.lift (𝟙 _) 0 ≫ e.inv)).val

/-- The second projection of a direct sum, via the inclusion of its generators.
Source: blueprint local decomposition (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomProjection₂ {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
    (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
    (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔) : V.E ⟶ V₂.E :=
  (vectorBundleLinearMap V V₂ (prod.lift 0 (𝟙 _) ≫ e.inv)).val

/-- The two pulled-back zero supports intersect in the total zero section.
Source: blueprint last paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: in simultaneous frames the two ideals are generated by the first r and
last s polynomial coordinates. Their sum is the augmentation ideal. Thus the
intersection quotient is O_B, and the resulting identification over E is unique
because both support inclusions are monic. -/
theorem vectorBundleThomSumSupport_existsUnique {s : ℕ}
    (V : PurityVectorBundle P B hB (r + s))
    (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
    (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔) :
    ∃! k : B ≅ pullback
        (pullback.snd V₁.zeroSection (vectorBundleThomProjection₁ V V₁ V₂ e))
        (pullback.snd V₂.zeroSection (vectorBundleThomProjection₂ V V₁ V₂ e)),
      k.hom ≫ ProEtale.cupIntersection
        (pullback.snd V₁.zeroSection (vectorBundleThomProjection₁ V V₁ V₂ e))
        (pullback.snd V₂.zeroSection (vectorBundleThomProjection₂ V V₁ V₂ e)) =
          V.zeroSection := by
  sorry

/-- The canonical intersection/zero-section identification fixed over E.
Source: blueprint last paragraph (blueprint: def-pur-vector-bundle-thom-class). -/
def vectorBundleThomSumSupport {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
    (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
    (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔) :=
  (vectorBundleThomSumSupport_existsUnique V V₁ V₂ e).choose

/-- The binary direct-sum law, iterated to give the ordered local product of line
Thom classes. The pullbacks are along the actual linear projections; the support
identification is scheme-theoretic, and the product is the published supported cup.
This statement applies on each open base carrying a decomposition; it also allows
rank-zero summands, whose class is the preceding empty unit.
Source: blueprint last paragraph (blueprint: def-pur-vector-bundle-thom-class).
Proof: in frames the tautological section is the direct sum of the two pulled
sections. Each partial coordinate sequence is regular by the polynomial coefficient
argument, so this is transverse. Apply L2 of thm-pur-localized-top-chern to the
projections and L3 to this transverse sum. Identify the common zero support by the
augmentation quotient. The tensor and shift comparisons are exactly those in
functorialCup, which specializes to def-pur-supported-cup. Iterate this binary
identity using supported-cup associativity to obtain every finite ordered line
product, with the rank-zero identity as the empty product. -/
theorem vectorBundleThomClass_directSum {s : ℕ}
    (V : PurityVectorBundle P B hB (r + s))
    (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
    (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔) :
    HEq ((P.functorialCupSingle true V.E).map
      (P.functorialCupSupportMap true
        (ProEtale.cupIntersection
          (pullback.snd V₁.zeroSection (vectorBundleThomProjection₁ V V₁ V₂ e))
          (pullback.snd V₂.zeroSection (vectorBundleThomProjection₂ V V₁ V₂ e)))
        V.zeroSection (vectorBundleThomSumSupport V V₁ V₂ e).hom
        (vectorBundleThomSumSupport_existsUnique V V₁ V₂ e).choose_spec.1) ≫
      vectorBundleThomClass V)
      (P.functorialCup true (V.p ≫ hB)
        (pullback.snd V₁.zeroSection (vectorBundleThomProjection₁ V V₁ V₂ e))
        (pullback.snd V₂.zeroSection (vectorBundleThomProjection₂ V V₁ V₂ e))
        (2 * (r : ℤ)) (2 * (s : ℤ)) r s
        (vectorBundleThomPullback V₁ (vectorBundleThomProjection₁ V V₁ V₂ e))
        (vectorBundleThomPullback V₂ (vectorBundleThomProjection₂ V V₁ V₂ e))) := by
  sorry

end WeilConjectures.PurityFiniteSetting
