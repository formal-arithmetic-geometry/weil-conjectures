module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf

/-! # A Zariski local criterion for a trace-defined adjunction

Source: Stacks Project, duality.tex, section-trace and equation-sheafy-trace;
cohomology.tex, Tags 08DK, 08FE and 0D5X; perfect.tex, Tag 08EU.
(blueprint: lem-sfb-zariski-local-duality-adjunction).

The counit is specified by its composite with the canonical projection mate.
Since this mate is invertible on quasi-coherent objects, this specifies exactly
inverse projection followed by tensoring with the supplied trace. The same
normalization is imposed locally. The local trace is specified by its composite
with the canonical open base-change map, which is invertible by Tag 08FE.
Thus neither the projection isomorphism nor the restricted trace is arbitrary.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Pullback followed by tensor with the specified complex, on the full unbounded
module derived categories. Source: Stacks, perfect.tex, Tag 08EU, and duality.tex,
section-trace (blueprint: lem-sfb-zariski-local-duality-adjunction). -/
def zariskiTraceTensorFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    (K : schemeDerivedCategory X) : schemeDerivedCategory S ⥤ schemeDerivedCategory X :=
  derivedPullback f ⋙ tensorRight K

/-- The canonical projection mate, with the base factor first. The adjunction and
pullback tensor comparison have the same fixed left-derived counit, as required
for the canonical projection formula. Source: Stacks, perfect.tex, Tag 08EU;
cohomology.tex, Tag 079U
(blueprint: lem-sfb-zariski-local-duality-adjunction). -/
def zariskiTraceProjectionMap {X S : Scheme.{u}} (f : X ⟶ S)
    (M : schemeDerivedCategory S) (K : schemeDerivedCategory X) :
    M ⊗ (schemeDerivedDirectImage f).obj K ⟶
      (schemeDerivedDirectImage f).obj ((zariskiTraceTensorFunctor f K).obj M) :=
  (canonicalPullbackAdjunction f).homEquiv _ _
    ((mixedHomTensorPullbackIso f).hom.app (M, (schemeDerivedDirectImage f).obj K) ≫
      ((derivedPullback f).obj M ◁ (canonicalPullbackAdjunction f).counit.app K))

/-- The pullback unit identification belonging to the fixed canonical tensorator.
The tensorator determines the monoidal unit by its unit laws. The chosen existence
witness therefore does not select an unspecified object or an arbitrary unit map.
Source: Stacks, cohomology.tex, Tag 079U
(blueprint: lem-sfb-zariski-local-duality-adjunction). -/
def zariskiTracePullbackUnitIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (derivedPullback f).obj (𝟙_ (schemeDerivedCategory S)) ≅
      𝟙_ (schemeDerivedCategory X) :=
  (Classical.choose (canonicalPullbackTensor_monoidal_realization f
    (fun A B ↦ (mixedHomTensorPullbackIso f).hom.app (A, B))
    (Classical.choose_spec (exists_mixedHomTensorPullbackIso f)))).εIso.symm

/-- Affine-local trace adjunctions give the global trace adjunction on unbounded
quasi-coherent derived categories, without any finiteness assumption on the schemes.
Source: Stacks, duality.tex, section-trace, equation-sheafy-trace and equation-global-hom;
cohomology.tex, Tags 08DK, 08FE and 0D5X; perfect.tex, Tag 08EU.
(blueprint: lem-sfb-zariski-local-duality-adjunction).

Proof:
1. Separated implies quasi-separated (lem-pc-separated-quasi-separated).
Derived pullback and tensor preserve quasi-coherent cohomology
(lem-pc-derived-pullback-tensor-qcoh), as does direct image for the given morphism
(lem-pc-derived-direct-image-preserves-qcoh). The unbounded projection formula
(lem-pc-projection-formula) identifies the normalized counit with the trace formula.
2. For E and M, put N = Lf*M tensor K. Form the sheafy comparison from
Rf*RHom(E,N) to RHom(Rf*E,M) by direct-image evaluation followed by the counit.
The comparison-on-open-Ext lemma lem-sfb-direct-image-hom-open-ext and
lem-trf-open-ext-hypercohomology-comparison identify its open hypercohomology maps
with u mapped to Rg*(u) followed by the restricted counit, in every degree.
Use lem-pc-restrict-derived-direct-image-open for the direct-image restrictions.
3. On every affine open these maps are bijective by the local adjunction,
applied also to shifted E. The pullback and tensor restriction comparisons
lem-pc-derived-pullback-open-restriction-universes and
lem-pc-derived-tensor-open-restriction-natural identify its functor and counit
with the ones specified by the restricted trace.
4. By lem-trf-unbounded-direct-image-section-presheaf, sheafifying these open
hypercohomology groups gives the cohomology sheaves. Affine neighbourhoods form
a basis, so the comparison is invertible on all cohomology stalks and hence in
the derived category. Taking degree-zero global hypercohomology and using
lem-trf-open-ext-hypercohomology-comparison gives the displayed bijection.
Its naturality in E follows from functoriality of direct image and composition;
its naturality in M follows from the natural transformation ε. No finite cover,
boundedness or global quasi-compactness or quasi-separatedness is used. -/
theorem zariskiLocalDualityAdjunction {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f]
    (K : schemeDerivedQCohCategory X)
    (τ : (schemeDerivedDirectImage f).obj K.obj ⟶ 𝟙_ (schemeDerivedCategory S))
    (ε : (schemeDerivedQCohProperty S).ι ⋙ zariskiTraceTensorFunctor f K.obj ⋙
      schemeDerivedDirectImage f ⟶ (schemeDerivedQCohProperty S).ι)
    (hε : ∀ M : schemeDerivedQCohCategory S,
      zariskiTraceProjectionMap f M.obj K.obj ≫ ε.app M =
        M.obj ◁ τ ≫ (ρ_ M.obj).hom)
    (hlocal : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (τV : (schemeDerivedDirectImage (f ∣_ V)).obj
            ((derivedPullback (f ⁻¹ᵁ V).ι).obj K.obj) ⟶
          𝟙_ (schemeDerivedCategory V.toScheme))
        (εV : (schemeDerivedQCohProperty V.toScheme).ι ⋙
          zariskiTraceTensorFunctor (f ∣_ V)
            ((derivedPullback (f ⁻¹ᵁ V).ι).obj K.obj) ⋙
          schemeDerivedDirectImage (f ∣_ V) ⟶ (schemeDerivedQCohProperty V.toScheme).ι),
        schemeDerivedBaseChangeMap f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
            (morphismRestrict_ι f V).symm K.obj ≫ τV =
          (derivedPullback V.ι).map τ ≫ (zariskiTracePullbackUnitIso V.ι).hom ∧
        (∀ M : schemeDerivedQCohCategory V.toScheme,
          zariskiTraceProjectionMap (f ∣_ V) M.obj
              ((derivedPullback (f ⁻¹ᵁ V).ι).obj K.obj) ≫ εV.app M =
            M.obj ◁ τV ≫ (ρ_ M.obj).hom) ∧
        ∀ (E : schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme)
          (M : schemeDerivedQCohCategory V.toScheme),
          Function.Bijective (fun a : E.obj ⟶
              (zariskiTraceTensorFunctor (f ∣_ V)
                ((derivedPullback (f ⁻¹ᵁ V).ι).obj K.obj)).obj M.obj ↦
            (schemeDerivedDirectImage (f ∣_ V)).map a ≫ εV.app M)) :
    ∀ (E : schemeDerivedQCohCategory X) (M : schemeDerivedQCohCategory S),
      Function.Bijective (fun a : E.obj ⟶ (zariskiTraceTensorFunctor f K.obj).obj M.obj ↦
        (schemeDerivedDirectImage f).map a ≫ ε.app M) := by
  sorry

end AlgebraicGeometry
