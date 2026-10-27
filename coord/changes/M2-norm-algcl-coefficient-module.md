# AlgebraicGeometry.ProEtale.NormAlgclComparison coefficient constructions

## Reason

The geometric normalization lemma and its parent must refer to the same actual coefficient
inclusion, derived tensor arrow and global-sections functor. Passing generic presentations
required expensive definitional comparisons of pulled-back ring multiplication. Extract the
already constructed declarations verbatim to a shared module and publicly reexport that module
from the parent. Every declaration retains its original name, signature, body and visibility.
There is no mathematical definition change, hence no target statement review is reopened.
The new module is under Sheaf, not the adopted source-library tree.

## Old

The following declarations were in `Sheaf.Paper.NormAlgclCohomologyTopologyComparison`:

```lean
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Sectionwise inclusion of finite-subextension-valued continuous functions.
Source: the coefficient inclusion in paragraph (3) of the source proof
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientInclusionRing :
    Profinite.padicAlgClCondensedRing.{u} ℓ ⟶
      Profinite.continuousMapRingSheaf (PadicAlgCl ℓ) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop).subtype.comp
            ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same inclusion as a morphism of the recorded condensed ring objects.
Source: paragraph (3), c:C to B
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientInclusion :
    Profinite.padicAlgClRingObj.{u} ℓ ⟶
      Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (coefficientInclusionRing ℓ)

/-- The inclusion respects units and multiplication, since it comes from ring maps.
Source: paragraph (3), c:C to B
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
instance coefficientInclusion_isMonHom : IsMonHom (coefficientInclusion.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (coefficientInclusionRing ℓ)))

variable (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The finite-field inclusion A to C_X, using the published scalar inclusion.
Source: paragraph (3), finite intermediate field E
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev finiteScalarMap :=
  (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)

/-- Pullback of c to X, including its ring-object structure.
Source: paragraph (3), c_X
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev inclusionOnScheme := (upperStarFromPoint X).map (coefficientInclusion ℓ)

/-- The regular C_X-module restricted to A.
Source: paragraph (3), Res(C_X)
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev finiteSubextensionModule :=
  (Mod.comap (finiteScalarMap ℓ X E)).obj
    (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))

/-- The regular B_X-module restricted to A along the composite inclusion.
Source: paragraph (3), Res(B_X)
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev normContinuousModule :=
  (Mod.comap (finiteScalarMap ℓ X E ≫ inclusionOnScheme ℓ X)).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))

/-- The actual A-linear coefficient inclusion, with its action inherited by restriction.
Source: paragraph (3), c_X viewed as a morphism of A-modules
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientModuleMap : finiteSubextensionModule ℓ X E ⟶ normContinuousModule ℓ X E :=
  Mod.Hom.mk' (inclusionOnScheme ℓ X) (by
    change (finiteScalarMap ℓ X E ▷ _ ≫ MonObj.mul) ≫ inclusionOnScheme ℓ X =
      _ ◁ inclusionOnScheme ℓ X ≫
        (finiteScalarMap ℓ X E ≫ inclusionOnScheme ℓ X) ▷ _ ≫ MonObj.mul
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc])

/-- The canonical comparison m_V in D(A). Tensoring the degree-zero inclusion with V
computes restricted derived extension of scalars on either side, and on any flat-term
K-flat model P the chain map is z tensor v mapping to c_X(z) tensor v.
Source: paragraph (3), displayed m_V
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def comparison
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :=
  ((DerivedCategory.singleFunctor _ 0).map (coefficientModuleMap ℓ X E)) ▷ V

/-- Forget A-actions exactly, then take ordinary unbounded derived global sections.
Source: paragraph (3), R Gamma on the small pro-etale site
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def derivedGlobalSections :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) ⥤
        DerivedCategory Ab.{u + 1} :=
  letI := (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).isRightAdjoint
  letI : (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Mod.forget (condensedRingObj (Profinite.continuousMapRingObj E) X)).mapDerivedCategory ⋙
    (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).rightDerivedFunctor

```

## New

Exactly the same declaration text is in `Sheaf.Paper.NormAlgclCoefficientMap`.
The parent starts with `public import Sheaf.Paper.NormAlgclCoefficientMap`; the normalization
module publicly imports the same shared construction. The original module therefore continues
to export every original declaration with exactly its original meaning. The definition node's
Lean attachment follows the extracted coefficient inclusion. The original theorem stays in its
original module with its original signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormAlgclCohomologyTopologyComparison | M2 | Public reexport; proof uses the shared geometric normalization. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | No edit; same exported names, types and bodies. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | No edit; same exported names, types and bodies. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | No edit; same exported names, types and bodies. |
| Sheaf.Paper.NormAlgclGeometricComparison | M2, new | Uses the actual shared constructions directly. |

The users are from `tools/downstream.py ... --uses coefficientInclusion`. No consumer requires a
forced adaptation: declaration identities, public signatures and definitions are preserved.

## Status

landed 20261025T050838-L-3850424 2026-10-25 (merge of deliver/M2/Sheaf.Paper.NormAlgclCohomologyTopologyComparison)
