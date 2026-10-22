# AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel

## Reason

Complete the degree-one Artin--Schreier kernel proof using exactness on the base,
instead of the rank-one Frobenius vector-bundle result. Its unused public import is
replaced by the finite-locally-free API required by the existing statement. Added
proof-local options, instance priorities, reducibility attributes and namespace opens
keep concrete tensor-pullback and derived cohomology calculations within the fixed
60-second single-file limit. Preflight requests this record for the public import
removal and these proof-context commands.

The existing public theorem signature is preserved verbatim. All added declarations
are private and proved, or private definitions explicitly constructing the actual maps
and their laws. Every added attribute is local. There are no global instance or simp
attributes, no new public declarations, no changed target meaning, and no adopted
source-library changes.

## Old

Original public imports, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
```

Original namespace opening, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
```

Original theorem signature, verbatim:

```lean
theorem exists_prime_curve_artinSchreier_kernel
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
      (F : Scheme.Modules.liftedCoherentEtaleSheaf E ⟶
        Scheme.Modules.liftedCoherentEtaleSheaf E),
      (∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)),
        F.hom.app U (ULift.up (a.down • e.down)) =
          ULift.up (a.down ^ p •
            (@id Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)
              (F.hom.app U e).down))) ∧
      Nonempty ((moduleAbelianForget (ULift.{u + 1} (ZMod p)) S).obj
        (higherDirectImage (ULift.{u + 1} (ZMod p)) f 1
          ((constantSheaf X.smallEtaleTopology _).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) ≅
        kernel (F - 𝟙 _))
```

## New

New public imports:

```lean
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
```

The theorem signature above is unchanged. The additional namespace opens are
`Opposite` and `open scoped CategoryTheory.Functor`. The initial proof context is:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
open Scheme.Modules in
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

private theorem zariskiSheafifyOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      HasSheafify ((_root_.Opens.grothendieckTopology T).over U) AddCommGrpCat.{u} :=
  fun _ ↦ inferInstance

private theorem zariskiWeakSheafifyOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      HasWeakSheafify ((_root_.Opens.grothendieckTopology T).over U) AddCommGrpCat.{u} :=
  fun U ↦ (zariskiSheafifyOver T U).isRightAdjoint

private theorem zariskiLocallyBijectiveOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      ((_root_.Opens.grothendieckTopology T).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun _ ↦ inferInstance

attribute [local instance 2000] zariskiSheafifyOver zariskiWeakSheafifyOver
  zariskiLocallyBijectiveOver
```

The private scalar endomorphism definition additionally has
`attribute [local irreducible] liftedScalarMap`. These commands affect only
elaboration in this file. Private proof imports provide Artin--Schreier section maps
and exactness, smooth-curve structure direct images, the right-derived universal
delta functor, raw restricted cohomology comparison, and canonical class
normalization and its resolution-class identity. The proof constructs the canonical
comparisons and explicitly packages their data and proved laws; it does not choose
an arbitrary isomorphism from a bare existence statement.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel
--uses AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel` reports
zero current downstream modules and only this item's declaration occurrence.
The quarantined intended parent is also checked below. No consumer adaptation is
required; no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | T4 | Assigned theorem proved; signature unchanged; unused public dependency pruned. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients` | unclaimed; quarantined | Its archived source imports this item at line 23 and independently imports `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel` at line 34. Its theorem use at line 256 therefore retains both the unchanged kernel statement and its separate Frobenius kernel API. No edit is needed. |

The archive remains at
`quarantine/Sheaf/AlgebraicGeometry/ProperSmoothCurvesPrimeCoefficients.lean`,
as recorded in `coord/rework.tsv`. Neither that archive nor its node or mathematical
route is removed. The Frobenius vector-bundle module remains available for it.

## Status

landed 20261022T022955-L-767450 2026-10-22 (merge of deliver/T4/Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel)
