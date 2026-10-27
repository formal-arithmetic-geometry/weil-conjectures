/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
import WeilConjectures.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat

/-! # Open restriction and rigidity of relative dualizing pairs over arbitrary bases

Source: Stacks Project, duality.tex, Tags 0E2V, 0E2W and 0E2X.
(blueprint: lem-sfb-relative-dualizing-pair-open-rigidity).
The restriction maps below use the actual adjunction units and composition comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The map of fibre squares for an open source and an open base.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
abbrev relativeDualizingOpenSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    (h : f' ≫ b = j ≫ f) : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f j j b h h

/-- The existing sectionwise restriction functor, typed on the shared module-sheaf
categories so that deriving it uses the supplied localizations in universe w.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
abbrev relativeDualizingOpenRestriction {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] :
    SheafOfModules.{u} (moduleRings B.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings A.toRingedSpace) :=
  Scheme.Modules.restrictFunctor j

/-- Additivity of the existing exact restriction on the shared category instance.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
instance relativeDualizingOpenRestriction_additive {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] : (relativeDualizingOpenRestriction j).Additive :=
  inferInstanceAs (Scheme.Modules.restrictFunctor j).Additive

/-- Preservation of finite limits by the existing exact restriction.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
instance relativeDualizingOpenRestriction_limits {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] : PreservesFiniteLimits (relativeDualizingOpenRestriction j) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor j))

/-- Preservation of finite colimits by the existing exact restriction.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
instance relativeDualizingOpenRestriction_colimits {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] : PreservesFiniteColimits (relativeDualizingOpenRestriction j) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor j))

/-- Derived pullback along an open immersion compared with exact sectionwise restriction,
using the unique comparison of the adjunctions with the same direct image.
Source: Stacks 0E2X, 079W (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
def relativeDualizingOpenPullbackIso {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] :
    derivedPullback j ≅ (relativeDualizingOpenRestriction j).mapDerivedCategory :=
  (relativeMVAdj j).leftAdjointUniq
    (CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (C := SheafOfModules.{u} (moduleRings B.toRingedSpace))
      (D := SheafOfModules.{u} (moduleRings A.toRingedSpace))
      (L := relativeDualizingOpenRestriction j)
      (Scheme.Modules.restrictAdjunction j))

/-- The section-normalized restriction of the ordinary diagonal algebra: the module
base-change map followed by pullback of the structure sheaf. No arbitrary isomorphism
of diagonal objects is chosen.
Source: Stacks 0E2T, 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
def relativeDualizingOpenDiagonalModuleMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] (h : f' ≫ b = j ≫ f) :
    (relativeDualizingOpenRestriction (relativeDualizingOpenSquare f f' j b h)).obj
        (relativeDualizingDiagonalModule f) ⟶ relativeDualizingDiagonalModule f' :=
  ((Scheme.Modules.restrictAdjunction
      (relativeDualizingOpenSquare f f' j b h)).leftAdjointUniq
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (relativeDualizingOpenSquare f f' j b h)))).hom.app _ ≫
    Scheme.Modules.moduleBaseChangeMap (pullback.diagonal f) (pullback.diagonal f')
      (relativeDualizingOpenSquare f f' j b h) j
      (by ext <;> simp [relativeDualizingOpenSquare])
      (SheafOfModules.unit (moduleRings X.toRingedSpace)) ≫
    (Scheme.Modules.pushforward (pullback.diagonal f')).map
      (Scheme.Modules.tensorPullbackObjUnitToUnit j)

/-- Localization of the section-normalized diagonal restriction map in degree zero.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
def relativeDualizingOpenDiagonalMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] (h : f' ≫ b = j ≫ f) :
    (relativeDualizingOpenRestriction
        (relativeDualizingOpenSquare f f' j b h)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)) ⟶
      DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') :=
  (relativeDualizingOpenRestriction
      (relativeDualizingOpenSquare f f' j b h)).mapDerivedCategory.map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app _) ≫
    ((relativeDualizingOpenRestriction
      (relativeDualizingOpenSquare f f' j b h)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      (relativeDualizingOpenDiagonalModuleMap f f' j b h) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _

/-- The canonical diagonal restriction map is invertible, also for an empty source.
Source: Stacks 0E2X, open-restriction and base-open observations
(blueprint: lem-sfb-relative-dualizing-pair-open-rigidity).
Proof: step 1 and step 5 of the node. The square with the two diagonals and j is a
full inverse-image open square: the inverse image of the product open under the
diagonal is precisely the source open. For an open base change the two fibre products
are canonically identical, since the base inclusion is a monomorphism. The ordinary
module base-change map is thus an isomorphism by
lem-weil-pbc-module-base-change-map-open-restriction. Pullback of the structure sheaf
is its canonical isomorphism, so the ordinary diagonal map is invertible. Applying
the degree-zero functor and the exact-restriction localization comparisons preserves
invertibility. This proof uses no dualizing pair, boundedness or Noetherian hypothesis. -/
@[instance] theorem relativeDualizingOpenDiagonalMap_isIso
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] (h : f' ≫ b = j ≫ f) :
    IsIso (relativeDualizingOpenDiagonalMap f f' j b h) := by
  sorry

/-- Pullback by the first projection commutes with the specified open restriction,
using the pinned derived composition comparisons and their adjunction normalization.
Source: Stacks 0E2X, 0D5S (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
def relativeDualizingOpenFirstProjectionIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] (h : f' ≫ b = j ≫ f) :
    derivedPullback (pullback.fst f f) ⋙
        (relativeDualizingOpenRestriction
          (relativeDualizingOpenSquare f f' j b h)).mapDerivedCategory ≅
      (relativeDualizingOpenRestriction j).mapDerivedCategory ⋙
        derivedPullback (pullback.fst f' f') :=
  Functor.isoWhiskerLeft _
      (relativeDualizingOpenPullbackIso (relativeDualizingOpenSquare f f' j b h)).symm ≪≫
    relativeMVComp (relativeDualizingOpenSquare f f' j b h) (pullback.fst f f) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (by simp [relativeDualizingOpenSquare])) ≪≫
    (relativeMVComp (pullback.fst f' f') j).symm ≪≫
    Functor.isoWhiskerRight (relativeDualizingOpenPullbackIso j) _

/-- Restriction of a supplied diagonal class along the actual open square. The inverse
is applied to the canonical diagonal map, whose inverse is uniquely determined by
the preceding invertibility theorem.
Source: Stacks 0E2X (blueprint: lem-sfb-relative-dualizing-pair-open-rigidity). -/
def relativeDualizingOpenClass {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] (h : f' ≫ b = j ≫ f)
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj
        ((relativeDualizingOpenRestriction j).mapDerivedCategory.obj K) :=
  inv (relativeDualizingOpenDiagonalMap f f' j b h) ≫
    (relativeDualizingOpenRestriction
      (relativeDualizingOpenSquare f f' j b h)).mapDerivedCategory.map ξ ≫
    (relativeDualizingOpenFirstProjectionIso f f' j b h).hom.app K

/-- Scalar rigidity, marked uniqueness, and their compatibility with every open source
and base restriction, with no Noetherian assumption.
Source: Stacks 0E2V, 0E2W, 0E2X
(blueprint: lem-sfb-relative-dualizing-pair-open-rigidity).

Proof following the five steps of the node:
1. On U ×_S U restrict the diagonal algebra, its unit and multiplication. The
termwise tensor comparison is strong monoidal and preserves the localization map
(def-pc-derived-pullback-tensor-comparison). Restriction preserves K-flatness
(lem-sfb-ringed-site-restriction-kflat). The evaluation mate is invertible by
lem-pc-open-restriction-evaluation-mate-is-iso and tensor-Hom naturality
(def-pc-canonical-derived-tensor-hom-bijection) carries multiplication by the class
to multiplication by its restriction. Restrict finite-free pseudo-coherent models.
Extend relative Tor test modules by zero on amplitude neighbourhoods to retain
all bounds. Flatness and finite presentation persist on open affine charts
(lem-weil-pbc-lfp-affine-opens-finite-presentation). Thus supplied pairs restrict.
2. Use lem-sfb-arbitrary-base-affine-dualizing-realization on affine basis opens.
The lem-sfb-arbitrary-ring-relative-dualizing-homothety identifies their scalar maps
with isomorphisms. The unit law of the tensor comparison identifies these maps with
the restricted scalar map. Its cone therefore has zero cohomology sheaves globally.
The same affine calculation gives negative self-Ext vanishing on the basis.
3. The lem-sfb-arbitrary-ring-relative-dualizing-isomorphism gives an unmarked affine
isomorphism. Its action on the diagonal generator is multiplication by a unique unit.
Multiply by the inverse unit to preserve the class. Homothety makes this normalization
unique, and the affine realization transfers the normalized isomorphism to sheaves.
4. Apply lem-trf-diagonal-class-basis-descent to these uniquely marked basis maps and
the negative self-Ext vanishing. Obtain exactly one global marked isomorphism.
Repeat on every open, including the empty open, whose module category is zero.
Naturality of the class transport identifies the restricted global isomorphism.
5. For an open base factorization, the canonical map of fibre squares is an
isomorphism, since the base inclusion is a monomorphism. Diagonal, first projection,
classes, inverse-image coefficient rings and relative Tor tests identify. The pair
predicate and marked comparison are therefore unchanged. -/
theorem relativeDualizingPair_open_rigidity
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (K L : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj L)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (hL : IsCoherentRelativeDualizingPair f L η) :
    IsIso (relativeDualizingScalarMap X K) ∧
    (∃! α : K ≅ L,
      ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η) ∧
    ∀ (X' S' : Scheme.{u}) (f' : X' ⟶ S') (j : X' ⟶ X) (b : S' ⟶ S)
        [IsOpenImmersion j] [IsOpenImmersion b]
        [IsSeparated f'] [Flat f'] [LocallyOfFinitePresentation f']
        (h : f' ≫ b = j ≫ f),
        IsIso (relativeDualizingOpenDiagonalMap f f' j b h) ∧
        IsCoherentRelativeDualizingPair f'
          ((relativeDualizingOpenRestriction j).mapDerivedCategory.obj K)
          (relativeDualizingOpenClass f f' j b h K ξ) ∧
        IsCoherentRelativeDualizingPair f'
          ((relativeDualizingOpenRestriction j).mapDerivedCategory.obj L)
          (relativeDualizingOpenClass f f' j b h L η) ∧
        IsIso (relativeDualizingScalarMap X'
          ((relativeDualizingOpenRestriction j).mapDerivedCategory.obj K)) ∧
        (∃! β : (relativeDualizingOpenRestriction j).mapDerivedCategory.obj K ≅
            (relativeDualizingOpenRestriction j).mapDerivedCategory.obj L,
          relativeDualizingOpenClass f f' j b h K ξ ≫
            (derivedPullback (pullback.fst f' f')).map β.hom =
              relativeDualizingOpenClass f f' j b h L η) ∧
        ∀ α : K ≅ L,
          ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η →
          relativeDualizingOpenClass f f' j b h K ξ ≫
            (derivedPullback (pullback.fst f' f')).map
              ((relativeDualizingOpenRestriction j).mapDerivedCategory.map α.hom) =
                relativeDualizingOpenClass f f' j b h L η := by
  sorry

/-- Passing to an open base through which f factors gives the same supplied-pair
predicate and the same condition on any comparison, under the canonical class transport.
Source: Stacks 0E2X, first paragraph of the proof
(blueprint: lem-sfb-relative-dualizing-pair-open-rigidity).
Proof: this is step 5 of the node. The base inclusion is a monomorphism, so the
canonical map X ×_V X → X ×_S X is an isomorphism. Its square with the diagonal
identifies the diagonal algebra, including multiplication and unit. The pinned
composition comparison identifies the first projection and the transported class.
The inverse-image rings from V and S identify because V → S is open; hence the
relative Tor tests agree in both directions. Pseudo-coherence is intrinsic to X.
These identifications prove the equivalence of the pair predicates. Functoriality
of restriction and the first-projection comparison proves the equivalence of
class preservation for every isomorphism. Thus uniqueness gives the same marked
comparison. Empty V forces X empty and all the same identifications still apply. -/
theorem relativeDualizingPair_open_base_iff
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (V : S.Opens) (g : X ⟶ V.toScheme) (h : g ≫ V.ι = (𝟙 X) ≫ f)
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g]
    (K L : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj L) :
    (IsCoherentRelativeDualizingPair f K ξ ↔
      IsCoherentRelativeDualizingPair g
        ((relativeDualizingOpenRestriction (𝟙 X)).mapDerivedCategory.obj K)
        (relativeDualizingOpenClass f g (𝟙 X) V.ι h K ξ)) ∧
    (∀ α : K ≅ L,
      (ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η ↔
        relativeDualizingOpenClass f g (𝟙 X) V.ι h K ξ ≫
          (derivedPullback (pullback.fst g g)).map
            ((relativeDualizingOpenRestriction (𝟙 X)).mapDerivedCategory.map α.hom) =
          relativeDualizingOpenClass f g (𝟙 X) V.ι h L η)) := by
  sorry

end AlgebraicGeometry
