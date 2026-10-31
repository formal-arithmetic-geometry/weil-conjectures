/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalRestriction
public import WeilConjectures.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk

/-! # Canonical global arrows used by the normalized line-family stalk comparison

Source: blueprint latest, sk-prop-a1-kummer, prop-pur-gm-relative-kummer.proof.md,
Step 2; Stacks Project, Tags 03Q8, 03Q9 and 03PL
(blueprint: def-pur-normalized-kummer-global-arrows).

This module only defines data; it states no theorem. For a k-scheme B it gives the
family C_B = C x_k B with its projection a_B and k-structure, the derived global sections
G(T) and derived direct image I(f) of the root line L, the global germ Gamma -> stalk at
a geometric point s through the terminal etale object, the edge germ G(X) -> I(f)_s
(inverse Leray comparison followed by the derived germ), the constant map
c_T : A_T -> L_T, a -> zeta tensor a, its transpose under the constant-sheaf/sections
derived adjunction, the untwisted unit A_B[0] -> L_B -> I(f) and its stalk through the
canonical constant-stalk identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Forgetting modules preserves filtered colimits indexed in the site universe.
Source: Stacks Tag 03Q9 (blueprint: def-pur-normalized-kummer-global-arrows). -/
instance normalizedKummerForgetFiltered (A : Type (u + 1)) [CommRing A] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} (forget (ModuleCat.{u + 1} A))

/-- The family C times B, with the specified affine or Laurent curve.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerFamily {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (b : Bool) := pullback (KummerLine.structureMap k b) p

/-- The projection a_B of the specified family.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerProjection {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (b : Bool) := pullback.snd (KummerLine.structureMap k b) p

/-- Its k-structure, using the projection to C.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerStructure {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (b : Bool) :=
  pullback.fst (KummerLine.structureMap k b) p ≫ KummerLine.structureMap k b

/-- Derived global sections of the existing root line.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerGlobal (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj
    (relativeKummerLinePlus A m hA T)

/-- The existing derived direct image of the root line.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerImage (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {X B : Scheme.{u}} (f : X ⟶ B) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj
    (relativeKummerLinePlus A m hA X)

/-- The global germ in module coefficients.
Source: Stacks Tag 03Q9 (blueprint: def-pur-normalized-kummer-global-arrows). -/
def normalizedKummerGlobalGerm (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    Sheaf.Γ B.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      (Scheme.pointSmallEtale s).sheafFiber :=
  (Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale B)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf _ _)
      ((Scheme.pointSmallEtale s).toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 B))
        (Over.homMk s (Category.comp_id s)))

/-- Leray followed by the derived germ. Hq of this arrow is the germ of the Leray
edge section, after the exact-stalk cohomology comparison.
Source: Stacks Tag 03Q9 (blueprint: def-pur-normalized-kummer-global-arrows). -/
@[irreducible]
def normalizedKummerEdgeGerm (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {X B : Scheme.{u}} (f : X ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) :
    normalizedKummerGlobal A m hA X ⟶
      ((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.obj (normalizedKummerImage A m hA f) :=
  (moduleLerayPlus A f).inv.app (relativeKummerLinePlus A m hA X) ≫
    (Functor.rightDerivedFunctorPlusNatTrans (normalizedKummerGlobalGerm A s) ≫
      ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom).app
      (normalizedKummerImage A m hA f)

/-- Transpose a degree-zero coefficient map under constant sheaves and derived sections.
Source: Stacks Tag 01EZ (blueprint: def-pur-normalized-kummer-global-arrows). -/
@[irreducible]
def normalizedKummerGlobalSection (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u})
    (c : kummerExchangeConstant A T ⟶ Scheme.finiteEtaleTateLine T m A hA) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (ModuleCat.of A A) ⟶
      normalizedKummerGlobal A m hA T :=
  ((constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).derivedPlus.homEquiv
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (ModuleCat.of A A))
    (relativeKummerLinePlus A m hA T))
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map c)

/-- The actual constant map a -> zeta tensor a, extended from its section on one by
A-linearity and the constant-sheaf adjunction.
Source: Stacks Tag 03PK (blueprint: def-pur-normalized-kummer-global-arrows). -/
@[irreducible]
def normalizedKummerConstantMap (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) (T : Scheme.{u}) (p : T ⟶ Spec (.of k)) :
    kummerExchangeConstant A T ⟶ Scheme.finiteEtaleTateLine T m A hA :=
  ((constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton A _
      ((Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).inv.app
          (Scheme.finiteEtaleTateLine T m A hA)
            (Sheaf.H.equiv₀ ((RawModuleScalarComparison.forget A T).obj
              (Scheme.finiteEtaleTateLine T m A hA))
                (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
                  (relativeKummerConstant A m hm hA hζ T p 1)))))

/-- The untwisted unit, using the chosen primitive root.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
@[irreducible]
def normalizedKummerUntwistedUnit (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) {X B : Scheme.{u}} (p : B ⟶ Spec (.of k))
    (f : X ⟶ B) (hB : IsUnit (m : Γ(B, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (kummerExchangeConstant A B) ⟶
      normalizedKummerImage A m hA f :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (normalizedKummerConstantMap A m hm hA hζ B p) ≫
    relativeKummerUnit A m hm hA f hB hX

/-- The stalk of the untwisted unit, with the canonical constant-stalk identification.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
@[irreducible]
def normalizedKummerUnitGerm (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) {X B : Scheme.{u}} (p : B ⟶ Spec (.of k))
    (f : X ⟶ B) (hB : IsUnit (m : Γ(B, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (ModuleCat.of A A) ⟶
      ((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.obj
          (normalizedKummerImage A m hA f) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).inv ≫
    (Functor.mapDerivedCategoryPlusSingleFunctor
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)) 0).inv.app _ ≫
    ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.map
        (normalizedKummerUntwistedUnit A m hm hA hζ p f hB hX)

end AlgebraicGeometry.Etale
