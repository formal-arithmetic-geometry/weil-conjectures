/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Operations on module objects over arbitrary pro-etale ring sheaves

These are the existing transparent operations, factored out for use by the localization
and base-change arguments. Source: Stacks Tags 03D3, 03DI, 03CB and 03CC.
(blueprint: def-sf-proetale-ring-sheaf-operations)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Module inverse image, with inverse-image coefficients and the transported action.
Source: Stacks, Tags 03D2 and 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafInverseImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (upperStar Ab.{u + 1} f).mapMod B

/-- Module direct image, with scalars restricted through the canonical ring unit.
Source: Stacks, Tag 03D3 and Pro-etale Cohomology, section 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (lowerStar Ab.{u + 1} f).mapMod ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom B)

/-- The actual inverse-image/direct-image module adjunction.
Source: Stacks, Tag 03D3
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafAdjunction {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction B

/-- Extension by zero with its coefficient action supplied by the existing projection
formula linearization. Its carrier is the sheafification of extension by zero of the
underlying abelian presheaf, and its action is the sheafified original action.
Source: Stacks, Tags 03DI, 03DJ and 09AE
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft B

/-- The extension-by-zero adjunction with its specified underlying abelian unit and counit.
Source: Stacks, Tag 03DI
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenExtension j B ⊣ ringSheafInverseImage j B :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

/-- The fixed inverse-image composition comparison on a pullback square.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :=
  upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f))

/-- The canonical coefficient identification, with the two successive inverse-image
ring structures made explicit, rather than the structure on a composite functor.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
def ringSheafSquareCoefficient {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ⟶
      (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj B) :=
  (ringSheafSquareComparison g f).hom.app B

/-- Pullback along the fibre projection, with scalars identified by the fixed canonical
composition comparison. Multiplicativity of this comparison is concluded in the theorem.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquarePullback {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    [IsMonHom (ringSheafSquareCoefficient g f B)] :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback g f)) Ab.{u + 1})
        ((upperStar Ab.{u + 1} (pullback.fst g f)).obj
          ((upperStar Ab.{u + 1} g).obj B)) :=
  ringSheafInverseImage (pullback.snd g f) ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap (ringSheafSquareCoefficient g f B)

end AlgebraicGeometry.ProEtale
