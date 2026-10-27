/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.SchemeLiftClassificationData
public import Sheaf.AlgebraicGeometry.ZariskiSquareZeroExtensions
public import Sheaf.Topology.ZariskiSheafAlgebraExtensionExt

/-! # Cotangent Ext classification of marked scheme lifts

Source: Stacks Project, Deformation Theory, Tags 0D14, 0GPZ, 0GQ0--0GQ2;
Cotangent Complex, Tags 08UW and 08UZ; More on Morphisms, Tag 0D0I
(blueprint: def-sfb-scheme-coefficient-extension-problems).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution Simplicial

namespace AlgebraicGeometry.SchemeDeformation

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- The square-zero extension problem on the fixed special fibre, including arbitrary
coefficient sheaves. Source: Stacks 08UC
(blueprint: def-sfb-scheme-coefficient-extension-problems). -/
abbrev SchemeProblem {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') (G : X.Modules) :=
  TopCat.SquareZero.Problem (baseReduction f i) (Scheme.Modules.tensorPullbackRingMap f) G

/-- A torsor of solutions for a prescribed base-ideal map, using actual extension
isomorphism classes. Source: Stacks 08UC
(blueprint: def-sfb-scheme-coefficient-extension-problems). -/
structure SolutionTorsor (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'} {G : X.Modules}
    (P : SchemeProblem f i G) where
  translate : Ext C D f G 1 → P.Classes → P.Classes
  zero (x : P.Classes) : translate 0 x = x
  add (a b : Ext C D f G 1) (x : P.Classes) :
    translate (a + b) x = translate a (translate b x)
  unique (x y : P.Classes) : ∃! a : Ext C D f G 1, translate a x = y

/-- The intrinsic extension of a scheme lift, including its actual ring sheaf,
quotient, ideal inclusion and base map on every local base section.
Source: Stacks 0D14 and 08UC
(blueprint: def-sfb-scheme-coefficient-extension-problems). -/
structure LiftSolution {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (P : SchemeProblem f i (coefficient f i)) (Y : Lift f i) (K : LiftKernel Y) where
  solution : P.Solution
  ring : solution.val.ring ≅
    TopCat.Sheaf.inverseImageRing Y.marking.base Y.space.sheaf
  quotient : ring.hom ≫ Scheme.Modules.tensorPullbackRingMap Y.marking =
    solution.val.p
  inclusion (V : X.Opens) (g : Γ(coefficient f i, V)) :
    ring.hom.hom.app (op V) (solution.val.i (op V) g) = K.inclusion V g
  base (V : S'.Opens) (W : X.Opens) (h : W ≤ (f ≫ i) ⁻¹ᵁ V)
    (h' : W ≤ Y.marking ⁻¹ᵁ (Y.projection ⁻¹ᵁ V)) (a : Γ(S', V)) :
    ring.hom.hom.app (op W)
      (solution.val.base.hom.app (op W) (inverseSection (f ≫ i) V W h a)) =
        inverseSection Y.marking (Y.projection ⁻¹ᵁ V) W h' (Y.projection.app V a)

/-- Restrict the scalars of an actual extension along a base ring reduction.
Source: Stacks 08UC (blueprint: def-sfb-scheme-coefficient-extension-problems). -/
def rebaseExtension {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    (q : R' ⟶ R) {ρ : R ⟶ A}
    {G : TopCat.SquareZeroSheaf.Modules A}
    (E : TopCat.SquareZeroSheaf.Extension ρ G) :
    TopCat.SquareZeroSheaf.Extension (q ≫ ρ) G :=
  { E with base := q ≫ E.base, base_p := by rw [Category.assoc, E.base_p] }

/-- The normalized polynomial-conormal representative interpreted in the chosen
sheaf derived localization. All its maps are the recorded, coordinate-normalized
maps; this also handles a derived-category universe different from the standard one.
Source: Stacks 0GQ0 (blueprint: def-sfb-scheme-coefficient-extension-problems). -/
def extensionClass {C : Coherence.{u}} {D : TopCat.SheafCotangent.Comparison C}
    (s : TopCat.SquareZeroSheaf.Classification C D)
    {X S : Scheme.{u}} {f : X ⟶ S} {G : X.Modules}
    (E : TopCat.SquareZeroSheaf.Extension (Scheme.Modules.tensorPullbackRingMap f) G)
    (a : TopCat.SquareZeroSheaf.ConormalClass C D E
      (s.standardPresentation _) (s.projection _) (s.extensionPresentation E)
      (s.cl _ G E)) : Ext C D f G 1 :=
  letI := a.quasiIso
  DerivedCategory.Q.map (s.projection _).map ≫
    inv (DerivedCategory.Q.map a.comparison) ≫ DerivedCategory.Q.map a.map ≫
    ((DerivedCategory.singleFunctors (SheafOfModules.{u} X.ringCatSheaf)).shiftIso
      1 (-1) 0 (add_neg_cancel (1 : ℤ))).inv.app G

/-- The split family, as an extension over the original field. Its ring, quotient,
kernel and field action are the actual ones of the marked lift.
Source: Stacks 0GPZ (blueprint: def-sfb-scheme-coefficient-extension-problems). -/
structure SplitLiftExtension {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {M : ModuleCat.{u} k}
    (Y : Lift f (directionReduction k M)) (K : LiftKernel Y)
    (t : coefficient f (directionReduction k M) ≅ directionModule f M) where
  extension : TopCat.SquareZeroSheaf.Extension
    (Scheme.Modules.tensorPullbackRingMap f) (directionModule f M)
  ring : extension.ring ≅ TopCat.Sheaf.inverseImageRing Y.marking.base Y.space.sheaf
  quotient : ring.hom ≫ Scheme.Modules.tensorPullbackRingMap Y.marking = extension.p
  inclusion (V : X.Opens) (g : Γ(coefficient f (directionReduction k M), V)) :
    ring.hom.hom.app (op V) (extension.i (op V) (t.hom.app V g)) = K.inclusion V g
  base (V : (Spec (.of k)).Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (h' : W ≤ Y.marking ⁻¹ᵁ (Y.projection ⁻¹ᵁ ((directionProjection k M) ⁻¹ᵁ V)))
    (a : Γ(Spec (.of k), V)) :
    ring.hom.hom.app (op W)
      (extension.base.hom.app (op W) (inverseSection f V W h a)) =
        inverseSection Y.marking _ W h'
          (Y.projection.app _ ((directionProjection k M).app V a))

end AlgebraicGeometry.SchemeDeformation
