/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationExtension
import WeilConjectures.RingTheory.NormalLocalDepthTwo
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation
import WeilConjectures.RingTheory.DualDepthTwo
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# Coherent reflexive modules across a codimension-two complement

Source: Stacks Project, Divisors, Tag 0EBJ, specialized using Properties, Tag 0345
(blueprint: lem-sfb-normal-reflexive-open-equivalence).

The equivalence is stated through preservation of its full subcategories and the
canonical adjunction unit and counit. All module morphisms are retained, and the
restriction map on their Hom sets is explicitly asserted to be bijective.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction and direct image are quasi-inverse on coherent reflexive modules over an
integral locally Noetherian normal scheme when the omitted local rings have dimension
at least two. Reflexivity means invertibility of the actual bidual evaluation morphism.
The first clause gives restriction preservation and the unit; the second gives direct-image
preservation and the counit; the third records the induced bijection on every Hom set.

Source: Stacks Project, Divisors, Tag 0EBJ; Properties, Tag 0345
(blueprint: lem-sfb-normal-reflexive-open-equivalence).

Proof:
1. Every boundary stalk is a Noetherian normal local domain: choose a Noetherian affine
   neighbourhood and localize. By the normal-local-depth theorem, its dimension bound
   implies depth at least two. This remains true in every open neighbourhood.
2. Restriction preserves coherence by coherence locality, and preserves the bidual
   evaluation since sheaf Hom on an open is the sheaf of the same local module maps.
   For coherent reflexive F, its dual is coherent by coherent sheaf Hom (the structure
   sheaf is coherent on a locally Noetherian scheme). Thus its dual is locally finitely
   presented with finite stalks. Stalk-Hom comparison identifies the stalk of F with the
   dual of the stalk of its dual. The local dual-depth theorem gives depth at least two
   at boundary points. Coherence implies quasi-coherence and finite type, giving finite
   sections on affine opens and finite stalks. The depth-two Hartogs restriction theorem
   therefore makes the canonical unit an isomorphism. The same applies on affine opens.
3. For coherent reflexive G on V, work on a nonempty affine open A of Y. The intersection
   with V is quasi-compact since an open immersion into a locally Noetherian scheme is
   quasi-compact. G restricted to that intersection is finitely presented. Apply the
   finite-presentation extension theorem to its zero map into the zero module on A.
   The resulting finitely presented extension H is coherent by the locally Noetherian
   coherent-finite-type criterion. No global quasi-compactness is needed.
4. Replace H by its explicit double dual E. The coherent-reflexive-hull theorem makes E
   coherent reflexive. Restriction commutes with the double dual, so E restricts to G.
   Step 2 on A identifies E with the direct image of that restriction. Section by section
   this direct image is the restriction of j_*G to A, with identical scalar action and
   restriction maps. Coherence glues on the affine cover; the stalk criterion for
   reflexivity gives reflexivity of j_*G as well.
5. The counit on each open of V is the identity on the sections of G. The functors act on
   all module morphisms, and their unit and counit are natural. Their invertibility on
   the specified full subcategories gives the quasi-inverse equivalence. Explicitly,
   extend a morphism a between restrictions by eta_F1, followed by j_*a, followed by the
   inverse of eta_F2. The triangle identities show its restriction is a, and naturality
   of the unit gives uniqueness. Hence the map on every Hom set is bijective. -/
theorem normal_reflexive_open_equivalence
    {Y V : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (hnormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : V ⟶ Y) [IsOpenImmersion j]
    (hcodim : ∀ y : Y, y ∉ Set.range j →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)) :
    (∀ F : Y.Modules, RingedSpace.IsCoherent Y.toRingedSpace F →
      IsIso (SheafOfModules.bidual (R := Y.sheaf) F) →
        RingedSpace.IsCoherent V.toRingedSpace ((restrictFunctor j).obj F) ∧
        IsIso (SheafOfModules.bidual (R := V.sheaf) ((restrictFunctor j).obj F)) ∧
        IsIso ((restrictAdjunction j).unit.app F)) ∧
    (∀ G : V.Modules, RingedSpace.IsCoherent V.toRingedSpace G →
      IsIso (SheafOfModules.bidual (R := V.sheaf) G) →
        RingedSpace.IsCoherent Y.toRingedSpace ((pushforward j).obj G) ∧
        IsIso (SheafOfModules.bidual (R := Y.sheaf) ((pushforward j).obj G)) ∧
        IsIso ((restrictAdjunction j).counit.app G)) ∧
    (∀ F₁ F₂ : Y.Modules, RingedSpace.IsCoherent Y.toRingedSpace F₁ →
      IsIso (SheafOfModules.bidual (R := Y.sheaf) F₁) →
      RingedSpace.IsCoherent Y.toRingedSpace F₂ →
      IsIso (SheafOfModules.bidual (R := Y.sheaf) F₂) →
        Function.Bijective (fun f : F₁ ⟶ F₂ ↦ (restrictFunctor j).map f)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
