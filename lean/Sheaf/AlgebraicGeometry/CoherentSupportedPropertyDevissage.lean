/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed

/-! # Coherent property devissage with an arbitrary support subset

Source: Stacks Project, Cohomology of Schemes, Tags 01YG and 01YH,
labels `lemma-property-initial` and `lemma-property-irreducible`;
the supported finite-filtration argument
(blueprint: lem-pc-coherent-supported-property-devissage).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- An extension-closed, isomorphism-invariant property containing zero holds for all
coherent modules supported in an arbitrary subset `S` if it holds for pushforwards of
nonzero quasi-coherent ideals on every integral closed subscheme with image in `S`.
The ideal data `J : W.IdealSheafData` encode precisely quasi-coherent ideals, and
`J.toModules` is the corresponding ideal module. Support is nonvanishing of stalks,
not the zero locus `IdealSheafData.support`.

Source: Stacks Project, Cohomology of Schemes, Tag 01YG, `lemma-property-initial`,
and Tag 01YH, `lemma-property-irreducible`, supported filtration paragraphs
(blueprint: lem-pc-coherent-supported-property-devissage).

Proof:
1. For coherent F supported in S, apply
   lem-weil-pbc-coherent-filtration-integral-subschemes to obtain a finite coherent
   filtration starting at zero and ending at F, with quotients isomorphic to i_*I for
   integral closed immersions i and nonzero coherent ideals I. The quotients are coherent
   by lem-weil-pbc-coherent-modules-kernel-cokernel-sum. Length zero is allowed.
2. At every point outside S the stalk of F vanishes. Exactness of stalks
   (lem-weil-pbc-module-stalk-exact) gives vanishing of the stalks of all filtration terms
   and their quotients. Stalk isomorphisms also put the supports of i_*I in S.
3. Each integral source is locally Noetherian by pqf-lem-locnoeth-lft, since closed
   immersions are locally of finite type (def-weil-closed-immersion). The coherent ideal
   is quasi-coherent by pqf-lem-coherent-ft-locnoeth. Its generic stalk is nonzero by
   lem-weil-pbc-integral-scheme-ideal-generic-stalk. Hence the image of the generic point
   lies in the quotient support, by lem-weil-pbc-closed-pushforward-stalks. This support
   is closed by lem-weil-pbc-finite-type-module-support-closed and
   pqf-lem-coherent-ft-locnoeth. It contains the closure of that point, which is the whole
   integral closed image. The pushforward stalks vanish off the image, so its support
   equals that image and the image lies in S. The ideal hypothesis and isomorphism
   invariance now give the property for each quotient.
4. Induct along the filtration, starting with the assumed property of zero. The extension
   hypothesis gives the property for each next coherent term, since both end terms have
   it and all three supports lie in S. The last term gives the claim. This covers F = 0,
   the empty subset and the empty scheme without requiring an integral subscheme. -/
theorem coherent_supported_property_devissage
    (X : Scheme.{u}) [IsNoetherian X] (S : Set X) (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (hP_iso : ∀ (F G : X.Modules) (_e : F ≅ G),
      RingedSpace.IsCoherent X.toRingedSpace F →
      RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ S →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ S → P F → P G)
    (hP_extension : ∀ T : ShortComplex X.Modules, T.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace T.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace T.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace T.X₃ →
      {x : X | ¬ Subsingleton (T.X₁.presheaf.stalk x)} ⊆ S →
      {x : X | ¬ Subsingleton (T.X₂.presheaf.stalk x)} ⊆ S →
      {x : X | ¬ Subsingleton (T.X₃.presheaf.stalk x)} ⊆ S →
      P T.X₁ → P T.X₃ → P T.X₂)
    (hP_integral : ∀ (W : Scheme.{u}) (j : W ⟶ X),
      IsClosedImmersion j → IsIntegral W → Set.range j.base ⊆ S →
      ∀ J : W.IdealSheafData, J ≠ ⊥ → P ((pushforward j).obj J.toModules)) :
    ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F →
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ S → P F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
