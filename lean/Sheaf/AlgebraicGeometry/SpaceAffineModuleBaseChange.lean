/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
public import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange

import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-! # Arbitrary base change for affine algebraic-space module direct images

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 07U8,
lemma-affine-base-change, ordinary degree zero
(blueprint: lem-sfb-space-affine-module-base-change).

The existing natural transformation `moduleBaseChange` is the adjoint of the
tensor-composition comparison followed by pullback of the specified counit.
The theorem uses an arbitrary sheaf pullback square of algebraic spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine direct image preserves quasi-coherence and its canonical base-change
map is invertible for every base morphism. `hf` states representability and `ha`
states exactly the affine-scheme tests of the node. The sheaf pullback square
retains both projections; its commutativity supplies the tensor comparison.
Naturality in `F` is built into the existing transformation `moduleBaseChange`.
No flatness or finiteness hypotheses are imposed on `g` or `F`.

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 07U8,
lemma-affine-base-change and equation-base-change-diagram; Cohomology of Schemes,
Tag 02KG (blueprint: lem-sfb-space-affine-module-base-change).

Proof:
1. On an affine etale chart V of Y, the pullback U of X is an affine scheme.
   Restrict F to E on U. Etale direct-image restriction identifies the image on V
   with p_* E. Affine morphism permanence makes p quasi-compact and separated.
   Scheme Zariski/etale quasi-coherent equivalence and affine scheme pushforward
   show that this image is quasi-coherent. Its local presentations on the covering
   charts give quasi-coherence of f_* F.
2. Pull the affine etale covering V_i of Y back to Y', and cover each pullback by
   affine etale schemes V'_{ij}. Fibre products and chartwise etale permanence give
   a covering of Y'. The spaces U_i and U_i times_{V_i} V'_{ij} are affine schemes
   by affine base-change permanence. No scheme assumption on Y' is needed.
3. Etale direct-image restriction and tensor composition identify the restriction
   of the source and target of moduleBaseChange with a^* p_* E and p'_* b^* E.
   Pullback preserves quasi-coherence. The scheme Zariski/etale equivalence,
   including its direct-image comparisons for the affine p and p', identifies
   these with the corresponding Zariski module objects.
4. Check the map: chart tensor realization gives the unit m to 1 tensor m and
   the counit c tensor m to c times the restricted m. Tensor composition multiplies
   the two coefficients. Direct-image restriction fixes sections. Therefore, for
   V = Spec R, U = Spec B and V' = Spec R', the restricted mate is
   R' tensor_R M to (R' tensor_R B) tensor_B M,
   sending r' tensor m to (r' tensor 1) tensor m. The Zariski/etale functor
   comparison square preserves these units and counits, so this is the precise
   canonical map of the affine scheme base-change theorem.
5. Scheme affine pushforward/base change makes this map invertible: its inverse
   sends (r' tensor b) tensor m to r' tensor bm. These formulas are balanced and
   have identity composites on pure tensors. Thus the restricted maps are
   isomorphisms on the covering of Y'. Their inverses agree on overlaps and glue
   uniquely by the sheaf axiom. The tensor formulas commute with module maps,
   giving the stated canonical natural comparison for arbitrary g and F. -/
theorem affine_moduleDirectImage_baseChange
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : IsRepresentable f.hom.hom) (ha : MapIsAffine f)
    (sq : IsPullback h.hom f'.hom f.hom g.hom)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((moduleDirectImage f).obj F).IsQuasicoherent ∧
      IsIso ((moduleBaseChange f g h f' (ObjectProperty.hom_ext _ sq.w)).app F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
