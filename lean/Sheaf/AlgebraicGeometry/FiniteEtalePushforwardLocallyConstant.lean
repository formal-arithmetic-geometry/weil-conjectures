/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.Paper.DirectImageSplitCoverProduct
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite etale pushforward of finite locally constant module sheaves

Source: Stacks Project, Tag 095B, Lemma 59.64.3, module clause
(blueprint: lem-weil-pbc-etale-finite-pushforward-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Direct image along a finite etale morphism preserves finite locally constant sheaves
of modules over a finite commutative ring. The finite-local-constancy predicate agrees
with local trivializations by finite modules by `finite_locally_constant_module_values_iff`.

Proof, following Stacks 095B and the node's six steps:
1. Finite local constancy is invariant under isomorphism and local for etale coverings:
   transport trivializations through an isomorphism, or compose the trivializing covers
   with the given cover (`lem-weil-pbc-finite-locally-constant-module-values`).
2. Etale restriction preserves finite local constancy: inverse image preserves local
   constancy (`lemma-constructible-pullback-locally-constant`), and its geometric stalk is
   the original stalk (`lem-weil-pbc-inverse-image-stalk-germ`). Restriction agrees with
   inverse image (`lem-weil-pbc-etale-inverse-image-restriction`); naturality at scalar
   multiplication makes this identification module-linear.
3. Direct image commutes with etale localization. On each test object, cartesian-square
   pasting (`lem-weil-pbc-cartesian-square-pasting`) identifies the two iterated fibre
   products naturally, hence gives an isomorphism of module sheaves.
4. A finite etale morphism splits over an etale cover into finitely many sheets, each
   isomorphic to the base (`lem-weil-pbc-finite-etale-etale-local-split`, Stacks 04HN).
5. On that cover, direct image is the product of restrictions to the sheets
   (`lem-weil-pbc-direct-image-split-cover-product`). Each restriction is finite locally
   constant by step 2. A finite nonempty product is a finite biproduct, hence finite
   locally constant (`lemma-constructible-flc-biproduct`). For no sheets it is the zero
   sheaf, trivialized by the identity cover with the finite zero module.
6. Apply step 3 and isomorphism invariance to obtain finite local constancy on the cover,
   then descend by the locality in step 1.

Source: Stacks Project, Tag 095B, Lemma 59.64.3, module clause and proof
(blueprint: lem-weil-pbc-etale-finite-pushforward-locally-constant). -/
theorem finiteLocallyConstant_lowerStar_of_finite_etale
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
