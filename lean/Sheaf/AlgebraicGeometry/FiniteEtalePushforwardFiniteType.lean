/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Finite etale direct image of locally constant finite-type module sheaves

Source: Stacks Project, Etale Cohomology, Tag 095B,
`lemma-pushforward-locally-constant`, module-sheaf finite-type clause
(blueprint: lem-per-finite-etale-pushforward-finite-type).

The coefficient category is `ModuleCat`, the fixed-coefficient presentation of modules
on the constant ring sheaf. In `IsFiniteLocallyConstantSheaf`, finite means finitely
generated geometric stalks, not finite underlying sets. Together with local constancy,
this is precisely local triviality with finitely generated module values, as exposed by
`def-weil-pbc-locally-constant-finite-type-modules` for the small etale site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Direct image under a finite etale morphism preserves local constancy of finite type
for module sheaves over an arbitrary commutative coefficient ring.

Source: Stacks Project, Etale Cohomology, Tag 095B,
`lemma-pushforward-locally-constant`, statement and proof, module clause
(blueprint: lem-per-finite-etale-pushforward-finite-type).

Proof (the six steps of the node):
1. At every point of the base apply `lem-weil-pbc-finite-etale-etale-local-split`.
   The resulting etale neighbourhoods cover the base and split the pullback into
   finitely many clopen sheets, each isomorphic to the neighbourhood. Their number
   may vary with the neighbourhood.
2. Direct image commutes with this etale localization: on an etale test object `W`,
   both sides evaluate `F` on the same fibre product, up to the natural isomorphism
   `W ×_U (Y ×_X U) ≅ W ×_X Y`. Its inverse inserts the image in `U`.
   These identifications commute with restriction and are coefficient-linear.
   Use `def-weil-pbc-direct-image`, `def-pur-localized-ringed-site`,
   `lem-weil-pbc-etale-base-change-finite-limits`, and `def-pc-fibre-product`.
3. Apply `lem-weil-pbc-direct-image-split-cover-product`: on each neighbourhood the
   direct image is the product of the restrictions to its finitely many sheets,
   with the empty product equal to the zero module sheaf.
4. Each sheet restriction is locally constant of finite type. On any etale test
   object take a common refinement of the finitely many trivializing covers by
   iterated fibre products. Localizations and etale composition preserve these
   covers (`def-pur-localized-ringed-site`, `def-weil-pbc-etale-site`, and
   `lem-weil-pbc-etale-composition-cancellation`). Constant module values stay
   constant on refinement by `lemma-constructible-pullback-constant`.
5. A finite product of constant module presheaves is the constant presheaf of the
   product module. Finite-limit preservation of sheafification gives the same
   assertion for the constant sheaves, including the empty product. Use
   `def-weil-pbc-constant-sheaf` and
   `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`.
6. A finite product of finitely generated modules is finitely generated: the
   coordinate vectors from finite generating sets form a finite generating set.
   The empty family generates the zero module. Compose the trivializing covers
   with those in step 1 to obtain the defining local trivializations of the direct
   image (`def-weil-pbc-locally-constant-finite-type-modules` and
   `def-weil-finitely-generated-module`). For an empty base use the empty cover.
   No Noetherian property or finiteness of underlying coefficient sets is used. -/
theorem isFiniteLocallyConstantSheaf_lowerStar_of_isFinite_etale
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} R) f).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
