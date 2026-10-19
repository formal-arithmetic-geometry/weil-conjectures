/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.FiniteNormalClopenConstructibleModule
import Sheaf.AlgebraicGeometry.LisseTrivializedFiniteEtale
import Sheaf.AlgebraicGeometry.NormalConstantOpenImage
import Sheaf.AlgebraicGeometry.NormalizationExtendsCover
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension

/-!
# Constructibility of the direct image from a normal open

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-open-lisse-image`,
statement and both proof paragraphs (blueprint: lem-fin-normal-open-lisse-image).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite locally constant module sheaf on a nonempty normal open of an integral scheme
of finite type over a field has constructible direct image. The coefficient ring is finite
and commutative, as in the constructibility convention. `IsNormalScheme V` includes
integrality, hence nonemptiness, of `V`.

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-open-lisse-image`,
statement and both proof paragraphs (blueprint: lem-fin-normal-open-lisse-image).

Proof plan:
1. The field is Noetherian, so `X` is Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`, and its open `V` is Noetherian by
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`. A finite affine principal-open cover
   shows that `V` is of finite type. Choose a finite etale surjective trivializing cover
   `P → V` by `fin2-lem-lisse-trivialized-finite-etale`. Its finitely many clopen connected
   components `P_a` are nonempty normal integral by `lem-fin-etale-normal-components`, and
   the pullback of `L` on each is a constant finite module `M_a`.
2. The adjunction unit `L → p_* p^* L` is monic. After forgetting module structure it is
   the abelian unit by `lem-weil-pbc-module-direct-image-left-exact` and
   `lem-weil-pbc-module-abelian-inverse-image-comparison`. The finite stalk formula
   `lemma-weil-pbc-finite-stalk-formula` and the germ compatibility of
   `lem-weil-pbc-inverse-image-stalk-germ` identify it with the diagonal into a nonempty
   product of the same stalk. Use `lem-weil-pbc-geometric-stalks-detect-mono`.
3. Each component map `P_a → V` is surjective: its nonempty image is open by
   `lem-weil-pbc-etale-morphism-open-map` and closed by
   `lem-weil-pbc-finite-closed-map-finite-fibres`, while `V` is irreducible. Its generic
   fibre is a nonzero finite-dimensional domain over `K = k(X) = k(V)`, hence a field
   `K_a = k(P_a)` finite over `K`. On affine charts, surjectivity makes the kernel of
   the base ring map lie in the nilradical, and integrality makes it zero.
4. Normalize `X` in `K_a` using `def-fin-normalization-extension`. Its finite map
   `g_a : Y_a → X` extends `P_a → V` by `lem-fin-normalization-extends-cover` and
   `lem-fin-normalization-extension-finite`. The scheme `Y_a` is normal integral by
   `lem-weil-pbc-normalization-in-residue-field-extension`; its quasi-separatedness
   hypothesis follows from `lem-weil-pbc-locally-noetherian-quasi-separated`.
   Finiteness makes `Y_a` of finite type and therefore Noetherian.
5. By `lem-fin-normal-constant-open-image`, the constant sheaf `M_a` extends from
   `P_a` to the constant sheaf on `Y_a`. Composition of direct images, computed by
   fibre products as in `def-weil-pbc-direct-image`, and left exactness give an injection
   `k_* L → ∏_a g_{a,*} M_a`. Glue the constants on the finite disjoint union of the
   `Y_a` to a sheaf `E`; the displayed product is `g_* E` for the finite map `g`.
6. The finite clopen partition makes `E` constructible both in
   `def-weil-pbc-etale-constructible-sheaf` and in `def-constructible-constructible`.
   Its stalks are finite by `lem-weil-pbc-finite-locally-constant-module-values`.
   The representative descriptions in `lem-weil-pbc-filtered-colimit-sets-elementwise`
   and `lem-weil-pbc-filtered-colimit-modules-elementwise` identify the underlying sets
   of the module stalks with set stalks. Use `lem-galois-finite-stalks-comparison` for
   separably closed points, then `lem-weil-pbc-finite-pushforward-finite-stalk-module`
   to conclude that `g_* E` is constructible as a module sheaf.
7. Finally `lem-weil-pbc-constructible-subobjects-noetherian` applied to the injection
   into `g_* E` gives the asserted constructibility of `k_* L`. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open
    {K : Type u} [Field K] {X V : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [IsIntegral X] (k : V ⟶ X) [IsOpenImmersion k] (hV : IsNormalScheme V)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf L] :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) k).obj L) := by
  sorry

end AlgebraicGeometry.Scheme
