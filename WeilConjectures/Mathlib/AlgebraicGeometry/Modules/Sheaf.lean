/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Kernels
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens
public import WeilConjectures.Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.Mathlib.Topology.Sheaves.Stalks

/-!
# Sections, stalks, restrictions and fibres of `𝒪_X`-modules

This file collects eleven groups of results about sheaves of modules over a scheme.

The first is a concrete description of the sections of a categorical kernel. Limits in
`X.Modules` are computed section-wise, because evaluation at an open subset preserves finite
limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`): over any open `U`, the sections
of `kernel f` are exactly the sections of the source that `f` kills. This is the tool that turns
a sheaf of modules defined as a kernel — as the ideal sheaf of a `Scheme.IdealSheafData` is in
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` — into a computable object.

The second transports the module structure on the stalk of a presheaf of modules
(`PresheafOfModules.instModule`) to `X.Modules`: the stalk `F_x` of a sheaf of `𝒪_X`-modules is a
module over the local ring `𝒪_{X, x}`, and, for `x` in an open `U`, over `Γ(X, U)` by restriction
of scalars along the germ map. Taking stalks at a fixed point is a left exact functor
`X.Modules ⥤ ModuleCat 𝒪_{X, x}`, and it **detects isomorphisms**: a morphism of sheaves of
modules which is an isomorphism on every stalk is an isomorphism. This is the criterion that
`Scheme.Modules.Hom.isIso_iff_isIso_app` cannot replace, since the latter quantifies over all
opens, including the non-affine ones over which sections are not computable. This group also
records that **restriction along an open immersion does not change stalks**: Mathlib's comparison
`restrictStalkNatIso` is semilinear over the stalk map of the immersion, so an isomorphism between
the restrictions of two sheaves of modules to an open subscheme identifies their stalks as modules
over the local ring of the *ambient* scheme.

The third compares the pushforward and pullback functors along `f : X ⟶ Y` with restriction to
open subsets: restricting `f _* M` to an open `U` of `Y` is the pushforward of the restriction of
`M` to `f ⁻¹ᵁ U` along `f ∣_ U`, the pullback of `𝒪_Y` is `𝒪_X`, and the pullback commutes with
restricting to an open `U` of `Y` and to its preimage. The latter is packaged as a functor
`Scheme.Modules.pullbackOver` between the categories of modules over the restricted structure
sheaves, which is what quasi-coherence and finite type are formulated in terms of. This group
also records the dictionary between sheaves of modules over `𝒪_X` restricted to the site of opens
contained in `U` and sheaves of `𝒪_X|_U`-modules on the scheme `U`.

The fourth is the **fibre `F(x)` of a sheaf of modules at a point**, as a vector space over the
residue field `κ(x)`, together with the **restriction `F_y` of a sheaf of modules to a fibre of a
morphism** and the **global sections `Γ(X_y, F_y)` on a fibre**. Since Mathlib has no module
structure on the stalk of a sheaf of modules, the fibre is
defined not as `F_x ⊗_{𝒪_{X,x}} κ(x)` but by pullback: `F(x)` is the module of global sections
of the pullback of `F` along `Spec κ(x) ⟶ X`. The two agree for quasi-coherent `F`. It is built on
a base change section, comparing global sections on `Spec S` with global sections on `Spec R`
after restriction of scalars along `φ : R ⟶ S`.

The fifth is **base change for the direct image**: for a commutative square `v ≫ f = g ≫ u` of
schemes, the pullbacks along the two sides are compared by an isomorphism `g^* u^* ≅ v^* f^*`,
and the mate of that comparison is the base change transformation `u^* f_* ⟶ g_* v^*`. Applied
to the fibre square of `f : X ⟶ Y` over `y : Y` and evaluated on global sections, this is the
base change map `(f_* F)(y) ⟶ Γ(X_y, F_y)`.

The sixth is the `R`-module structure on the global sections of a sheaf of modules on a scheme
`X` over `Spec R`, by restriction of scalars along the structure map `R → Γ(X, 𝒪ₓ)`, and the
computation of `h⁰(X, 𝒪ₓ)` when that structure map is an isomorphism.

The seventh concerns a scheme `X` **with at most one point**, such as the spectrum of a field. The
only open subsets of such an `X` are `⊥` and `⊤`, and all sections over `⊥` vanish, so a morphism
of `𝒪ₓ`-modules is an isomorphism as soon as it is one on global sections. In particular a global
section `m` of `M` such that `r ↦ r • m` is bijective trivialises `M`.

The eighth is the **vanishing of a global section at a point**, meaning that its germ there lies
in `𝔪ₓ Fₓ`. The global sections vanishing at a fixed point form a `Γ(X, 𝒪ₓ)`-submodule of
`Γ(X, F)`, and Nakayama's lemma makes it a *proper* submodule as soon as `F` is generated by its
global sections at `x` and `Fₓ` is a non-zero finite `𝒪_{X, x}`-module. Both hypotheses hold for
the structure sheaf, whose stalk is generated by the germ of the unit section, and there vanishing
at `x` means exactly that `x` lies outside the basic open subset of the function. Generation by
global sections at a point follows from the global statement `SheafOfModules.IsGloballyGenerated`:
every element of a stalk is the germ of a linear combination of restrictions of global sections,
and taking germs turns such a combination into a linear combination over the local ring. The germ
of the unit section is in fact a basis of the stalk of the structure sheaf, so that stalk is the
local ring itself, and in particular a flat module over it.

The ninth is the **epimorphism criterion**. An epimorphism of sheaves is not a section-wise
surjection but a *locally* surjective morphism, so a morphism of sheaves of `𝒪_X`-modules is an
epimorphism as soon as it is surjective on the sections over every affine open subset, the affine
opens being a basis. The motivating example is the comparison morphism `𝒪_X ⟶ g_* 𝒪_Y` of a
closed immersion `g : Y ⟶ X`: it is surjective over an affine open and almost never over a
general one, and being an epimorphism is exactly what makes `g_* 𝒪_Y` the quotient of `𝒪_X` by
the ideal sheaf of `Y`, so that a morphism out of `𝒪_X` killing that ideal descends to `g_* 𝒪_Y`.
That `𝒪_X ⟶ g_* 𝒪_Y` is an epimorphism for a closed immersion `g` is proved in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, which is where the
surjectivity over an affine open subset lives.

The tenth is the **pullback of the morphism attached to a global section**. A global section `m`
of `M` is a morphism `𝒪ₓ ⟶ M` (`AlgebraicGeometry.Scheme.Modules.homOfSectionTop`), and pulling
that morphism back along `a : X ⟶ Y` is multiplication by the pulled back section, under the
identification `a^* 𝒪ᵧ ≅ 𝒪ₓ`. Over a fixed base the same holds for the pullback of sections
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver`, and this is what transports the
non-vanishing of a section to a fibre.

The eleventh is the **restriction to a fibre of a section taken over an open neighbourhood of the
base point**. A section of `f _* F` over an open neighbourhood `V` of `y` is a section of `F` over
`f ⁻¹ᵁ V`, that is a *global* section of the restriction of `F` to the open subscheme `f ⁻¹ᵁ V`,
and restricting it to the fibre `X_y` factors through that restriction, along the morphism
`AlgebraicGeometry.Scheme.Hom.fiberLift` from the fibre to `f ⁻¹ᵁ V`. In particular the
restriction to the fibre does not depend on the neighbourhood the section is taken over.

## Main definitions

- `AlgebraicGeometry.Scheme.structureModules`: the structure sheaf of a scheme, as a sheaf of
  modules over itself.
- `AlgebraicGeometry.Scheme.freeModules`: the free sheaf of `𝒪_X`-modules on a type, that is a
  direct sum of copies of the structure sheaf.
- `AlgebraicGeometry.Scheme.freeModulesCofan` and
  `AlgebraicGeometry.Scheme.isColimitFreeModulesCofan`: `X.freeModules ι` is the coproduct of
  copies of `𝒪ₓ` indexed by `ι`, in the category `X.Modules`.
- `AlgebraicGeometry.Scheme.Modules.isColimitMapFreeModulesCofan`: `g_* (𝒪_Y^ι)` is the
  coproduct of `ι` copies of `g_* 𝒪_Y`, and
  `AlgebraicGeometry.Scheme.Modules.pushforwardFreeDesc`: the morphism
  `g_* (𝒪_Y^ι) ⟶ P` assembled from a family of morphisms `g_* 𝒪_Y ⟶ P`, with
  `AlgebraicGeometry.Scheme.Modules.pushforwardFree_hom_ext` and
  `AlgebraicGeometry.Scheme.Modules.eq_pushforwardFreeDesc` determining it.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctor`, `AlgebraicGeometry.Scheme.Modules.fiber`: the
  fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space, and its
  functoriality `AlgebraicGeometry.Scheme.Modules.fiberMap` in `F`.
- `AlgebraicGeometry.Scheme.Modules.restrictToFiber`: the restriction `F ↦ F_y` of sheaves of
  modules to the scheme-theoretic fibre of a morphism over a point, and
  `AlgebraicGeometry.Scheme.Modules.fiberSectionsOfNhds`, the restriction to `X_y` of a section
  of `f_* F` over an open neighbourhood of `y`.
- `AlgebraicGeometry.Scheme.Modules.sectionsOfNhds`: a section of `f_* F` over an open
  neighbourhood `V` of `y`, read as a global section of the restriction of `F` to the open
  subscheme `f ⁻¹ᵁ V`; `AlgebraicGeometry.Scheme.Modules.sectionsOfNhds_comp_sectionsPullbackOver`
  factors `fiberSectionsOfNhds` through it.
- `AlgebraicGeometry.Scheme.Modules.fiberSectionsFunctor`,
  `AlgebraicGeometry.Scheme.Modules.fiberSections`: the global sections `Γ(X_y, F_y)` on the
  scheme-theoretic fibre, as a `κ(y)`-vector space.
- `AlgebraicGeometry.Scheme.Modules.moduleStalkBase`: the module structure on a stalk of a sheaf
  of `𝒪_X`-modules over the local ring of the base of a morphism `f : X ⟶ Y`.
- `AlgebraicGeometry.Scheme.Modules.stalkFunctor`, `AlgebraicGeometry.Scheme.Modules.Hom.stalkMap`:
  the stalk of a sheaf of `𝒪_X`-modules at a point, as a functor to `𝒪_{X, x}`-modules, and the
  map it induces on stalks.
- `AlgebraicGeometry.Scheme.Modules.restrictStalkEquiv`,
  `AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfRestrictIso`: the comparison of stalks
  under restriction along an open immersion, and the resulting identification of the stalks of
  two sheaves of modules which agree on a neighbourhood of a point.
- `AlgebraicGeometry.Scheme.Modules.stalkStructureModulesLinearEquiv`: the stalk of the structure
  sheaf, viewed as a sheaf of modules over itself, is the local ring.
- `AlgebraicGeometry.Scheme.Modules.pullbackSectionIso`: pulling a sheaf of modules back along a
  morphism and then along a section of it gives back the sheaf.
- `AlgebraicGeometry.Scheme.Modules.pullbackTwoSquare`,
  `AlgebraicGeometry.Scheme.Modules.baseChange`: the comparison of pullbacks around a commutative
  square of schemes, and its mate, the base change transformation `u^* f_* ⟶ g_* v^*`.
- `AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap`: **the base change map**
  `(f_* F)(y) ⟶ Γ(X_y, F_y)`, the specialisation of `baseChange` to a fibre square, on global
  sections.
- `AlgebraicGeometry.Scheme.Modules.sectionsEquivOfIso`: an isomorphism of sheaves of modules
  identifies their sections over any open subset.
- `AlgebraicGeometry.Scheme.Modules.sectionsBaseEquivOfIso`: an isomorphism of sheaves of modules
  on a scheme over `Spec R` identifies their global sections as `R`-modules.
- `AlgebraicGeometry.Scheme.Modules.sectionsUnitEquiv`: the global functions of `X` are free of
  rank one over the base ring, when the structure morphism identifies the two.
- `AlgebraicGeometry.Scheme.Modules.fiberMk`: the image `s(x) ∈ F(x)` of a global section `s` of
  `F` in the fibre at `x`, as a map semilinear over the evaluation `Γ(X, 𝒪_X) ⟶ κ(x)`.
- `AlgebraicGeometry.Scheme.Modules.homOfSectionTop`: the morphism `𝒪ₓ ⟶ M` determined by a global
  section of `M`.
- `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`: the bijection between morphisms
  `𝒪ₓ ⟶ M` and global sections of `M`, and
  `AlgebraicGeometry.Scheme.Modules.sectionsEquivTop`, the identification of the compatible
  families of sections of `M` with `Γ(M, ⊤)`.
- `AlgebraicGeometry.Scheme.Modules.endSection`: the global function attached to an
  endomorphism of the structure sheaf.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctorRestrictIso`: the fibre at a point of an open
  subscheme of a restricted sheaf of modules, as the fibre of the sheaf itself.
- `AlgebraicGeometry.Scheme.Modules.module_sections`: the `R`-module structure on `Γ(X, F)` for a
  scheme `X` over `Spec R`.
- `AlgebraicGeometry.Scheme.Modules.VanishesAt`: a global section vanishes at a point.
- `AlgebraicGeometry.Scheme.Modules.vanishingSubmodule`: the global sections vanishing at a point,
  as a `Γ(X, 𝒪ₓ)`-submodule of `Γ(X, F)`.
- `AlgebraicGeometry.Scheme.Modules.IsGloballyGeneratedAt`: the germs at a point of the global
  sections span the stalk there.
- `AlgebraicGeometry.Scheme.Modules.oneSection`: the unit function of `X`, as a section of the
  structure sheaf viewed as a sheaf of modules.
- `AlgebraicGeometry.Scheme.Hom.toPushforwardStructure`: the comparison morphism
  `𝒪_X ⟶ g_* 𝒪_Y` of `𝒪_X`-modules attached to a morphism of schemes `g : Y ⟶ X`, and
  `AlgebraicGeometry.Scheme.Hom.descPushforwardStructure`, the descent of a morphism out of
  `𝒪_X` through it when the comparison morphism is an epimorphism.

## Main results

- `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_stalkMap`,
  `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_stalkMap`: **a morphism of sheaves of
  `𝒪_X`-modules is an isomorphism exactly when it is one on every stalk.**
- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`,
  `AlgebraicGeometry.Scheme.Modules.range_stalkMap_kernelι`: the sections, respectively the germs,
  of a kernel are the sections, respectively the germs, killed by the morphism.
- `AlgebraicGeometry.Scheme.Modules.Hom.range_stalkMap`: the germs in the image of a morphism
  are the germs of the sections in its image.
- `AlgebraicGeometry.Scheme.Modules.germₗ`, `AlgebraicGeometry.Scheme.Modules.germₛₗ`: the germ
  map `Γ(F, U) →ₗ[Γ(X, U)] F_x`, and its variant semilinear over the germ map on functions.
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompRestrictFunctorIso`
- `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompMorphismRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.overEquivInverseRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`: the pullback of a free sheaf is free,
  compatibly with `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` on each summand.
- `AlgebraicGeometry.Scheme.Modules.pullbackOver`
- `AlgebraicGeometry.Scheme.Modules.pullbackOverObjIso`
- `AlgebraicGeometry.Scheme.Modules.Hom.naturality`: a morphism of sheaves of modules commutes
  with the restriction maps.
- `AlgebraicGeometry.Scheme.Modules.sectionsPullback_naturality`: the pullback
  `Γ(N, ⊤) ⟶ Γ(a^* N, ⊤)` of global sections along `a : X ⟶ Y` is natural in `N`.
- `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`: the pullback functors along a commuting
  triangle `h ≫ v = u`, namely `v^* ⋙ h^* ≅ u^*`, together with its compatibility
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle_hom_app_sectionsPullback` with the pullback
  of global sections and its compatibility
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle_comp_hom` with stacking two triangles.
- `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPushforwardIso`,
  `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPullbackIso`: base change of the global sections
  of a sheaf of modules on `Spec S` along `φ : R ⟶ S`.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctorPullbackIso`,
  `AlgebraicGeometry.Scheme.Modules.fiberPullbackIso`: compatibility of the fibre with pullback,
  for a morphism `u` inducing an isomorphism on residue fields at the point in question.
- `AlgebraicGeometry.Scheme.Modules.fiberRestrictToFiberIso`: the fibre of `F_y` at a point `x`
  of the fibre is the fibre of `F` at `f.fiberι y x`.
- `AlgebraicGeometry.Scheme.Modules.map_baseChange_comp_counit`: the mate identity satisfied by
  the base change transformation.
- `AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap_naturality`: naturality of the base change
  map in the sheaf.
- `AlgebraicGeometry.Scheme.Modules.app_pullbackUnitIso_hom_sectionsPullback`: the pullback of
  global sections of the structure sheaf along `a : X ⟶ Y` is the map on global functions.
- `AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop` and
  `AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop_over`: the pullback of multiplication by a
  global section, absolutely or over a base, is multiplication by the pulled back section; with
  `AlgebraicGeometry.Scheme.Modules.homOfSectionTop_comp` and
  `AlgebraicGeometry.Scheme.Modules.fiberMap_homOfSectionTop_eq_zero_iff_over`.
- `AlgebraicGeometry.Scheme.Modules.surjective_sectionsPullback_of_iso_structureModules` and
  `AlgebraicGeometry.Scheme.Modules.surjective_sectionsPullbackOver_of_iso_structureModules`:
  pulling back the global sections of a *trivial* sheaf of modules, absolutely or over a base,
  is as surjective as pulling back functions.
- `AlgebraicGeometry.Scheme.Modules.fiberMk_unit_eq_zero_iff`: the fibre of the structure sheaf
  at `x` is the residue field `κ(x)`, so a global function has zero image in it exactly when it
  vanishes at `x`.
- `AlgebraicGeometry.Scheme.Modules.finrank_sections_unit_eq_one`: `h⁰(X, 𝒪ₓ) = 1` for a scheme
  whose structure morphism identifies the base ring `R` with `Γ(X, 𝒪ₓ)`.
- `AlgebraicGeometry.Scheme.Modules.isGloballyGenerated_of_forall_exists_mem_span`: **a family
  of global sections whose restrictions span the sections of `M` locally generates `M`**.
- `AlgebraicGeometry.Scheme.Modules.isGloballyGeneratedAt_of_isGloballyGenerated`: **a sheaf of
  modules generated by its global sections is generated by them at every point**, together with
  the intermediate `AlgebraicGeometry.Scheme.Modules.exists_mem_span_germ_eq`.
- `AlgebraicGeometry.Scheme.Modules.exists_not_vanishesAt`: **Nakayama's lemma in the form of a
  non-vanishing section** — a sheaf of modules generated by its global sections at `x`, with
  non-zero finite stalk there, has a global section which does not vanish at `x`.
- `AlgebraicGeometry.Scheme.Modules.isGloballyGeneratedAt_structureModules`,
  `AlgebraicGeometry.Scheme.Modules.vanishesAt_structureModules_iff`: the structure sheaf is
  generated by its global sections at every point, and a global function vanishes at `x` exactly
  when `x` is outside its basic open subset.
- `AlgebraicGeometry.Scheme.Modules.fiberMap_ne_zero_of_isIso`: an isomorphism is non-zero on
  every non-trivial fibre.
- `AlgebraicGeometry.Scheme.Modules.fiberMap_restrictFunctor_map_eq_zero_iff`: a morphism of
  sheaves of modules vanishes on the fibre at a point of an open subscheme exactly when its
  restriction to that open subscheme does.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_isIso_app` and
  `AlgebraicGeometry.Scheme.Modules.isIso_of_isOpenCover_restrict`: a morphism of sheaves of
  modules which is invertible on sections over every small enough open subset is an isomorphism,
  and being an isomorphism is local on the base; with the additive companions
  `AlgebraicGeometry.Scheme.Modules.eq_zero_of_forall_exists_app_eq_zero` and
  `AlgebraicGeometry.Scheme.Modules.eq_zero_of_isOpenCover_restrict`.
- `AlgebraicGeometry.Scheme.Modules.Hom.app_eq_smul_res` and
  `AlgebraicGeometry.Scheme.Modules.endSectionRingEquiv`: a morphism `𝒪ₓ ⟶ M` is multiplication
  by a global section of `M`, and the endomorphism ring of `𝒪ₓ` is the ring `Γ(X, 𝒪ₓ)` of global
  functions; `AlgebraicGeometry.Scheme.Modules.isIso_iff_isUnit_endSection` reads off when such
  an endomorphism is an isomorphism.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app_top`,
  `AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop`: on a scheme with at most one point, a
  morphism of `𝒪ₓ`-modules which is an isomorphism on global sections is an isomorphism, and a
  generating global section trivialises the module.

- `AlgebraicGeometry.Scheme.Modules.epi_iff_isLocallySurjective` and
  `AlgebraicGeometry.Scheme.Modules.epi_iff_surjective_stalkMap`: **a morphism of sheaves of
  `𝒪_X`-modules is an epimorphism exactly when it is locally surjective**, equivalently when it
  is surjective on every stalk; `AlgebraicGeometry.Scheme.Modules.epi_of_surjective_app` is the
  sufficient criterion that surjectivity over every affine open subset gives.
- `AlgebraicGeometry.Scheme.Hom.toPushforwardStructure_descPushforwardStructure` and
  `AlgebraicGeometry.Scheme.Hom.eq_descPushforwardStructure`: the universal property of
  `𝒪_X ⟶ g_* 𝒪_Y` when that morphism is an epimorphism — a morphism out of `𝒪_X` killing its
  kernel factors through it, uniquely — together with
  `AlgebraicGeometry.Scheme.Hom.shortExact_kernelSequence_toPushforwardStructure`, which packages
  it as the short exact sequence `0 ⟶ ker (𝒪_X ⟶ g_* 𝒪_Y) ⟶ 𝒪_X ⟶ g_* 𝒪_Y ⟶ 0`, and
  `AlgebraicGeometry.Scheme.Hom.kernelι_toPushforwardStructure_comp_eq_zero_iff`, which reads
  the hypothesis section-wise: killing the kernel means killing every function vanishing on `Y`.

## Blueprint

The fibre and the restriction to a fibre are notion **(N2)** of `sec:cube-cost`, the formalisation
count of the theorem-of-the-cube chapter. The remaining half of (N2) — the compatibility of the
fibre with tensor products and with inverses of line bundles, and the one-dimensionality of the
fibre of an invertible sheaf — is in `WeilConjectures.AlgebraicGeometry.Modules.Fiber`: it needs
the monoidal structure on sheaves of modules and the notion of an invertible sheaf, which a file
under `WeilConjectures/Mathlib/` may not import.
-/
@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry

/-- The structure sheaf `𝒪_X` of a scheme `X`, as a sheaf of modules over itself: the tensor
unit of `X.Modules`.

The abbreviation is needed because dot notation on `SheafOfModules.unit X.ringCatSheaf`
resolves in `SheafOfModules _` rather than in `X.Modules`. -/
noncomputable abbrev Scheme.structureModules (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The free sheaf of `𝒪_X`-modules on a type `ι`, that is a direct sum of copies of `𝒪_X`
indexed by `ι`.

As for `AlgebraicGeometry.Scheme.structureModules`, the abbreviation is needed because dot
notation on `SheafOfModules.free ι` resolves in `SheafOfModules _` rather than in
`X.Modules`. -/
noncomputable abbrev Scheme.freeModules (X : Scheme.{u}) (ι : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) ι

/-- The tautological cofan exhibiting `X.freeModules ι` as the coproduct of copies of `𝒪ₓ`
indexed by `ι`, in the category `X.Modules`.

This is Mathlib's `SheafOfModules.freeCofan`, taken in `X.Modules` rather than in
`SheafOfModules X.ringCatSheaf`. It typechecks because `AlgebraicGeometry.Scheme.Modules`
unfolds to `SheafOfModules X.ringCatSheaf`; downstream proofs should go through
`AlgebraicGeometry.Scheme.freeModulesCofan_inj` rather than rely on that unfolding
themselves. -/
noncomputable def Scheme.freeModulesCofan (X : Scheme.{u}) (ι : Type u) :
    Cofan (fun _ : ι ↦ X.structureModules) :=
  Cofan.mk (X.freeModules ι) SheafOfModules.ιFree

@[simp]
lemma Scheme.freeModulesCofan_inj (X : Scheme.{u}) (ι : Type u) (j : ι) :
    (X.freeModulesCofan ι).inj j = SheafOfModules.ιFree j :=
  rfl

/-- **The free sheaf of modules on `ι` is the coproduct of copies of `𝒪ₓ`.** -/
noncomputable def Scheme.isColimitFreeModulesCofan (X : Scheme.{u}) (ι : Type u) :
    IsColimit (X.freeModulesCofan ι) :=
  SheafOfModules.isColimitFreeCofan ι

instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The `j`-th inclusion into the biproduct `⨁ (fun _ : ι ↦ 𝒪ₓ)`, read through the comparison
with the coproduct, is `SheafOfModules.ιFree j`.**

Like `AlgebraicGeometry.Scheme.freeModulesCofan_inj` this is a place where the unfolding
`X.freeModules ι = ∐ (fun _ ↦ 𝒪ₓ)` is used; downstream proofs should go through it rather than
rely on that unfolding themselves. -/
@[reassoc (attr := simp)]
lemma Scheme.biproduct_ι_comp_isoCoproduct_hom (X : Scheme.{u}) (ι : Type u) [Finite ι]
    (j : ι) :
    biproduct.ι (fun _ : ι ↦ X.structureModules) j ≫
        (biproduct.isoCoproduct fun _ : ι ↦ X.structureModules).hom =
      (SheafOfModules.ιFree j : X.structureModules ⟶ X.freeModules ι) := by
  rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  exact X.freeModulesCofan_inj ι j

/-- **The `j`-th projection of the biproduct `⨁ (fun _ : ι ↦ 𝒪ₓ)`, read through the comparison
with the coproduct, is `SheafOfModules.πFree j`**: the companion of
`AlgebraicGeometry.Scheme.biproduct_ι_comp_isoCoproduct_hom`. -/
@[reassoc (attr := simp)]
lemma Scheme.isoCoproduct_inv_comp_biproduct_π (X : Scheme.{u}) (ι : Type u) [Finite ι]
    (j : ι) :
    (biproduct.isoCoproduct fun _ : ι ↦ X.structureModules).inv ≫
        biproduct.π (fun _ : ι ↦ X.structureModules) j =
      (SheafOfModules.πFree j : X.freeModules ι ⟶ X.structureModules) := by
  rw [Iso.inv_comp_eq]
  refine biproduct.hom_ext' _ _ fun k ↦ ?_
  rw [← Category.assoc, X.biproduct_ι_comp_isoCoproduct_hom]
  by_cases h : k = j
  · subst h
    rw [biproduct.ι_π_self, SheafOfModules.ιFree_πFree_self]
  · rw [biproduct.ι_π_ne _ h, SheafOfModules.ιFree_πFree_of_ne h]

namespace Scheme.Modules

section Restriction

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of sheaves of modules commutes with the restriction maps: for `i : U ⟶ V`,

```
Γ(M, V) --- φ.app V ---> Γ(N, V)
   |                        |
  res                      res
   v                        v
Γ(M, U) --- φ.app U ---> Γ(N, U)
```
-/
@[reassoc (attr := simp)]
lemma Hom.naturality (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op ≫ φ.app U = φ.app V ≫ N.presheaf.map i.op :=
  φ.mapPresheaf.naturality i.op

/-- Elementwise version of `AlgebraicGeometry.Scheme.Modules.Hom.naturality`: applying a
morphism of sheaves of modules commutes with restricting a section. -/
lemma Hom.naturality_apply (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (s : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op s) = N.presheaf.map i.op (φ.app V s) :=
  ConcreteCategory.congr_hom (φ.naturality i) s

end Restriction

section Kernel

variable {X : Scheme.{u}} (U : X.Opens)
  {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N)

/-- **The sections of a kernel are the kernel of the sections.** Over any open `U`, the image
of `kernel.ι f` on sections is the set of sections of `M` killed by `f`.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma range_map_kernelι :
    Set.range ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) =
      { x | (SheafOfModules.evaluation X.ringCatSheaf (op U)).map f x = 0 } :=
  ModuleCat.range_map_kernelι f _

instance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) := by
  rw [map_kernelι_eq]
  infer_instance

/-- `kernel.ι f` is injective on sections over any open, not merely a monomorphism. -/
lemma map_kernelι_injective :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

section Stalk

variable {U} (F : X.Modules)

/-- The stalk of a sheaf of `𝒪_X`-modules at `x` is a module over the local ring `𝒪_{X, x}`. -/
noncomputable instance moduleStalk (x : X) : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  letI M : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  inferInstanceAs (Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x))

lemma germ_smul (x : X) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) (M := F.val) x U hx r m

/-- The stalk of a sheaf of `𝒪_X`-modules at a point of `U` is a module over `Γ(X, U)`,
by restriction of scalars along the germ map. -/
noncomputable instance module_section_stalk (x : U) : Module Γ(X, U) (F.presheaf.stalk x.1) :=
  Module.compHom _ (X.presheaf.germ U x.1 x.2).hom

lemma smul_stalk_def (x : U) (r : Γ(X, U)) (m : F.presheaf.stalk x.1) :
    r • m = X.presheaf.germ U x.1 x.2 r • m :=
  rfl

instance isScalarTower_section_stalk (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) (F.presheaf.stalk x.1) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

/-- The germ map on sections, as a `Γ(X, U)`-linear map. -/
noncomputable def germₗ (x : U) : Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x.1 where
  toFun := F.presheaf.germ U x.1 x.2
  map_add' := map_add _
  map_smul' r m := by
    change F.presheaf.germ U x.1 x.2 (r • m) = _
    rw [germ_smul]
    rfl

@[simp]
lemma germₗ_apply (x : U) (m : Γ(F, U)) :
    germₗ F x m = F.presheaf.germ U x.1 x.2 m := rfl

/-- The germ map on sections, as a map semilinear over the germ map on functions.

This is the variant of `AlgebraicGeometry.Scheme.Modules.germₗ` in which the stalk carries its
`𝒪_{X, x}`-module structure rather than the `Γ(X, U)`-module structure obtained from it by
restriction of scalars; it is what transports a `Γ(X, U)`-span of sections to an
`𝒪_{X, x}`-span of germs. -/
noncomputable def germₛₗ (x : U) :
    Γ(F, U) →ₛₗ[(X.presheaf.germ U x.1 x.2).hom] F.presheaf.stalk x.1 where
  toFun := F.presheaf.germ U x.1 x.2
  map_add' := map_add _
  map_smul' := germ_smul F x.1 x.2

@[simp]
lemma germₛₗ_apply (x : U) (m : Γ(F, U)) :
    germₛₗ F x m = F.presheaf.germ U x.1 x.2 m := rfl

end Stalk

end Kernel

section StalkFunctor

variable {X : Scheme.{u}} {M N K : X.Modules}

variable (X) in
/-- **The stalk of a sheaf of `𝒪_X`-modules at a point**, as a functor to modules over the local
ring `𝒪_{X, x}`:

```
X.Modules ⥤ ModuleCat 𝒪_{X, x},    M ↦ M_x
```

The module structure on the stalk is `AlgebraicGeometry.Scheme.Modules.moduleStalk`; forgetting
it leaves the composite `toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab x`, which is the functor
on which Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` is stated. -/
noncomputable def stalkFunctor (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map φ := ModuleCat.ofHom (PresheafOfModules.stalkMapₗ φ.val x)
  map_id M := by
    ext z
    exact ConcreteCategory.congr_hom
      ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_id M) z
  map_comp φ ψ := by
    ext z
    exact ConcreteCategory.congr_hom
      ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_comp φ ψ) z

@[simp]
lemma stalkFunctor_obj (x : X) (M : X.Modules) :
    (stalkFunctor X x).obj M = ModuleCat.of _ (M.presheaf.stalk x) :=
  rfl

/-- Forgetting the module structure on the stalks leaves the stalk of the underlying presheaf of
abelian groups. -/
lemma stalkFunctor_comp_forget₂ (x : X) :
    stalkFunctor X x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) Ab.{u} =
      toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x :=
  rfl

/-- Taking stalks is left exact. -/
instance (x : X) : PreservesFiniteLimits (stalkFunctor X x) := by
  -- after forgetting the module structure this is the stalk of a presheaf of abelian groups,
  -- which is a filtered colimit, and the forgetful functor reflects limits
  have : PreservesFiniteLimits
      (stalkFunctor X x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) Ab.{u}) := by
    rw [stalkFunctor_comp_forget₂]
    exact comp_preservesFiniteLimits _ _
  exact ⟨fun _ _ _ ↦ ⟨fun {_} ↦ preservesLimit_of_reflects_of_preserves _ (forget₂ _ Ab.{u})⟩⟩

/-- The map `M_x ⟶ N_x` on stalks at `x` induced by a morphism `M ⟶ N` of sheaves of
`𝒪_X`-modules, as a map of abelian groups.

`AlgebraicGeometry.Scheme.Modules.stalkFunctor` refines it to an `𝒪_{X, x}`-linear map; it is
the underlying map of abelian groups that composes with the germ maps, which are semilinear
over the germ maps of `𝒪_X` rather than linear. -/
noncomputable def Hom.stalkMap (φ : M ⟶ N) (x : X) :
    M.presheaf.stalk x ⟶ N.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf

@[simp]
lemma stalkFunctor_map_apply (φ : M ⟶ N) (x : X) (z : M.presheaf.stalk x) :
    (stalkFunctor X x).map φ z = φ.stalkMap x z :=
  rfl

/-- The map on stalks is `𝒪_{X, x}`-linear. -/
lemma Hom.stalkMap_smul (φ : M ⟶ N) (x : X) (r : X.presheaf.stalk x) (z : M.presheaf.stalk x) :
    φ.stalkMap x (r • z) = r • φ.stalkMap x z :=
  LinearMap.map_smul ((stalkFunctor X x).map φ).hom r z

/-- The map on stalks is compatible with the germ maps:

```
Γ(M, U) --- φ.app U ---> Γ(N, U)
   |                        |
  germ                     germ
   v                        v
  M_x --- φ.stalkMap x ---> N_x
```
-/
@[reassoc (attr := simp)]
lemma Hom.germ_stalkMap (φ : M ⟶ N) {U : X.Opens} (x : X) (hx : x ∈ U) :
    M.presheaf.germ U x hx ≫ φ.stalkMap x = φ.app U ≫ N.presheaf.germ U x hx :=
  TopCat.Presheaf.stalkFunctor_map_germ U x hx φ.mapPresheaf

/-- Elementwise version of `AlgebraicGeometry.Scheme.Modules.Hom.germ_stalkMap`. -/
@[simp]
lemma Hom.germ_stalkMap_apply (φ : M ⟶ N) {U : X.Opens} (x : X) (hx : x ∈ U) (s : Γ(M, U)) :
    φ.stalkMap x (M.presheaf.germ U x hx s) = N.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s

@[simp]
lemma Hom.stalkMap_id (M : X.Modules) (x : X) : (𝟙 M :).stalkMap x = 𝟙 _ :=
  (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_id M

@[reassoc (attr := simp)]
lemma Hom.stalkMap_comp (φ : M ⟶ N) (ψ : N ⟶ K) (x : X) :
    (φ ≫ ψ).stalkMap x = φ.stalkMap x ≫ ψ.stalkMap x :=
  (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_comp φ ψ

/-- Elementwise version of `AlgebraicGeometry.Scheme.Modules.Hom.stalkMap_comp`. -/
lemma Hom.stalkMap_comp_apply (φ : M ⟶ N) (ψ : N ⟶ K) (x : X) (z : M.presheaf.stalk x) :
    (φ ≫ ψ).stalkMap x z = ψ.stalkMap x (φ.stalkMap x z) :=
  ConcreteCategory.congr_hom (φ.stalkMap_comp ψ x) z

/-- **Taking stalks is an additive functor.** -/
instance stalkFunctor_additive (x : X) : (stalkFunctor X x).Additive where
  map_add {M N f g} := by
    ext z
    obtain ⟨U, hU, s, rfl⟩ := M.presheaf.exists_germ_eq z
    simp only [stalkFunctor_map_apply, Hom.germ_stalkMap_apply, ModuleCat.hom_add,
      LinearMap.add_apply]
    -- `Hom.app (f + g) U s` is `Hom.app f U s + Hom.app g U s` by definition
    change N.presheaf.germ U x hU (Hom.app f U s + Hom.app g U s) = _
    rw [map_add]

@[simp]
lemma Hom.stalkMap_add (φ ψ : M ⟶ N) (x : X) (z : M.presheaf.stalk x) :
    (φ + ψ).stalkMap x z = φ.stalkMap x z + ψ.stalkMap x z :=
  ConcreteCategory.congr_hom ((stalkFunctor X x).map_add (f := φ) (g := ψ)) z

@[simp]
lemma Hom.stalkMap_zero (x : X) (z : M.presheaf.stalk x) : (0 : M ⟶ N).stalkMap x z = 0 :=
  ConcreteCategory.congr_hom ((stalkFunctor X x).map_zero M N) z

lemma Hom.stalkMap_sum {κ : Type*} (s : Finset κ) (φ : κ → (M ⟶ N)) (x : X)
    (z : M.presheaf.stalk x) :
    (∑ j ∈ s, φ j).stalkMap x z = ∑ j ∈ s, (φ j).stalkMap x z := by
  refine (ConcreteCategory.congr_hom ((stalkFunctor X x).map_sum φ s) z).trans ?_
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ rfl

instance (φ : M ⟶ N) [IsIso φ] (x : X) : IsIso (φ.stalkMap x) :=
  (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_isIso φ

/-- **The germs in the image of a morphism are the germs of the sections in its image.** Since
every element of a stalk is the germ of a section over some open neighbourhood, the image of
`φ` on the stalk at `x` is the union over the open neighbourhoods `U` of `x` of the germs of the
sections of `N` over `U` in the image of `φ.app U`. -/
lemma Hom.range_stalkMap (φ : M ⟶ N) (x : X) :
    Set.range (φ.stalkMap x) =
      ⋃ (U : X.Opens) (hx : x ∈ U), N.presheaf.germ U x hx '' Set.range (φ.app U) := by
  ext z
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨U, hx, t, rfl⟩ := M.presheaf.exists_germ_eq w
    exact ⟨U, hx, φ.app U t, ⟨t, rfl⟩, (φ.germ_stalkMap_apply x hx t).symm⟩
  · rintro ⟨U, hx, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨M.presheaf.germ U x hx t, φ.germ_stalkMap_apply x hx t⟩

/-- **A morphism of sheaves of `𝒪_X`-modules which is an isomorphism on every stalk is an
isomorphism.**

This is the criterion that `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app` cannot
replace: the latter quantifies over *all* opens, and the sections of a sheaf over a non-affine
open are rarely computable, whereas stalks always are. -/
theorem Hom.isIso_of_isIso_stalkMap (φ : M ⟶ N) (h : ∀ x : X, IsIso (φ.stalkMap x)) :
    IsIso φ := by
  -- the forgetful functor to presheaves of abelian groups reflects isomorphisms, and for a
  -- morphism of *sheaves* of abelian groups `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`
  -- turns the hypothesis on stalks into an isomorphism
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) ⟶ ⟨N.presheaf, N.isSheaf⟩ :=
    ObjectProperty.homMk φ.mapPresheaf
  -- `φ.stalkMap x` is by definition the map on stalks of `ψ.hom`
  have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ψ.hom) := h
  have : IsIso ψ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  have : IsIso ((toPresheaf X).map φ) := (TopCat.Sheaf.forget Ab.{u} X).map_isIso ψ
  exact isIso_of_reflects_iso φ (toPresheaf X)

/-- **A morphism of sheaves of `𝒪_X`-modules is an isomorphism if and only if it is one on
every stalk.** -/
theorem Hom.isIso_iff_isIso_stalkMap (φ : M ⟶ N) : IsIso φ ↔ ∀ x : X, IsIso (φ.stalkMap x) :=
  ⟨fun _ _x ↦ inferInstance, φ.isIso_of_isIso_stalkMap⟩

section StalkKernel

variable (f : M ⟶ N) (x : X)

/-- **The stalk of a kernel is the kernel of the stalk.** At every point, the image of
`kernel.ι f` on stalks is the set of germs killed by `f`:

```
0 ⟶ (kernel f)_x --- (kernel.ι f).stalkMap x ---> M_x --- f.stalkMap x ---> N_x
```

This is the stalkwise counterpart of
`AlgebraicGeometry.Scheme.Modules.range_map_kernelι`. -/
lemma range_stalkMap_kernelι :
    Set.range ((kernel.ι f).stalkMap x) = { z | f.stalkMap x z = 0 } :=
  ModuleCat.range_map_kernelι f (stalkFunctor X x)

/-- `kernel.ι f` is injective on stalks, not merely a monomorphism. -/
lemma stalkMap_kernelι_injective : Function.Injective ((kernel.ι f).stalkMap x) :=
  (ModuleCat.mono_iff_injective _).mp ((stalkFunctor X x).map_mono (kernel.ι f))

instance : Mono ((kernel.ι f).stalkMap x) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (stalkMap_kernelι_injective f x)

end StalkKernel

end StalkFunctor

noncomputable section StalkDesc

variable {X : Scheme.{u}} (G : X.Modules) (x : X) (A : Ab.{u})
  (c : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ A))
  (hc : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
    G.presheaf.map i ≫ c V hV = c U hU)
  {S : CommRingCat.{u}} (φ : X.presheaf.stalk x ⟶ S) [Module S A]
  (hφ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
    c U hU (r • s) = φ (X.presheaf.germ U x hU r) • c U hU s)

include hφ in
/-- The map out of the stalk of `G` at `x` given by a family of maps which is semilinear over a
ring map `φ : 𝒪_{X, x} ⟶ S` is itself semilinear over `φ`. -/
lemma stalkDesc_smul (r : X.presheaf.stalk x) (z : G.presheaf.stalk x) :
    G.presheaf.stalkDesc x A c hc (r • z) = φ r • G.presheaf.stalkDesc x A c hc z := by
  obtain ⟨U, hU, s, rfl⟩ := G.presheaf.exists_germ_eq z
  obtain ⟨V, hV, r₀, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hU, hV⟩ r₀,
    ← G.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x ⟨hU, hV⟩ s,
    ← germ_smul, TopCat.Presheaf.stalkDesc_germ, TopCat.Presheaf.stalkDesc_germ, hφ]

/-- The `𝒪_{X, x}`-linear map out of the stalk of `G` at `x` induced by a compatible family of
maps out of the sections of `G` over the open neighbourhoods of `x` which is semilinear over a
ring map `φ : 𝒪_{X, x} ⟶ S`. -/
def stalkDescₗ :
    G.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S A) where
  toFun := G.presheaf.stalkDesc x A c hc
  map_add' := map_add _
  map_smul' := stalkDesc_smul G x A c hc φ hφ

@[simp]
lemma stalkDescₗ_apply (z : G.presheaf.stalk x) :
    stalkDescₗ G x A c hc φ hφ z = G.presheaf.stalkDesc x A c hc z := rfl

include hφ in
/-- Composing the linear map out of the stalk with a semilinear map of the targets is the linear
map out of the stalk for the composed family.

This is stated for a variable `G` so that it can be instantiated at a concrete sheaf of modules
without the kernel having to redo the argument by `TopCat.Presheaf.stalk_hom_ext` there. -/
lemma ofSemilinear_comp_stalkDescₗ {S' : CommRingCat.{u}} (ψ : X.presheaf.stalk x ⟶ S')
    (A' : Ab.{u}) [Module S' A'] (c' : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ A'))
    (hc' : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
      G.presheaf.map i ≫ c' V hV = c' U hU)
    (hψ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
      c' U hU (r • s) = ψ (X.presheaf.germ U x hU r) • c' U hU s)
    (g : A ⟶ A') (hg : ∀ (r : X.presheaf.stalk x) (a : A), g (φ r • a) = ψ r • g a)
    (hgc : ∀ (U : X.Opens) (hU : x ∈ U), c U hU ≫ g = c' U hU) :
    (ModuleCat.ofSemilinear φ ψ g hg).hom.comp (stalkDescₗ G x A c hc φ hφ) =
      stalkDescₗ G x A' c' hc' ψ hψ := by
  have hcomp : G.presheaf.stalkDesc x A c hc ≫ g = G.presheaf.stalkDesc x A' c' hc' :=
    TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ by
      rw [← Category.assoc, TopCat.Presheaf.germ_comp_stalkDesc,
        TopCat.Presheaf.germ_comp_stalkDesc, hgc]
  exact LinearMap.ext fun z ↦ (ModuleCat.ofSemilinear_apply _ _ g hg _).trans
    ((ConcreteCategory.comp_apply (G.presheaf.stalkDesc x A c hc) g z).symm.trans
      (ConcreteCategory.congr_hom hcomp z))

end StalkDesc
section StalkBase

variable {X Y : Scheme.{u}}

/-- The module structure on the stalk `F_x` of a sheaf of `𝒪_X`-modules over the local ring
`𝒪_{Y, f x}` of the base of `f : X ⟶ Y`, by restriction of scalars along `f.stalkMap x`.

This is the companion of `AlgebraicGeometry.Scheme.Modules.moduleStalk`, which is the case of
the identity morphism: there the scalars are the local ring of `X` itself. -/
@[instance_reducible]
noncomputable def moduleStalkBase (F : X.Modules) (f : X ⟶ Y) (x : X) :
    Module (Y.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
  Module.compHom _ (f.stalkMap x).hom

end StalkBase

section StalkRestriction

variable {Y W : Scheme.{u}} (f : Y ⟶ W) [IsOpenImmersion f] (y : Y)

/-- **Restriction along an open immersion does not change stalks**, as an additive
equivalence. -/
noncomputable def restrictStalkEquiv (M : W.Modules) :
    ((restrictFunctor f).obj M).presheaf.stalk y ≃+ M.presheaf.stalk (f y) :=
  ((restrictStalkNatIso f y).app M).addCommGroupIsoToAddEquiv

@[simp]
lemma restrictStalkEquiv_germ (M : W.Modules) {U : Y.Opens} (hyU : y ∈ U)
    (s : Γ((restrictFunctor f).obj M, U)) :
    restrictStalkEquiv f y M (((restrictFunctor f).obj M).presheaf.germ U y hyU s) =
      M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ s :=
  ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app f y M hyU) s

/-- The comparison of stalks under restriction along an open immersion is semilinear over the
stalk map of the open immersion. -/
lemma restrictStalkEquiv_smul (M : W.Modules) (r : Y.presheaf.stalk y)
    (z : ((restrictFunctor f).obj M).presheaf.stalk y) :
    restrictStalkEquiv f y M (r • z) = inv (f.stalkMap y) r • restrictStalkEquiv f y M z := by
  obtain ⟨V, hyV, a, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨U, hUV, hyU, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (C := Ab.{u})
    ((restrictFunctor f).obj M).presheaf z hyV
  rw [← Y.presheaf.germ_res_apply (homOfLE hUV) y hyU a, ← germ_smul, restrictStalkEquiv_germ,
    restrictStalkEquiv_germ]
  have key (b : Γ(Y, U)) :
      M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ (b • s) =
        inv (f.stalkMap y) (Y.presheaf.germ U y hyU b) •
          M.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ s := by
    have hsmul : b • s =
        (f.appIso U).inv b • (show ToType Γ(M, f ''ᵁ U) from s) := rfl
    have hscal : inv (f.stalkMap y) (Y.presheaf.germ U y hyU b) =
        W.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ ((f.appIso U).inv b) := by
      rw [← Scheme.Hom.stalkMap_germ_appIso_inv f y U hyU b, ← ConcreteCategory.comp_apply,
        IsIso.hom_inv_id]
      rfl
    rw [hsmul, germ_smul M (f y) (⟨y, hyU, rfl⟩ : f y ∈ f ''ᵁ U) ((f.appIso U).inv b)
        (show ToType Γ(M, f ''ᵁ U) from s), hscal]
  exact key _

lemma restrictStalkEquiv_symm_smul (M : W.Modules) (r : W.presheaf.stalk (f y))
    (z : M.presheaf.stalk (f y)) :
    (restrictStalkEquiv f y M).symm (r • z) =
      f.stalkMap y r • (restrictStalkEquiv f y M).symm z := by
  apply (restrictStalkEquiv f y M).injective
  rw [AddEquiv.apply_symm_apply, restrictStalkEquiv_smul, AddEquiv.apply_symm_apply,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
  rfl

/-- The linear map on stalks induced by a morphism between the restrictions of two sheaves of
modules to an open subscheme.

It is the conjugate of `PresheafOfModules.stalkMapₗ` by the comparison
`AlgebraicGeometry.Scheme.Modules.restrictStalkEquiv`; the conjugate is linear over
`𝒪_{W, f y}` because the comparison is semilinear over `f.stalkMap y` in one direction and over
its inverse in the other. -/
noncomputable def stalkMapOfRestrictHom {M N : W.Modules}
    (φ : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    M.presheaf.stalk (f y) →ₗ[W.presheaf.stalk (f y)] N.presheaf.stalk (f y) where
  toFun z := restrictStalkEquiv f y N
    (PresheafOfModules.stalkMapₗ φ.val y ((restrictStalkEquiv f y M).symm z))
  map_add' z z' := by simp only [map_add]
  map_smul' r z := by
    rw [RingHom.id_apply, restrictStalkEquiv_symm_smul, LinearMap.map_smul,
      restrictStalkEquiv_smul, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
    rfl

/-- `AlgebraicGeometry.Scheme.Modules.stalkMapOfRestrictHom` is functorial:

```text
  M_{f y} ── stalkMapOfRestrictHom φ ──▶ N_{f y} ── stalkMapOfRestrictHom ψ ──▶ P_{f y}
     │                                                                            ▲
     └───────────────── stalkMapOfRestrictHom (φ ≫ ψ) ────────────────────────────┘
```
-/
lemma stalkMapOfRestrictHom_comp {M N P : W.Modules}
    (φ : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N)
    (ψ : (restrictFunctor f).obj N ⟶ (restrictFunctor f).obj P)
    (z : M.presheaf.stalk (f y)) :
    stalkMapOfRestrictHom f y (φ ≫ ψ) z =
      stalkMapOfRestrictHom f y ψ (stalkMapOfRestrictHom f y φ z) := by
  simp only [stalkMapOfRestrictHom, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply,
    PresheafOfModules.stalkMapₗ_apply]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  rfl

lemma stalkMapOfRestrictHom_id (M : W.Modules) (z : M.presheaf.stalk (f y)) :
    stalkMapOfRestrictHom f y (𝟙 ((restrictFunctor f).obj M)) z = z := by
  simp only [stalkMapOfRestrictHom, LinearMap.coe_mk, AddHom.coe_mk,
    PresheafOfModules.stalkMapₗ_apply]
  rw [SheafOfModules.id_val, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp

/-- **Two sheaves of modules which agree on a neighbourhood of a point have the same stalk
there**, as a module over the local ring of the ambient scheme. -/
noncomputable def stalkLinearEquivOfRestrictIso {M N : W.Modules}
    (e : (restrictFunctor f).obj M ≅ (restrictFunctor f).obj N) :
    M.presheaf.stalk (f y) ≃ₗ[W.presheaf.stalk (f y)] N.presheaf.stalk (f y) :=
  LinearEquiv.ofLinearMap (stalkMapOfRestrictHom f y e.hom) (stalkMapOfRestrictHom f y e.inv)
    (LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, ← stalkMapOfRestrictHom_comp, e.inv_hom_id,
        stalkMapOfRestrictHom_id, LinearMap.id_apply])
    (LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, ← stalkMapOfRestrictHom_comp, e.hom_inv_id,
        stalkMapOfRestrictHom_id, LinearMap.id_apply])

end StalkRestriction

section Sections

variable {X : Scheme.{u}} {F G : X.Modules}

/-- **An isomorphism of sheaves of modules identifies their sections.** An isomorphism
`e : F ≅ G` of sheaves of `𝒪_X`-modules induces a `Γ(X, U)`-linear isomorphism
`Γ(F, U) ≃ₗ[Γ(X, U)] Γ(G, U)` on the sections over any open `U`. -/
noncomputable def sectionsEquivOfIso (e : F ≅ G) (U : X.Opens) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(G, U) where
  toFun := Hom.app e.hom U
  map_add' := map_add _
  map_smul' r m := Hom.app_smul e.hom r m
  invFun := Hom.app e.inv U
  left_inv m := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  right_inv m := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app]
    rfl

@[simp]
lemma sectionsEquivOfIso_apply (e : F ≅ G) (U : X.Opens) (s : Γ(F, U)) :
    sectionsEquivOfIso e U s = Hom.app e.hom U s := rfl

@[simp]
lemma sectionsEquivOfIso_symm_apply (e : F ≅ G) (U : X.Opens) (s : Γ(G, U)) :
    (sectionsEquivOfIso e U).symm s = Hom.app e.inv U s := rfl

end Sections

noncomputable section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **Base change for the pushforward of sheaves of modules.** Restricting the pushforward of
`M` along `f : X ⟶ Y` to an open `U` of `Y` is the pushforward of the restriction of `M` to
`f ⁻¹ᵁ U` along the induced morphism `f ∣_ U`. -/
def pushforwardCompRestrictFunctorIso :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _
      (NatIso.ofComponents (fun W ↦ eqToIso (image_morphismRestrict_preimage f U W))
        fun _ ↦ Subsingleton.elim _ _)
      (by
        ext W r
        have : (U.ι.appIso W.unop).inv ≫ f.app (U.ι ''ᵁ W.unop) ≫
              X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op =
            (f ∣_ U).app W.unop ≫ ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ W.unop)).inv := by
          rw [morphismRestrict_app]
          simp
          rfl
        exact congr($this r)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

variable {f} in
/-- Restricting along an isomorphism of schemes and then along its inverse is the identity. -/
def restrictFunctorCompInvIso [IsIso f] :
    restrictFunctor f ⋙ restrictFunctor (inv f) ≅ 𝟭 Y.Modules :=
  (restrictFunctorComp (inv f) f).symm ≪≫ restrictFunctorCongr (by simp) ≪≫ restrictFunctorId

/-- Restricting along the inverse of an isomorphism of schemes and then along the isomorphism
itself is the identity. -/
def restrictFunctorInvCompIso (e : X ≅ Y) :
    restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
    restrictFunctorId

/-- **Base change for the restriction of sheaves of modules to an open subscheme.** Restricting
`M` to an open `U` of `Y` and then along an open immersion `f : X ⟶ Y` is the same as restricting
`M` along `f` and then to `f ⁻¹ᵁ U`. -/
def restrictFunctorCompMorphismRestrictIso [IsOpenImmersion f] :
    restrictFunctor U.ι ⋙ restrictFunctor (f ∣_ U) ≅
      restrictFunctor f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  (restrictFunctorComp (f ∣_ U) U.ι).symm ≪≫
    restrictFunctorCongr (morphismRestrict_ι f U) ≪≫ restrictFunctorComp (f ⁻¹ᵁ U).ι f

/-- **Sections of a morphism restricted to an open subscheme.** Over an open `V` of the open
subscheme `U`, the restriction of `φ` to `U` acts as `φ` itself over the image `U.ι ''ᵁ V`. -/
@[simp]
lemma Hom.app_restrictFunctor_ι_map {V : Y.Opens} {M N : Y.Modules} (φ : M ⟶ N)
    (W : V.toScheme.Opens) :
    Hom.app ((restrictFunctor V.ι).map φ) W = Hom.app φ (V.ι ''ᵁ W) :=
  rfl

end Pushforward

noncomputable section Over

variable {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)

/-- The sheaf of `𝒪_X`-modules `M` restricted to the site of opens contained in `U`
corresponds to the sheaf of `𝒪_X|_U`-modules `M.restrict U.ι` on the scheme `U`. -/
def overEquivInverseRestrictIso : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
    ((overEquiv U).unitIso.app (M.over U)).symm

/-- `(Scheme.Modules.overEquiv U).inverse` sends `𝒪_X|_U` to the structure sheaf of the site of
opens contained in `U`. -/
def overEquivInverseUnitIso :
    SheafOfModules.unit.{u} (X.ringCatSheaf.over U) ≅
      (overEquiv U).inverse.obj (SheafOfModules.unit.{u} U.toScheme.ringCatSheaf) :=
  (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm

end Over
section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The pullback of sheaves of modules along `f` is a left adjoint, in the form the
constructions of `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` ask for it. -/
instance : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u} f.toRingCatSheafHom).isRightAdjoint

/-- The pullback of the structure sheaf `𝒪_Y` along a morphism of schemes `f : X ⟶ Y`
is the structure sheaf `𝒪_X`. -/
noncomputable def pullbackUnitIso :
    (pullback f).obj Y.structureModules ≅ X.structureModules :=
  have := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (φ := f.toRingCatSheafHom)
  asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- The pullback of the free sheaf `𝒪_Y^ι` along a morphism of schemes `f : X ⟶ Y` is the free
sheaf `𝒪_X^ι`. It is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` on each summand, by
`AlgebraicGeometry.Scheme.Modules.pullback_map_ιFree_comp_pullbackFreeIso_hom`. -/
noncomputable def pullbackFreeIso (ι : Type u) :
    (pullback f).obj (Y.freeModules ι) ≅ X.freeModules ι :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom ι

/-- **The identification `f^*(𝒪_Y^ι) ≅ 𝒪_X^ι` is the identification `f^* 𝒪_Y ≅ 𝒪_X` on each
summand**:

```
  f^*(𝒪_Y) ──f^*(ιFree i)──▶ f^*(𝒪_Y^ι)
      │                           │
      │ pullbackUnitIso           │ pullbackFreeIso
      ▼                           ▼
     𝒪_X ──────ιFree i─────────▶ 𝒪_X^ι
```
-/
@[reassoc (attr := simp)]
lemma pullback_map_ιFree_comp_pullbackFreeIso_hom (ι : Type u) (i : ι) :
    (pullback f).map (SheafOfModules.ιFree i) ≫ (pullbackFreeIso f ι).hom =
      (pullbackUnitIso f).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

set_option backward.isDefEq.respectTransparency false in
/-- **Base change for the pullback of sheaves of modules.** Restricting the pullback of `M`
along `f : X ⟶ Y` to `f ⁻¹ᵁ U` is the pullback of the restriction of `M` to `U` along the
induced morphism `f ⁻¹ᵁ U ⟶ U`. -/
noncomputable def restrictFunctorCompPullbackIso :
    restrictFunctor U.ι ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) ≅
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) _ ≪≫
    pullbackComp _ _ ≪≫ pullbackCongr (f.resLE_comp_ι le_rfl) ≪≫ (pullbackComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

/-- The pullback functor on the level of the slices: it takes a sheaf of modules over
`𝒪_Y` restricted to `U` to a sheaf of modules over `𝒪_X` restricted to `f ⁻¹ᵁ U`. -/
noncomputable def pullbackOver :
    SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (overEquiv U).functor ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) ⋙
    (overEquiv (f ⁻¹ᵁ U)).inverse

instance : PreservesColimitsOfSize.{u, u} (pullbackOver f U) := by
  unfold pullbackOver
  infer_instance

/-- `Scheme.Modules.pullbackOver` sends the structure sheaf to the structure sheaf. -/
noncomputable def pullbackOverUnitIso :
    SheafOfModules.unit.{u} (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      (pullbackOver f U).obj (SheafOfModules.unit.{u} (Y.ringCatSheaf.over U)) :=
  ((f ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
    (overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
      ((pullbackUnitIso (f.resLE U (f ⁻¹ᵁ U) le_rfl)).symm ≪≫
        (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mapIso
          (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm)

/-- `Scheme.Modules.pullbackOver` computes the restriction to `f ⁻¹ᵁ U` of the pullback
of `M` in terms of the restriction of `M` to `U`. -/
noncomputable def pullbackOverObjIso (M : Y.Modules) :
    (pullbackOver f U).obj (M.over U) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ U) :=
  (overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
      ((pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mapIso ((overFunctorEquiv U).app M) ≪≫
        (restrictFunctorCompPullbackIso f U).app M ≪≫
        ((overFunctorEquiv (f ⁻¹ᵁ U)).app ((pullback f).obj M)).symm) ≪≫
    ((overEquiv (f ⁻¹ᵁ U)).unitIso.app (((pullback f).obj M).over (f ⁻¹ᵁ U))).symm

end Pullback

/-!
## Pulling back sections along a morphism of schemes
-/

noncomputable section PushforwardPullback

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (N : Y.Modules) (M : Z.Modules)

/-- The canonical morphism `b_* b^* M ⟶ (a ≫ b)_* (a ≫ b)^* M`, obtained by applying `b_*`
to the unit of the adjunction `a^* ⊣ a_*`. -/
noncomputable def pushforwardPullbackComp :
    (pushforward b).obj ((pullback b).obj M) ⟶
      (pushforward (a ≫ b)).obj ((pullback (a ≫ b)).obj M) :=
  (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) ≫
    (pushforwardComp a b).hom.app ((pullback a).obj ((pullback b).obj M)) ≫
      (pushforward (a ≫ b)).map ((pullbackComp a b).hom.app M)

/-- The morphism `b_* b^* M ⟶ (a ≫ b)_* (a ≫ b)^* M` is compatible with the units of the
adjunctions, so that the section `s` of `M` over an open subset has the same image in
`Γ((a ≫ b)^* M, _)` whether it is pulled back in one step or in two. -/
@[reassoc (attr := simp)]
lemma unit_pushforwardPullbackComp :
    (pullbackPushforwardAdjunction b).unit.app M ≫ pushforwardPullbackComp a b M =
      (pullbackPushforwardAdjunction (a ≫ b)).unit.app M := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction b).comp
    (pullbackPushforwardAdjunction a)) (pullbackPushforwardAdjunction (a ≫ b))
    (pullbackComp a b).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  simp only [Functor.comp_obj] at h
  rw [pushforwardPullbackComp, ← Category.assoc, ← Category.assoc, h, Category.assoc,
    ← Functor.map_comp]
  simp

lemma pushforward_smul {X Y : Scheme.{u}} (a : X ⟶ Y) (N : X.Modules) (U : Y.Opens)
    (r : Γ(Y, U)) :
    ((pushforward a).obj N).smul (U := U) r = N.smul (a.app U r) := rfl

lemma eqToHom_pushforward_smul {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : X'.Modules) (U : Y'.Opens)
    (r : Γ(Y', U)) (y : Γ((pushforward a).obj N, U)) :
    eqToHom (pushforward_obj_obj a N U) (r • y) =
      a.app U r • eqToHom (pushforward_obj_obj a N U) y := rfl

/-- The restriction map `Γ(X', a ⁻¹ᵁ ⊤) ⟶ Γ(X', ⊤)` is the identity, so that restricting
the pullback of a global function gives the pullback of functions on global sections. -/
lemma map_le_top_app_top {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (r : Γ(Y', ⊤)) :
    X'.presheaf.map (homOfLE (by simp : (⊤ : X'.Opens) ≤ a ⁻¹ᵁ ⊤)).op (a.app ⊤ r) =
      a.appTop r := by
  exact (ConcreteCategory.congr_hom
    (Scheme.presheaf_map_homOfLE_preimage_top_eq_id X'.presheaf a) _).trans rfl

lemma pushforwardPullbackComp_app (V : Z.Opens) :
    (pushforwardPullbackComp a b M).app V =
      ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)).app (b ⁻¹ᵁ V) ≫
        ((pullbackComp a b).hom.app M).app ((a ≫ b) ⁻¹ᵁ V) := by
  simp [pushforwardPullbackComp]

/-- The unit of the adjunction `(𝟙 X)^* ⊣ (𝟙 X)_*` is the identification of `N` with
`(𝟙 X)_* (𝟙 X)^* N`. -/
@[reassoc (attr := simp)]
lemma unit_pushforwardId :
    (pullbackPushforwardAdjunction (𝟙 Y)).unit.app N ≫
        (pushforward (𝟙 Y)).map ((pullbackId Y).hom.app N) = (pushforwardId Y).inv.app N := by
  have h := unit_conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 Y)) (pullbackId Y).hom N
  rw [conjugateEquiv_pullbackId_hom] at h
  simpa using h.symm

/-- The sections of `a_* M` over `U` are the sections of `M` over `a ⁻¹ᵁ U` by definition, so
the identification of the two is the identity.

It is nevertheless spelled out in `AlgebraicGeometry.Scheme.Modules.sectionsPullbackLE`: letting
the two be identified silently makes elaboration unfold the scheme `a ⁻¹ᵁ U` is an open subset
of, which is expensive when that scheme is a pullback. -/
lemma eqToHom_pushforward_obj_obj (P : X.Modules) (U : Y.Opens) :
    eqToHom (pushforward_obj_obj a P U) = 𝟙 Γ((pushforward a).obj P, U) := rfl

/-- The identification of `Γ(a_* P, U)` with `Γ(P, a ⁻¹ᵁ U)` is compatible with restriction; see
`AlgebraicGeometry.Scheme.Modules.eqToHom_pushforward_obj_obj` for why it is spelled out. -/
lemma eqToHom_pushforward_map (P : X.Modules) {U U' : Y.Opens} (i : op U' ⟶ op U) :
    ((pushforward a).obj P).presheaf.map i ≫ eqToHom (pushforward_obj_obj a P U) =
      eqToHom (pushforward_obj_obj a P U') ≫
        P.presheaf.map ((Opens.map a.base).map i.unop).op := rfl

/-- The pullback of sections along `a : X ⟶ Y`, from an open `U` of `Y` to an open `V` of `X`
contained in `a ⁻¹ᵁ U`: the image of a section under the unit `N ⟶ a_* a^* N`, read as a section
of `a^* N` over `a ⁻¹ᵁ U` and restricted to `V`. -/
def sectionsPullbackLE {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) :
    Γ(N, U) ⟶ Γ((pullback a).obj N, V) :=
  ((pullbackPushforwardAdjunction a).unit.app N).app U ≫
    eqToHom (pushforward_obj_obj a ((pullback a).obj N) U) ≫
    ((pullback a).obj N).presheaf.map (homOfLE h).op

/-- Restricting further after pulling back is pulling back to the smaller open:

```
                  sectionsPullbackLE a N h
  Γ(N, U) ------------------------------------> Γ(a^* N, V)
         ╲                                            |
          ╲  sectionsPullbackLE a N (h' : V' ≤ V ≤ ..)| (a^* N).presheaf.map i
           ╲                                          v
            ────────────────────────────────> Γ(a^* N, V')
```
-/
@[reassoc]
lemma sectionsPullbackLE_map {U : Y.Opens} {V V' : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op V ⟶ op V') :
    sectionsPullbackLE a N h ≫ ((pullback a).obj N).presheaf.map i =
      sectionsPullbackLE a N (i.unop.le.trans h) := by
  rw [sectionsPullbackLE, sectionsPullbackLE, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  congr 1

/-- Pulling back the restriction of a section is the pullback of the section:

```
  Γ(N, U) --- sectionsPullbackLE a N h ---> Γ(a^* N, V)
     |                                            ^
     | N.presheaf.map i                          ╱
     v                                          ╱ sectionsPullbackLE a N h'
  Γ(N, U') ────────────────────────────────────
```
-/
@[reassoc]
lemma map_sectionsPullbackLE {U U' : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    N.presheaf.map i ≫ sectionsPullbackLE a N h =
      sectionsPullbackLE a N (h.trans ((Opens.map a.base).map i.unop).le) := by
  have hnat := ((pullbackPushforwardAdjunction a).unit.app N).mapPresheaf.naturality i
  simp only [mapPresheaf_app, Functor.id_obj, Functor.comp_obj] at hnat
  rw [sectionsPullbackLE, sectionsPullbackLE, ← Category.assoc, ← Category.assoc, hnat,
    Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, eqToHom_pushforward_map, Category.assoc, ← Functor.map_comp]
  congr 1

/-- The pullback of sections is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`. -/
lemma sectionsPullbackLE_smul {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U)
    (r : Γ(Y, U)) (r' : Γ(X, V)) (hr : a.appLE U V h r = r') (s : Γ(N, U)) :
    sectionsPullbackLE a N h (r • s) = r' • sectionsPullbackLE a N h s := by
  subst hr
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, sectionsPullbackLE]
  simp only [ConcreteCategory.comp_apply, Functor.id_obj, Functor.comp_obj, Hom.app_smul,
    eqToHom_pushforward_smul, map_smul]

/-- Pulling a section back along the identity is restricting it:

```
                  sectionsPullbackLE (𝟙 Y) N h
  Γ(N, U) ---------------------------------------> Γ((𝟙 Y)^* N, V)
         ╲                                                |
          ╲  N.presheaf.map (homOfLE h').op               | (pullbackId Y).hom.app N at V
           ╲                                              v
            ──────────────────────────────────────> Γ(N, V)
```
-/
@[reassoc]
lemma sectionsPullbackLE_id {U V : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (h' : V ≤ U) :
    sectionsPullbackLE (𝟙 Y) N h ≫ ((pullbackId Y).hom.app N).app V =
      N.presheaf.map (homOfLE h').op := by
  have hu := congrArg (fun φ ↦ Hom.app φ U) (unit_pushforwardId N)
  simp only [Hom.comp_app, pushforwardId_inv_app_app] at hu
  simp only [pushforward_map_app] at hu
  have hu' : (Hom.app ((pullbackPushforwardAdjunction (𝟙 Y)).unit.app N) U ≫
      eqToHom (pushforward_obj_obj (𝟙 Y) ((pullback (𝟙 Y)).obj N) U)) ≫
      Hom.app ((pullbackId Y).hom.app N) (𝟙 Y ⁻¹ᵁ U) = 𝟙 Γ(N, U) := hu
  rw [sectionsPullbackLE, Category.assoc, Category.assoc, Hom.naturality, ← Category.assoc,
    ← Category.assoc, hu', Category.id_comp]
  exact congrArg N.presheaf.map (Subsingleton.elim _ _)

/-- Pulling a section back to the full preimage in two steps agrees with pulling it back in
one:

```
             sectionsPullbackLE b M le_rfl
  Γ(M, U) ---------------------------------> Γ(b^* M, b ⁻¹ᵁ U)
         ╲                                          |
          ╲                                         | sectionsPullbackLE a (b^* M) le_rfl
           ╲ sectionsPullbackLE (a ≫ b) M le_rfl    v
            ╲                       Γ(a^* (b^* M), a ⁻¹ᵁ b ⁻¹ᵁ U)
             ╲                                      |
              ╲                                     | (pullbackComp a b).hom.app M
               ─────────────────────────> Γ((a ≫ b)^* M, (a ≫ b) ⁻¹ᵁ U)
```
-/
@[reassoc]
lemma sectionsPullbackLE_comp_pullbackComp_app (U : Z.Opens) :
    sectionsPullbackLE b M (le_refl (b ⁻¹ᵁ U)) ≫
        sectionsPullbackLE a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U))) ≫
          ((pullbackComp a b).hom.app M).app (a ⁻¹ᵁ (b ⁻¹ᵁ U)) =
      sectionsPullbackLE (a ≫ b) M (le_refl ((a ≫ b) ⁻¹ᵁ U)) := by
  have h := congrArg (fun φ ↦ Hom.app φ U) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at h
  simp only [sectionsPullbackLE, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [eqToHom_pushforward_obj_obj b ((pullback b).obj M) U,
    eqToHom_pushforward_obj_obj a ((pullback a).obj ((pullback b).obj M)) (b ⁻¹ᵁ U),
    eqToHom_pushforward_obj_obj (a ≫ b) ((pullback (a ≫ b)).obj M) U]
  simpa using h

/-- Pulling a section back in two steps agrees with pulling it back in one:

```
                sectionsPullbackLE b M h₁
  Γ(M, U) ---------------------------------> Γ(b^* M, V)
         ╲                                         |
          ╲                                        | sectionsPullbackLE a (b^* M) h₂
           ╲ sectionsPullbackLE (a ≫ b) M h₃       v
            ╲                                Γ(a^* (b^* M), V')
             ╲                                     |
              ╲                                    | (pullbackComp a b).hom.app M at V'
               ────────────────────────────> Γ((a ≫ b)^* M, V')
```
-/
@[reassoc]
lemma sectionsPullbackLE_comp {U : Z.Opens} {V : Y.Opens} {V' : X.Opens}
    (h₁ : V ≤ b ⁻¹ᵁ U) (h₂ : V' ≤ a ⁻¹ᵁ V) (h₃ : V' ≤ (a ≫ b) ⁻¹ᵁ U) :
    sectionsPullbackLE b M h₁ ≫ sectionsPullbackLE a ((pullback b).obj M) h₂ ≫
        ((pullbackComp a b).hom.app M).app V' =
      sectionsPullbackLE (a ≫ b) M h₃ := by
  rw [← sectionsPullbackLE_map b M (le_refl (b ⁻¹ᵁ U)) (homOfLE h₁).op, Category.assoc,
    map_sectionsPullbackLE_assoc,
    ← sectionsPullbackLE_map a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U)))
      (homOfLE (h₂.trans ((Opens.map a.base).map (homOfLE h₁)).le)).op,
    Category.assoc, Hom.naturality, sectionsPullbackLE_comp_pullbackComp_app_assoc,
    sectionsPullbackLE_map]

/-- Pulling back sections along equal morphisms:

```
                sectionsPullbackLE c N hc
  Γ(N, U) ---------------------------------> Γ(c^* N, V)
         ╲                                         |
          ╲  sectionsPullbackLE d N hd             | (pullbackCongr hcd).hom.app N at V
           ╲                                       v
            ───────────────────────────────> Γ(d^* N, V)
```
-/
lemma sectionsPullbackLE_congr {c d : X ⟶ Y} (hcd : c = d) {U : Y.Opens} {V : X.Opens}
    (hc : V ≤ c ⁻¹ᵁ U) (hd : V ≤ d ⁻¹ᵁ U) :
    sectionsPullbackLE c N hc ≫ ((pullbackCongr hcd).hom.app N).app V =
      sectionsPullbackLE d N hd := by
  subst hcd
  simp [pullbackCongr]

/-- The pullback of global sections along a morphism of schemes: the image of a global section
of `N` under the unit `N ⟶ a_* a^* N`, read as a global section of `a^* N`. -/
def sectionsPullback : Γ(N, ⊤) ⟶ Γ((pullback a).obj N, ⊤) :=
  sectionsPullbackLE a N (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)

/-- The pullback of global sections is semilinear over the pullback of functions. -/
lemma sectionsPullback_smul (r : Γ(Y, ⊤)) (s : Γ(N, ⊤)) :
    sectionsPullback a N (r • s) = a.appTop r • sectionsPullback a N s :=
  sectionsPullbackLE_smul a N _ r _ (Scheme.Hom.appLE_eq_appTop a _ ▸ rfl) s

/-- The pullback of a global section is the image of the section under the unit of the
adjunction, restricted from `a ⁻¹ᵁ ⊤` to `⊤`. -/
lemma sectionsPullback_apply {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : Y'.Modules) (s : Γ(N, ⊤))
    (i : (⊤ : X'.Opens) ⟶ a ⁻¹ᵁ ⊤) :
    sectionsPullback a N s =
      ((pullback a).obj N).presheaf.map i.op
        (((pullbackPushforwardAdjunction a).unit.app N).app ⊤ s) :=
  rfl

/-- **The pullback of global sections is natural in the sheaf of modules.** For `a : X' ⟶ Y'`
and `φ : N ⟶ N'`, the square

```
    Γ(N, ⊤)  ------------- φ.app ⊤ ------------->  Γ(N', ⊤)
       |                                              |
sectionsPullback a N                       sectionsPullback a N'
       v                                              v
Γ(a ^* N, ⊤) -- ((pullback a).map φ).app ⊤ --> Γ(a ^* N', ⊤)
```

commutes. -/
@[reassoc]
lemma sectionsPullback_naturality {X' Y' : Scheme.{u}} (a : X' ⟶ Y') {N N' : Y'.Modules}
    (φ : N ⟶ N') :
    sectionsPullback a N ≫ ((pullback a).map φ).app ⊤ = φ.app ⊤ ≫ sectionsPullback a N' := by
  ext s
  have h := ConcreteCategory.congr_hom
    congr(Hom.app $(((pullbackPushforwardAdjunction a).unit.naturality φ).symm) ⊤) s
  simp only [Functor.comp_map, Functor.id_map, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at h
  simp only [ConcreteCategory.comp_apply,
    sectionsPullback_apply a N s (homOfLE (by simp)),
    sectionsPullback_apply a N' _ (homOfLE (by simp)), Hom.naturality_apply]
  exact congrArg _ h

/-- Elementwise version of
`AlgebraicGeometry.Scheme.Modules.sectionsPullback_naturality`. -/
lemma sectionsPullback_naturality_apply {X' Y' : Scheme.{u}} (a : X' ⟶ Y') {N N' : Y'.Modules}
    (φ : N ⟶ N') (s : Γ(N, ⊤)) :
    ((pullback a).map φ).app ⊤ (sectionsPullback a N s) = sectionsPullback a N' (φ.app ⊤ s) :=
  ConcreteCategory.congr_hom (sectionsPullback_naturality a φ) s

/-- The pullback of sections is natural in the sheaf of modules:

```
  Γ(N, U) --- sectionsPullbackLE a N h ---> Γ(a^* N, V)
     |                                            |
     | ψ.app U                                    | ((pullback a).map ψ).app V
     v                                            v
  Γ(N', U) --- sectionsPullbackLE a N' h --> Γ(a^* N', V)
```
-/
@[reassoc]
lemma sectionsPullbackLE_naturality {N' : Y.Modules} (ψ : N ⟶ N') {U : Y.Opens} {V : X.Opens}
    (h : V ≤ a ⁻¹ᵁ U) :
    ψ.app U ≫ sectionsPullbackLE a N' h =
      sectionsPullbackLE a N h ≫ ((pullback a).map ψ).app V := by
  have hnat := congrArg (fun φ ↦ Hom.app φ U) ((pullbackPushforwardAdjunction a).unit.naturality ψ)
  simp only [Hom.comp_app, Functor.id_map, Functor.comp_map, pushforward_map_app] at hnat
  rw [sectionsPullbackLE, sectionsPullbackLE, ← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]
  rw [Hom.naturality]
  rfl

/-- Pulling back a global section in two steps, along `a` and then along `b`, agrees with
pulling it back in one step along `a ≫ b`, under the identification `a^* b^* M ≅ (a ≫ b)^* M`:

```
                 sectionsPullback b
         Γ(M, ⊤) ───────────────────→ Γ(b^* M, ⊤)
            │                              │
            │ sectionsPullback (a ≫ b)     │ sectionsPullback a
            ↓                              ↓
  Γ((a ≫ b)^* M, ⊤) ←──────────────── Γ(a^* b^* M, ⊤)
                      (pullbackComp a b).hom
```
-/
@[simp]
lemma pullbackComp_hom_app_sectionsPullback (s : Γ(M, ⊤)) :
    Hom.app ((pullbackComp a b).hom.app M) ⊤
        (sectionsPullback a ((pullback b).obj M) (sectionsPullback b M s)) =
      sectionsPullback (a ≫ b) M s := by
  have key := congrArg (fun ψ ↦ Hom.app ψ ⊤ s) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at key
  simp only [sectionsPullback, sectionsPullbackLE, ConcreteCategory.comp_apply,
    Scheme.presheaf_map_homOfLE_preimage_top_eq_id]
  exact key

/-- Pulling back a global section along equal morphisms gives the same section, under the
identification `c^* M ≅ d^* M`:

```
                  sectionsPullback c
          Γ(N, ⊤) ──────────────────→ Γ(c^* N, ⊤)
              ╲                            │
               ╲ sectionsPullback d        │ (pullbackCongr h).hom
                ↘                          ↓
                             Γ(d^* N, ⊤)
```
-/
@[simp]
lemma pullbackCongr_hom_app_sectionsPullback {c d : X ⟶ Y} (h : c = d) (N : Y.Modules)
    (s : Γ(N, ⊤)) :
    Hom.app ((pullbackCongr h).hom.app N) ⊤ (sectionsPullback c N s) = sectionsPullback d N s := by
  subst h
  rfl

/-- **The pullback of sections of the structure sheaf is the map on functions.**

```
                sectionsPullback a
     Γ(Y, 𝒪_Y) -------------------> Γ(a ^* 𝒪_Y, ⊤)
             \                            |
              \                           | Hom.app (pullbackUnitIso a).hom ⊤
     a.appTop  \                          v
                `----------------> Γ(X, 𝒪_X)
```
-/
lemma app_pullbackUnitIso_hom_sectionsPullback {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (r : Γ(Y', ⊤)) :
    Hom.app (pullbackUnitIso a).hom ⊤ (sectionsPullback a (unit Y'.ringCatSheaf) r) =
      a.appTop r := by
  have hle : (⊤ : X'.Opens) ≤ a ⁻¹ᵁ ⊤ := by simp
  have : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Modules.pushforward a).IsRightAdjoint
  have hkey : (pullbackPushforwardAdjunction a).unit.app (unit Y'.ringCatSheaf) ≫
      (pushforward a).map (pullbackUnitIso a).hom =
        unitToPushforwardObjUnit a.toRingCatSheafHom := by
    have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (φ := a.toRingCatSheafHom)
    rwa [Adjunction.homEquiv_unit] at h
  have hnat := ((pullbackUnitIso a).hom.mapPresheaf).naturality (homOfLE hle).op
  have happ := congrArg (fun f ↦ Hom.app f ⊤) hkey
  rw [Hom.comp_app, pushforward_map_app] at happ
  replace happ := ConcreteCategory.congr_hom happ r
  rw [ConcreteCategory.comp_apply] at happ
  simp only [sectionsPullback, sectionsPullbackLE, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← mapPresheaf_app, hnat]
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app]
  exact (congrArg (ConcreteCategory.hom ((presheaf (unit X'.ringCatSheaf)).map
    (homOfLE hle).op)) happ).trans (map_le_top_app_top a r)

/-- **Pulling back the global sections of a trivial sheaf is as surjective as pulling back
functions.** If `N` is isomorphic to the structure sheaf of `Y`, then the pullback of global
sections along `a : X ⟶ Y` is surjective as soon as `a.appTop` is. -/
theorem surjective_sectionsPullback_of_iso_structureModules (e : N ≅ Y.structureModules)
    (ha : Function.Surjective a.appTop) :
    Function.Surjective (sectionsPullback a N) := by
  have key (s : Γ(N, ⊤)) :
      Hom.app (pullbackUnitIso a).hom ⊤
          (Hom.app ((pullback a).mapIso e).hom ⊤ (sectionsPullback a N s)) =
        a.appTop (Hom.app e.hom ⊤ s) := by
    rw [Functor.mapIso_hom, sectionsPullback_naturality_apply a e.hom s,
      app_pullbackUnitIso_hom_sectionsPullback]
  intro y
  obtain ⟨r, hr⟩ := ha (Hom.app (pullbackUnitIso a).hom ⊤
    (Hom.app ((pullback a).mapIso e).hom ⊤ y))
  refine ⟨Hom.app e.inv ⊤ r, ?_⟩
  have h₁ : Hom.app e.hom ⊤ (Hom.app e.inv ⊤ r) = r :=
    (sectionsEquivOfIso e ⊤).apply_symm_apply r
  have h₂ := key (Hom.app e.inv ⊤ r)
  rw [h₁, hr] at h₂
  exact (sectionsEquivOfIso ((pullback a).mapIso e) ⊤).injective
    ((sectionsEquivOfIso (pullbackUnitIso a) ⊤).injective h₂)

end PushforwardPullback

/-!
## Pulling back sections along a morphism over a base
-/

noncomputable section PullbackOver

variable {X X' X'' W : Scheme.{u}}

/-- The pullback of global sections along a morphism `u : X ⟶ X'` over a fixed base `W`: a
global section of the pullback of `F` to `X'` gives a global section of the pullback of `F` to
`X`, using that `u ≫ p' = p`.

This is the form in which the pullback of sections is functorial, by
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver_id` and
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver_comp`. -/
def sectionsPullbackOver (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W}
    (hu : u ≫ p' = p) (F : W.Modules) :
    Γ((pullback p').obj F, ⊤) ⟶ Γ((pullback p).obj F, ⊤) :=
  sectionsPullback u ((pullback p').obj F) ≫
    ((pullbackComp u p').hom.app F).app ⊤ ≫ ((pullbackCongr hu).hom.app F).app ⊤

/-- The pullback of global sections over a base is semilinear over
`AlgebraicGeometry.Scheme.Hom.appTop`.

This is stated for a variable `u` so that it can be instantiated at a concrete morphism without
the kernel having to redo the element-level rewriting there. -/
lemma sectionsPullbackOver_smul (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (r : Γ(X', ⊤)) (r' : Γ(X, ⊤)) (hr : u.appTop r = r')
    (s : Γ((pullback p').obj F, ⊤)) :
    sectionsPullbackOver u hu F (r • s) = r' • sectionsPullbackOver u hu F s := by
  simp only [sectionsPullbackOver, ConcreteCategory.comp_apply, sectionsPullback_smul, hr,
    Functor.comp_obj, Hom.app_smul]

/-- Pulling back sections along the identity is the identity. -/
@[simp]
lemma sectionsPullbackOver_id {p : X ⟶ W} (hu : 𝟙 X ≫ p = p) (F : W.Modules) :
    sectionsPullbackOver (𝟙 X) hu F = 𝟙 _ := by
  have key : ((pullbackComp (𝟙 X) p).hom.app F) ≫ ((pullbackCongr hu).hom.app F)
      = (pullbackId X).hom.app ((pullback p).obj F) := by
    have h := pseudofunctor_right_unitality (f := p)
    rw [Iso.inv_comp_eq] at h
    have h2 := congrArg (fun φ ↦ NatTrans.app φ F) h
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h2
    rw [pullbackCongr]
    simpa using h2.symm
  rw [sectionsPullbackOver, ← Hom.comp_app, key, sectionsPullback,
    sectionsPullbackLE_id _ _ le_rfl]
  simp

/-- Pulling back sections over a base in two steps agrees with pulling them back in one:

```
                     sectionsPullbackOver u' hu' F
  Γ(p''^* F, ⊤) -----------------------------------> Γ(p'^* F, ⊤)
               ╲                                            |
                ╲  sectionsPullbackOver (u ≫ u') _ F        | sectionsPullbackOver u hu F
                 ╲                                          v
                  ────────────────────────────────> Γ(p^* F, ⊤)
```
-/
lemma sectionsPullbackOver_comp (u : X ⟶ X') (u' : X' ⟶ X'') {p : X ⟶ W} {p' : X' ⟶ W}
    {p'' : X'' ⟶ W} (hu : u ≫ p' = p) (hu' : u' ≫ p'' = p') (F : W.Modules) :
    sectionsPullbackOver u' hu' F ≫ sectionsPullbackOver u hu F =
      sectionsPullbackOver (u ≫ u') (by rw [Category.assoc, hu', hu]) F := by
  subst hu'
  subst hu
  simp only [sectionsPullbackOver, sectionsPullback, pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Hom.id_app, Category.comp_id, Category.assoc]
  rw [← sectionsPullbackLE_comp u u' ((pullback p'').obj F)
      (by simp : (⊤ : X'.Opens) ≤ u' ⁻¹ᵁ ⊤) (by simp : (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤) (by simp),
    sectionsPullbackLE_naturality_assoc]
  have key := congrArg (fun φ ↦ NatTrans.app φ F)
    (pseudofunctor_associativity (f := u) (g := u') (h := p''))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_refl] at key
  have hZ := congrArg ((pullbackComp u (u' ≫ p'')).hom.app F ≫ ·) key
  simp only [← Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at hZ
  have key2 : (pullback u).map ((pullbackComp u' p'').hom.app F) ≫
        (pullbackComp u (u' ≫ p'')).hom.app F =
      (pullbackComp u u').hom.app ((pullback p'').obj F) ≫
        (pullbackComp (u ≫ u') p'').hom.app F := by
    refine (congrArg ((pullback u).map ((pullbackComp u' p'').hom.app F) ≫ ·) hZ.symm).trans ?_
    simp
  simp only [Functor.comp_obj, Category.assoc, ← Hom.comp_app]
  rw [key2]

end PullbackOver

noncomputable section Triangle

/-! ### The pullback functors along a commuting triangle -/

variable {X Y Z : Scheme.{u}} {h : X ⟶ Y} {v : Y ⟶ Z} {u : X ⟶ Z}

/-- **The pullback functors along a commuting triangle**: for `h ≫ v = u`, that is, for

```
          h
    X ─────────→ Y
      ╲          │
       ╲ u       │ v
        ↘        ↓
                 Z
```

commuting, pulling back along `v` and then along `h` is pulling back along `u`. -/
def pullbackTriangle (w : h ≫ v = u) : pullback v ⋙ pullback h ≅ pullback u :=
  pullbackComp h v ≪≫ pullbackCongr w

/-- Under the identification `h^* v^* M ≅ u^* M` of `Scheme.Modules.pullbackTriangle`, pulling
a global section back along `v` and then along `h` agrees with pulling it back along `u`. -/
@[simp]
lemma pullbackTriangle_hom_app_sectionsPullback (w : h ≫ v = u) (M : Z.Modules) (s : Γ(M, ⊤)) :
    Hom.app ((pullbackTriangle w).hom.app M) ⊤
        (sectionsPullback h ((pullback v).obj M) (sectionsPullback v M s)) =
      sectionsPullback u M s := by
  simp only [pullbackTriangle, Iso.trans_hom, NatTrans.comp_app, Hom.comp_app,
    ConcreteCategory.comp_apply, pullbackComp_hom_app_sectionsPullback,
    pullbackCongr_hom_app_sectionsPullback]

/-- **Pulling back a global section over a base is pulling it back and transporting it along the
triangle isomorphism** `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`, which is the
isomorphism implicit in the definition of
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver`. -/
lemma sectionsPullbackOver_apply (w : h ≫ v = u) (M : Z.Modules)
    (s : Γ((pullback v).obj M, ⊤)) :
    sectionsPullbackOver h w M s =
      Hom.app ((pullbackTriangle w).hom.app M) ⊤
        (sectionsPullback h ((pullback v).obj M) s) := by
  simp [sectionsPullbackOver, pullbackTriangle]

section Comp

variable {W : Scheme.{u}} {h₁ : W ⟶ X} {h₂ : X ⟶ Y} {u₂ : X ⟶ Z} {u₁ : W ⟶ Z}

/-- **Stacking two commuting triangles**: for `h₂ ≫ v = u₂` and `h₁ ≫ u₂ = u₁`, so that

```
            h₁            h₂
      W ─────────→ X ─────────→ Y
        ╲          │           ╱
      u₁ ╲      u₂ │          ╱ v
          ↘        ↓         ↙
                   Z
```

commutes, the isomorphism `h₁^* h₂^* v^* M ≅ u₁^* M` obtained from the two triangles agrees
with the one obtained from the outer triangle `(h₁ ≫ h₂) ≫ v = u₁`. This is the associativity
coherence `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` of the pullback
pseudofunctor. -/
lemma pullbackTriangle_comp_hom (w₂ : h₂ ≫ v = u₂) (w₁ : h₁ ≫ u₂ = u₁)
    (w : (h₁ ≫ h₂) ≫ v = u₁) :
    Functor.whiskerRight (pullbackTriangle w₂).hom (pullback h₁) ≫ (pullbackTriangle w₁).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pullback v) (pullbackComp h₁ h₂).hom ≫
          (pullbackTriangle w).hom := by
  subst w₂
  subst w₁
  have key := pseudofunctor_associativity (f := h₁) (g := h₂) (h := v)
  rw [Iso.inv_comp_eq, ← Functor.isoWhiskerRight_inv, Iso.inv_comp_eq] at key
  simp only [pullbackTriangle, Iso.trans_hom, pullbackCongr, eqToIso.hom, eqToHom_refl,
    Category.comp_id]
  rw [key]
  simp

/-- `Scheme.Modules.pullbackTriangle_comp_hom` evaluated at a single sheaf of modules `M`, and
for an arbitrary factorisation `k = h₁ ≫ h₂` of the composite: the two ways of identifying
`h₁^* h₂^* v^* M` with `u₁^* M` agree. -/
@[reassoc]
lemma pullbackTriangle_comp_hom_app {k : W ⟶ Y} (e : k = h₁ ≫ h₂) (w₂ : h₂ ≫ v = u₂)
    (w₁ : h₁ ≫ u₂ = u₁) (w : k ≫ v = u₁) (M : Z.Modules) :
    (pullback h₁).map ((pullbackTriangle w₂).hom.app M) ≫ (pullbackTriangle w₁).hom.app M =
      (pullbackComp h₁ h₂).hom.app ((pullback v).obj M) ≫
        (pullbackCongr e.symm).hom.app ((pullback v).obj M) ≫
          (pullbackTriangle w).hom.app M := by
  subst e
  simp only [pullbackCongr, eqToIso.hom, eqToHom_refl]
  simpa using NatTrans.congr_app (pullbackTriangle_comp_hom w₂ w₁ w) M

end Comp

/-- Pulling a sheaf of modules back along `f` and then along a section `s` of `f` gives back the
sheaf:

```text
  s^* (f^* M) ≅ (s ≫ f)^* M ≅ (𝟙 T)^* M ≅ M
```
-/
noncomputable def pullbackSectionIso {W T : Scheme.{u}} (f : W ⟶ T) (s : T ⟶ W)
    (hs : s ≫ f = 𝟙 T) (M : T.Modules) :
    (Modules.pullback s).obj ((Modules.pullback f).obj M) ≅ M :=
  (Modules.pullbackComp s f).app M ≪≫ (Modules.pullbackCongr hs).app M ≪≫
    (Modules.pullbackId T).app M

end Triangle

/-! ### Pulling back the sections of a trivial sheaf over a base -/

noncomputable section PullbackTrivial

variable {X X' W : Scheme.{u}}

/-- **Pulling back the global sections of a trivial sheaf over a base.** If the pullback of `F`
to `X'` is trivial, then pulling sections back along a morphism `u : X ⟶ X'` over the base is
surjective as soon as `u.appTop` is. -/
theorem surjective_sectionsPullbackOver_of_iso_structureModules (u : X ⟶ X') {p : X ⟶ W}
    {p' : X' ⟶ W} (hu : u ≫ p' = p) (F : W.Modules)
    (e : (pullback p').obj F ≅ X'.structureModules)
    (hu' : Function.Surjective u.appTop) :
    Function.Surjective (sectionsPullbackOver u hu F) := by
  intro y
  set α : (pullback u).obj ((pullback p').obj F) ≅ (pullback p).obj F :=
    (pullbackTriangle hu).app F
  have key (s : Γ((pullback p').obj F, ⊤)) : sectionsPullbackOver u hu F s =
      Hom.app α.hom ⊤ (sectionsPullback u ((pullback p').obj F) s) := rfl
  obtain ⟨s, hs⟩ := surjective_sectionsPullback_of_iso_structureModules u _ e hu'
    ((sectionsEquivOfIso α ⊤).symm y)
  refine ⟨s, ?_⟩
  rw [key, hs]
  exact (sectionsEquivOfIso α ⊤).apply_symm_apply y

end PullbackTrivial

section BaseChange

variable {R S : CommRingCat.{u}}

/-- Taking global sections of a sheaf of modules on `Spec S` and restricting scalars along
`φ : R ⟶ S` is the same as pushing forward along `Spec φ` and taking global sections there. -/
noncomputable def moduleSpecΓPushforwardIso (φ : R ⟶ S) :
    Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y =
              ((Scheme.ΓSpecIso S).inv (φ r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [← h] }
      inv := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Scheme.ΓSpecIso S).inv (φ r)) • y =
              ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [h] }
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ ↦ rfl)

variable {X Y : Scheme.{u}}

/-- The pullback of sheaves of modules along an isomorphism is the pushforward along its
inverse. -/
noncomputable def pullbackIsoPushforwardInv (f : X ⟶ Y) [IsIso f] :
    Modules.pullback f ≅ Modules.pushforward (inv f) :=
  Adjunction.rightAdjointUniq
    (CategoryTheory.Equivalence.mk (Modules.pullback f) (Modules.pullback (inv f))
      (pullbackComp (inv f) f ≪≫ pullbackCongr (by simp) ≪≫ pullbackId Y).symm
      (pullbackComp f (inv f) ≪≫ pullbackCongr (by simp) ≪≫ pullbackId X)).symm.toAdjunction
    (pullbackPushforwardAdjunction (inv f))

/-- **Base change of global sections along an isomorphism of rings.** For `φ : R ⟶ S` an
isomorphism, pulling a sheaf of modules on `Spec R` back along `Spec φ` and taking global
sections is restricting the scalars of its global sections along `φ⁻¹`. -/
noncomputable def moduleSpecΓPullbackIso (φ : R ⟶ S) [IsIso φ] :
    Modules.pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) ≅
      moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars (inv φ).hom :=
  Functor.isoWhiskerRight (pullbackIsoPushforwardInv (Spec.map φ)) _ ≪≫
    Functor.isoWhiskerRight (pushforwardCongr (Spec.map_inv φ).symm) _ ≪≫
    moduleSpecΓPushforwardIso (inv φ)

end BaseChange

section Fiber

variable {X Y : Scheme.{u}}

/-- The fibre functor at a point `x` of a scheme `X`: it sends a sheaf of `𝒪_X`-modules `F` to
the `κ(x)`-vector space `F(x)`, obtained by pulling `F` back along `Spec κ(x) ⟶ X` and taking
global sections. -/
noncomputable def fiberFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat (X.residueField x) :=
  Modules.pullback (X.fromSpecResidueField x) ⋙ moduleSpecΓFunctor (R := X.residueField x)

/-- The fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space. -/
noncomputable abbrev fiber (F : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (fiberFunctor X x).obj F

/-- The `κ(x)`-linear map `φ(x) : F(x) ⟶ G(x)` induced by a morphism `φ : F ⟶ G` of sheaves of
`𝒪_X`-modules. -/
noncomputable abbrev fiberMap {F G : X.Modules} (φ : F ⟶ G) (x : X) : F.fiber x ⟶ G.fiber x :=
  (fiberFunctor X x).map φ

@[simp]
lemma fiberMap_id (F : X.Modules) (x : X) : fiberMap (𝟙 F) x = 𝟙 (F.fiber x) :=
  (fiberFunctor X x).map_id F

@[simp]
lemma fiberMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    fiberMap (φ ≫ ψ) x = fiberMap φ x ≫ fiberMap ψ x :=
  (fiberFunctor X x).map_comp φ ψ

@[simp]
lemma fiberMap_zero (F G : X.Modules) (x : X) : fiberMap (0 : F ⟶ G) x = 0 :=
  (congrArg (moduleSpecΓFunctor (R := X.residueField x)).map
    ((Modules.pullback (X.fromSpecResidueField x)).map_zero F G)).trans rfl

/-- **A composite vanishes on the fibre at `x` as soon as its first factor does.** -/
lemma fiberMap_comp_eq_zero_of_left {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X)
    (h : fiberMap φ x = 0) : fiberMap (φ ≫ ψ) x = 0 := by
  rw [fiberMap_comp, h, Limits.zero_comp]

/-- **A composite vanishes on the fibre at `x` as soon as its second factor does.** -/
lemma fiberMap_comp_eq_zero_of_right {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X)
    (h : fiberMap ψ x = 0) : fiberMap (φ ≫ ψ) x = 0 := by
  rw [fiberMap_comp, h, Limits.comp_zero]

/-- Composing with an isomorphism on the left does not change the vanishing of a fibre. -/
lemma fiberMap_isoComp_left_eq_zero_iff {F G H : X.Modules} (i : F ≅ G) (φ : G ⟶ H) (x : X) :
    fiberMap (i.hom ≫ φ) x = 0 ↔ fiberMap φ x = 0 := by
  rw [fiberMap_comp, Preadditive.IsIso.comp_left_eq_zero]

/-- Composing with an isomorphism on the right does not change the vanishing of a fibre. -/
lemma fiberMap_isoComp_right_eq_zero_iff {F G H : X.Modules} (φ : F ⟶ G) (i : G ≅ H) (x : X) :
    fiberMap (φ ≫ i.hom) x = 0 ↔ fiberMap φ x = 0 := by
  rw [fiberMap_comp, Preadditive.IsIso.comp_right_eq_zero]

/-- Composing with isomorphisms on both sides does not change the vanishing of a fibre. -/
lemma fiberMap_isoComp_eq_zero_iff {F G P Q : X.Modules} (φ : F ⟶ G) (i : P ≅ F) (j : G ≅ Q)
    (x : X) : fiberMap (i.hom ≫ φ ≫ j.hom) x = 0 ↔ fiberMap φ x = 0 :=
  (fiberMap_isoComp_left_eq_zero_iff i _ x).trans (fiberMap_isoComp_right_eq_zero_iff φ j x)

/-- The restriction `F ↦ F_y` of sheaves of modules to the scheme-theoretic fibre of
`f : X ⟶ Y` over a point `y : Y`, that is, the pullback along `f.fiberι y`. -/
noncomputable abbrev restrictToFiber (f : X ⟶ Y) (y : Y) : X.Modules ⥤ (f.fiber y).Modules :=
  Modules.pullback (f.fiberι y)

/-- **Restricting a section of `f_* F` near `y` to the scheme-theoretic fibre `X_y`.** A section
of `f_* F` over an open neighbourhood `U` of `y` is a section of `F` over `f ⁻¹ᵁ U`, which
contains the whole fibre over `y`, so it restricts to a global section of `F_y`. -/
noncomputable def fiberSectionsOfNhds (f : X ⟶ Y) (F : X.Modules) (y : Y) (U : Y.Opens)
    (hU : y ∈ U) :
    Γ((pushforward f).obj F, U) ⟶ Γ((restrictToFiber f y).obj F, ⊤) :=
  eqToHom (pushforward_obj_obj f F U) ≫
    sectionsPullbackLE (f.fiberι y) F (f.preimage_fiberι_eq_top hU).ge

/-- **A section of `f _* F` over `V`, read as a global section of the restriction of `F` to the
open subscheme `f ⁻¹ᵁ V`.** A section of `f _* F` over `V` is a section of `F` over `f ⁻¹ᵁ V`,
that is a global section of the pullback of `F` to the open subscheme `f ⁻¹ᵁ V`. -/
noncomputable def sectionsOfNhds (f : X ⟶ Y) (F : X.Modules) (V : Y.Opens) :
    Γ((pushforward f).obj F, V) ⟶ Γ((pullback (f ⁻¹ᵁ V).ι).obj F, ⊤) :=
  eqToHom (pushforward_obj_obj f F V) ≫
    sectionsPullbackLE (f ⁻¹ᵁ V).ι F (f ⁻¹ᵁ V).ι_preimage_self.ge

/-- **Restricting a section of `f _* F` near `y` to the fibre `X_y` factors through the open
subscheme `f ⁻¹ᵁ V`**, along the morphism `AlgebraicGeometry.Scheme.Hom.fiberLift` of the fibre
into `f ⁻¹ᵁ V`:

```
                      sectionsOfNhds f F V
  Γ(f _* F, V) ──────────────────────────────────→ Γ(ι^* F, ⊤)
              ╲                                          │
               ╲  fiberSectionsOfNhds f F y V hy          │ sectionsPullbackOver (f.fiberLift hy)
                ╲                                         ↓
                 ───────────────────────────────→ Γ(F_y, ⊤)
```
-/
lemma sectionsOfNhds_comp_sectionsPullbackOver (f : X ⟶ Y) (F : X.Modules) {V : Y.Opens} {y : Y}
    (hy : y ∈ V) :
    sectionsOfNhds f F V ≫ sectionsPullbackOver (f.fiberLift hy) (f.fiberLift_ι hy) F =
      fiberSectionsOfNhds f F y V hy := by
  have htop : (⊤ : (f.fiber y).Opens) ≤ (f.fiberLift hy ≫ (f ⁻¹ᵁ V).ι) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [f.fiberLift_ι hy]
    exact (f.preimage_fiberι_eq_top hy).ge
  rw [sectionsOfNhds, fiberSectionsOfNhds, Category.assoc]
  congr 1
  rw [sectionsPullbackOver, sectionsPullback,
    sectionsPullbackLE_comp_assoc _ _ F _ _ htop, sectionsPullbackLE_congr]

/-- `AlgebraicGeometry.Scheme.Modules.sectionsOfNhds_comp_sectionsPullbackOver` on a single
section. -/
lemma sectionsPullbackOver_fiberLift_sectionsOfNhds (f : X ⟶ Y) (F : X.Modules) {V : Y.Opens}
    {y : Y} (hy : y ∈ V) (z : Γ((pushforward f).obj F, V)) :
    sectionsPullbackOver (f.fiberLift hy) (f.fiberLift_ι hy) F (sectionsOfNhds f F V z) =
      fiberSectionsOfNhds f F y V hy z := by
  simpa using ConcreteCategory.congr_hom (sectionsOfNhds_comp_sectionsPullbackOver f F hy) z

/-- Restricting a section of `f _* F` to the fibre over `y` does not depend on the open
neighbourhood of `y` it is taken over. -/
lemma map_comp_fiberSectionsOfNhds (f : X ⟶ Y) (F : X.Modules) {V V' : Y.Opens} {y : Y}
    (hy : y ∈ V) (hV'V : V' ≤ V) (hy' : y ∈ V') :
    ((pushforward f).obj F).presheaf.map (homOfLE hV'V).op ≫ fiberSectionsOfNhds f F y V' hy' =
      fiberSectionsOfNhds f F y V hy := by
  rw [fiberSectionsOfNhds, fiberSectionsOfNhds, ← Category.assoc, eqToHom_pushforward_map,
    Category.assoc, map_sectionsPullbackLE]

/-- **The fibre of a pullback.** If `u : X ⟶ Y` induces an isomorphism `κ(u x) ≅ κ(x)` on
residue fields, then the fibre of `u^* F` at `x` is the fibre of `F` at `u x`, viewed as a
`κ(x)`-vector space along `κ(u x) ≅ κ(x)`. -/
noncomputable def fiberFunctorPullbackIso (u : X ⟶ Y) (x : X) [IsIso (u.residueFieldMap x)] :
    Modules.pullback u ⋙ fiberFunctor X x ≅
      fiberFunctor Y (u x) ⋙ ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom :=
  Functor.isoWhiskerRight (pullbackComp (X.fromSpecResidueField x) u)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight (pullbackCongr (u.SpecMap_residueFieldMap_fromSpecResidueField x).symm)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight
      (pullbackComp (Spec.map (u.residueFieldMap x)) (Y.fromSpecResidueField (u x))).symm
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerLeft (Modules.pullback (Y.fromSpecResidueField (u x)))
      (moduleSpecΓPullbackIso (u.residueFieldMap x))

/-- The fibre of `u^* F` at `x`, for `u` inducing an isomorphism on the residue field at `x`. -/
noncomputable def fiberPullbackIso (u : X ⟶ Y) (F : Y.Modules) (x : X)
    [IsIso (u.residueFieldMap x)] :
    ((Modules.pullback u).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).obj (F.fiber (u x)) :=
  (fiberFunctorPullbackIso u x).app F

/-- Naturality of the comparison between the fibre of a pullback and the pullback of a fibre:

```text
  (u^* M)(x) ── fiberMap ((pullback u).map φ) x ──▶ (u^* N)(x)
      │                                                 │
      │ (fiberPullbackIso u M x).hom                    │ (fiberPullbackIso u N x).hom
      ▼                                                 ▼
    M(u x) ── restrictScalars (fiberMap φ (u x)) ──────▶ N(u x)
```
-/
@[reassoc]
lemma fiberPullbackIso_hom_naturality (u : X ⟶ Y) (x : X) [IsIso (u.residueFieldMap x)]
    {M N : Y.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x ≫ (fiberPullbackIso u N x).hom =
      (fiberPullbackIso u M x).hom ≫
        (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).map (fiberMap φ (u x)) :=
  (fiberFunctorPullbackIso u x).hom.naturality φ

/-- **A morphism of sheaves of modules vanishes on the fibre at a point exactly when its
pullback does**, for a morphism inducing an isomorphism on the residue field at that point. This
is `AlgebraicGeometry.Scheme.Modules.fiberPullbackIso_hom_naturality` with both isomorphisms
cancelled.

`AlgebraicGeometry.Scheme.Modules.fiberMap_restrictFunctor_map_eq_zero_iff` is the same statement
for the restriction functor along an open immersion, proved from the corresponding naturality
square `AlgebraicGeometry.Scheme.Modules.fiberRestrictIso_hom_naturality`. -/
lemma fiberMap_pullback_map_eq_zero_iff (u : X ⟶ Y) (x : X) [IsIso (u.residueFieldMap x)]
    {M N : Y.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x = 0 ↔ fiberMap φ (u x) = 0 := by
  rw [← Preadditive.IsIso.comp_right_eq_zero (fiberMap ((Modules.pullback u).map φ) x)
      (fiberPullbackIso u N x).hom, fiberPullbackIso_hom_naturality,
    Preadditive.IsIso.comp_left_eq_zero, Functor.map_eq_zero_iff]

/-- **The fibre of a restriction to a fibre.** The fibre of `F_y` at a point `x` of the
scheme-theoretic fibre of `f` over `y` is the fibre of `F` at `f.fiberι y x`; the residue fields
`κ(f.fiberι y x)` and `κ(x)` agree because `f.fiberι y` is a preimmersion. -/
noncomputable def fiberRestrictToFiberIso (f : X ⟶ Y) (y : Y) (F : X.Modules) (x : f.fiber y) :
    ((restrictToFiber f y).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv ((f.fiberι y).residueFieldMap x)).hom).obj
        (F.fiber (f.fiberι y x)) :=
  fiberPullbackIso (f.fiberι y) F x

/-- The global sections of a sheaf of modules on the scheme-theoretic fibre `X_y` of
`f : X ⟶ Y` over `y : Y`, as a functor to `κ(y)`-vector spaces: the fibre is a scheme over
`Spec κ(y)`, and this is the direct image along that structure morphism, evaluated at the top
open. -/
noncomputable def fiberSectionsFunctor (f : X ⟶ Y) (y : Y) :
    (f.fiber y).Modules ⥤ ModuleCat (Y.residueField y) :=
  pushforward (f.fiberToSpecResidueField y) ⋙ moduleSpecΓFunctor (R := Y.residueField y)

/-- The `κ(y)`-vector space `Γ(X_y, F_y)` of global sections of the restriction of a sheaf of
`𝒪_X`-modules `F` to the fibre of `f : X ⟶ Y` over `y : Y`. -/
noncomputable abbrev fiberSections (f : X ⟶ Y) (F : X.Modules) (y : Y) :
    ModuleCat (Y.residueField y) :=
  (fiberSectionsFunctor f y).obj ((restrictToFiber f y).obj F)

/-- **The image `s(x)` of a global section in a fibre.** The fibre of `F` at `x` is the module of
global sections of the pullback of `F` along `Spec κ(x) ⟶ X`, so the image of a global section of
`F` in it is the pullback of sections along that morphism. It is semilinear over the evaluation
`Γ(X, 𝒪_X) ⟶ κ(x)` at `x`. -/
noncomputable def fiberMk (F : X.Modules) (x : X) :
    Γ(F, ⊤) →ₛₗ[(X.Γevaluation x).hom] F.fiber x where
  toFun := sectionsPullback (X.fromSpecResidueField x) F
  map_add' := map_add _
  map_smul' r s := by
    have h : (X.fromSpecResidueField x).appTop r =
        (Scheme.ΓSpecIso (X.residueField x)).inv (X.Γevaluation x r) := by
      rw [← ConcreteCategory.congr_hom (Scheme.fromSpecResidueField_appTop X x) r,
        ← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine (sectionsPullback_smul _ _ r s).trans ?_
    rw [h]
    rfl

lemma fiberMk_apply (F : X.Modules) (x : X) (s : Γ(F, ⊤)) :
    fiberMk F x s = sectionsPullback (X.fromSpecResidueField x) F s := rfl

/-- **The image in a fibre is natural in the sheaf of modules.**

```
              fiberMk F x
     Γ(F, ⊤) -------------> F(x)
        |                     |
        | Hom.app ψ ⊤         | fiberMap ψ x
        v                     v
     Γ(G, ⊤) -------------> G(x)
              fiberMk G x
```
-/
@[simp]
lemma fiberMap_fiberMk {F G : X.Modules} (ψ : F ⟶ G) (x : X) (s : Γ(F, ⊤)) :
    fiberMap ψ x (fiberMk F x s) = fiberMk G x (Hom.app ψ ⊤ s) :=
  sectionsPullback_naturality_apply (X.fromSpecResidueField x) ψ s

/-- A morphism of sheaves of modules taking a global section to one with non-zero image in the
fibre at `w` is non-zero on the fibre at `w`. -/
lemma fiberMap_ne_zero_of_fiberMk_ne_zero {Z : Scheme.{u}} {A G : Z.Modules} (ψ : A ⟶ G) (w : Z)
    (τ : Γ(A, ⊤)) (h : fiberMk G w (Hom.app ψ ⊤ τ) ≠ 0) : fiberMap ψ w ≠ 0 := by
  intro h0
  refine h ?_
  rw [← fiberMap_fiberMk ψ w τ, h0]
  simp

/-- **The fibre of the structure sheaf is the residue field.** A global function of `X` has zero
image in the fibre `𝒪_X(x) = κ(x)` exactly when it vanishes at `x`. -/
lemma fiberMk_unit_eq_zero_iff (x : X) (r : Γ(X, ⊤)) :
    fiberMk (unit X.ringCatSheaf) x r = 0 ↔ X.Γevaluation x r = 0 := by
  have hinj : Function.Injective
      (Hom.app (pullbackUnitIso (X.fromSpecResidueField x)).hom ⊤) :=
    (sectionsEquivOfIso (pullbackUnitIso (X.fromSpecResidueField x)) ⊤).injective
  have hΓinj : Function.Injective
      (ConcreteCategory.hom (Scheme.ΓSpecIso (X.residueField x)).hom) :=
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.injective
  have hmk : Hom.app (pullbackUnitIso (X.fromSpecResidueField x)).hom ⊤
      (fiberMk (unit X.ringCatSheaf) x r) = (X.fromSpecResidueField x).appTop r :=
    app_pullbackUnitIso_hom_sectionsPullback _ r
  have hev : X.Γevaluation x r =
      (Scheme.ΓSpecIso (X.residueField x)).hom ((X.fromSpecResidueField x).appTop r) :=
    (ConcreteCategory.congr_hom (Scheme.fromSpecResidueField_appTop X x) r).symm
  rw [hev, map_eq_zero_iff _ hΓinj, ← hmk, map_eq_zero_iff _ hinj]

/-- **A morphism which is invertible on a non-trivial fibre is non-zero there.** -/
lemma fiberMap_ne_zero_of_isIso_fiberMap {M N : X.Modules} (φ : M ⟶ N) (x : X)
    [Nontrivial (M.fiber x)] (h : IsIso (fiberMap φ x)) : fiberMap φ x ≠ 0 := by
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : M.fiber x)
  have hinj : Function.Injective (fiberMap φ x) :=
    ((ConcreteCategory.isIso_iff_bijective (fiberMap φ x)).1 h).1
  exact hv (hinj (by simp [hz]))

/-- **An isomorphism is non-zero on every non-trivial fibre.** -/
lemma fiberMap_ne_zero_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (x : X)
    [Nontrivial (M.fiber x)] : fiberMap φ x ≠ 0 :=
  fiberMap_ne_zero_of_isIso_fiberMap φ x inferInstance

/-- **A global function which is a unit does not vanish at any point.** The image in the fibre
`𝒪_X(x) = κ(x)` of a unit of `Γ(X, 𝒪_X)` is non-zero. -/
lemma fiberMk_unit_ne_zero_of_isUnit {r : Γ(X, ⊤)} (hr : IsUnit r) (x : X) :
    fiberMk (unit X.ringCatSheaf) x r ≠ 0 :=
  fun h ↦ (hr.map (X.Γevaluation x).hom).ne_zero ((fiberMk_unit_eq_zero_iff x r).mp h)

/-- **The fibre of a restriction to an open subscheme.** For an open immersion `f : Y ⟶ X` and a
point `y` of `Y`, the fibre at `y` of the restriction of an `𝒪ₓ`-module to `Y` is its fibre at
`f y`, viewed as a `κ(y)`-vector space along the isomorphism `κ(f y) ≅ κ(y)`.

```
                      restrictFunctor f
     X.Modules ─────────────────────────────→ Y.Modules
         │                                        │
         │ fiberFunctor X (f y)                   │ fiberFunctor Y y
         ↓                                        ↓
  ModuleCat κ(f y) ─────────────────────────→ ModuleCat κ(y)
                restrictScalars (inv (f.residueFieldMap y))
```
-/
noncomputable def fiberFunctorRestrictIso (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    restrictFunctor f ⋙ fiberFunctor Y y ≅
      fiberFunctor X (f y) ⋙ ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback f) _ ≪≫ fiberFunctorPullbackIso f y

/-- The fibre at `y` of the restriction of an `𝒪ₓ`-module to an open subscheme, as a
`κ(y)`-vector space along `κ(f y) ≅ κ(y)`; the object part of
`AlgebraicGeometry.Scheme.Modules.fiberFunctorRestrictIso`. -/
noncomputable def fiberRestrictIso (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (y : Y) :
    ((restrictFunctor f).obj M).fiber y ≅
      (ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom).obj (M.fiber (f y)) :=
  (fiberFunctorRestrictIso f y).app M

@[reassoc]
lemma fiberRestrictIso_hom_naturality (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) (y : Y) :
    fiberMap ((restrictFunctor f).map φ) y ≫ (fiberRestrictIso f N y).hom =
      (fiberRestrictIso f M y).hom ≫
        (ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom).map (fiberMap φ (f y)) :=
  (fiberFunctorRestrictIso f y).hom.naturality φ

/-- **A morphism of sheaves of modules vanishes on the fibre at a point of an open subscheme
exactly when its restriction to that open subscheme does.** This is
`AlgebraicGeometry.Scheme.Modules.fiberRestrictIso_hom_naturality` with both isomorphisms
cancelled.

It is the special case of `AlgebraicGeometry.Scheme.Modules.fiberMap_pullback_map_eq_zero_iff`
in which the morphism is an open immersion; the two are kept apart because the restriction
functor and the pullback functor are only isomorphic, not equal, so deducing this statement from
that one would cost the comparison `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
lemma fiberMap_restrictFunctor_map_eq_zero_iff (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) (y : Y) :
    fiberMap ((restrictFunctor f).map φ) y = 0 ↔ fiberMap φ (f y) = 0 := by
  rw [← Preadditive.IsIso.comp_right_eq_zero (fiberMap ((restrictFunctor f).map φ) y)
      (fiberRestrictIso f N y).hom, fiberRestrictIso_hom_naturality,
    Preadditive.IsIso.comp_left_eq_zero, Functor.map_eq_zero_iff]

end Fiber

section BaseChangeSquare

variable {X Y S T : Scheme.{u}} {v : X ⟶ Y} {f : Y ⟶ T} {g : X ⟶ S} {u : S ⟶ T}

/-- **The comparison of pullbacks around a commutative square** `v ≫ f = g ≫ u` of schemes:
pulling back along `u` and then along `g` is pulling back along `f` and then along `v`.

```
            v
      X ─────────→ Y                X.Modules ←─── v^* ─── Y.Modules
      │            │                    ↑                      ↑
    g │            │ f              g^* │          ⟸           │ f^*
      ↓            ↓                    │                      │
      S ─────────→ T                S.Modules ←─── u^* ─── T.Modules
            u
```

It is an isomorphism (`AlgebraicGeometry.Scheme.Modules.isIso_natTrans_pullbackTwoSquare`), but
it is packaged as a 2-square so that the base change transformation
`AlgebraicGeometry.Scheme.Modules.baseChange` can be obtained as its mate. -/
noncomputable def pullbackTwoSquare (w : v ≫ f = g ≫ u) :
    TwoSquare (Modules.pullback u) (Modules.pullback f) (Modules.pullback g)
      (Modules.pullback v) :=
  TwoSquare.mk _ _ _ _
    ((pullbackComp g u).hom ≫ (pullbackCongr w.symm).hom ≫ (pullbackComp v f).inv)

/-- The comparison of pullbacks around a commutative square is an isomorphism: it is a composite
of isomorphisms. -/
instance isIso_natTrans_pullbackTwoSquare (w : v ≫ f = g ≫ u) :
    IsIso (pullbackTwoSquare w).natTrans :=
  inferInstanceAs (IsIso ((pullbackComp g u).hom ≫ (pullbackCongr w.symm).hom ≫
    (pullbackComp v f).inv))

/-- **The base change transformation** `u^* ∘ f_* ⟶ g_* ∘ v^*` attached to a commutative square
`v ≫ f = g ≫ u` of schemes: the mate of the comparison of pullbacks
`AlgebraicGeometry.Scheme.Modules.pullbackTwoSquare`.

```
   Y.Modules ─────── f_* ──────→ T.Modules
       │                             │
   v^* │              ⟹              │ u^*
       ↓                             ↓
   X.Modules ─────── g_* ──────→ S.Modules
```
-/
noncomputable def baseChange (w : v ≫ f = g ≫ u) :
    TwoSquare (pushforward f) (Modules.pullback v) (Modules.pullback u) (pushforward g) :=
  mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction g)
    (pullbackTwoSquare w)

/-- **The mate identity for the base change transformation**: the base change map, pulled back
along `g` and followed by the counit of `g^* ⊣ g_*`, is the comparison of pullbacks followed by
the pullback along `v` of the counit of `f^* ⊣ f_*`.

```
   g^* u^* f_* M ─── g^*(bc) ───→ g^* g_* v^* M
         │                              │
         │ comparison                   │ ε_g
         ↓                              ↓
   v^* f^* f_* M ─── v^*(ε_f) ──→     v^* M
```
-/
@[reassoc]
lemma map_baseChange_comp_counit (w : v ≫ f = g ≫ u) (M : Y.Modules) :
    (Modules.pullback g).map ((baseChange w).natTrans.app M) ≫
        (pullbackPushforwardAdjunction g).counit.app ((Modules.pullback v).obj M) =
      (pullbackTwoSquare w).natTrans.app ((pushforward f).obj M) ≫
        (Modules.pullback v).map ((pullbackPushforwardAdjunction f).counit.app M) :=
  mateEquiv_counit _ _ _ M

end BaseChangeSquare

section FiberBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (y : Y)

/-- **The base change transformation for a scheme-theoretic fibre**: the specialisation of
`AlgebraicGeometry.Scheme.Modules.baseChange` to the fibre square of `f : X ⟶ Y` over `y : Y`.

```
   X.Modules ────────── f_* ─────────→ Y.Modules
       │                                   │
   v^* │                ⟹                  │ u^*
       ↓                                   ↓
 (X_y).Modules ─── g_* ───→ (Spec κ(y)).Modules
```

Here `v = f.fiberι y`, `u = Y.fromSpecResidueField y` and `g = f.fiberToSpecResidueField y`. -/
noncomputable abbrev fiberBaseChange :
    TwoSquare (pushforward f) (restrictToFiber f y)
      (Modules.pullback (Y.fromSpecResidueField y))
      (pushforward (f.fiberToSpecResidueField y)) :=
  baseChange (f.fiber_fac y)

/-- **The base change map for a fibre, as a natural transformation** from the fibre at `y` of
the direct image to the global sections on the fibre `X_y`: the global sections on `Spec κ(y)`
of `AlgebraicGeometry.Scheme.Modules.fiberBaseChange`.

```
   X.Modules ────────── f_* ⋙ (–)(y) ─────────→ ModuleCat κ(y)
       │                                              ║
   F ↦ F_y │                    ⟹                     ║
       ↓                                              ║
 (X_y).Modules ────── Γ(X_y, –) ────────────→ ModuleCat κ(y)
```
-/
noncomputable def fiberBaseChangeNatTrans :
    pushforward f ⋙ fiberFunctor Y y ⟶ restrictToFiber f y ⋙ fiberSectionsFunctor f y :=
  Functor.whiskerRight (fiberBaseChange f y).natTrans
    (moduleSpecΓFunctor (R := Y.residueField y))

/-- **The base change map** `(f_* F)(y) ⟶ Γ(X_y, F_y)`, from the fibre at `y` of the direct
image of `F` along `f : X ⟶ Y` to the global sections of the restriction of `F` to the fibre
`X_y`. It is a `κ(y)`-linear map, and it is natural in `F` by
`AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap_naturality`. -/
noncomputable def fiberBaseChangeMap :
    ((pushforward f).obj F).fiber y ⟶ fiberSections f F y :=
  (fiberBaseChangeNatTrans f y).app F

/-- The base change map is the image of the base change transformation under global sections
on `Spec κ(y)`. -/
lemma fiberBaseChangeMap_eq :
    fiberBaseChangeMap f F y =
      (moduleSpecΓFunctor (R := Y.residueField y)).map ((fiberBaseChange f y).natTrans.app F) :=
  rfl

variable {F} in
/-- **The base change map is natural in `F`.** -/
@[reassoc]
lemma fiberBaseChangeMap_naturality {G : X.Modules} (φ : F ⟶ G) :
    fiberMap ((pushforward f).map φ) y ≫ fiberBaseChangeMap f G y =
      fiberBaseChangeMap f F y ≫ (fiberSectionsFunctor f y).map ((restrictToFiber f y).map φ) :=
  (fiberBaseChangeNatTrans f y).naturality φ

end FiberBaseChange

section OverBase

variable {X : Scheme.{u}} (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- The global sections of a sheaf of modules on a scheme over `Spec R` form an `R`-module, by
restriction of scalars along the structure map `R → Γ(X, 𝒪ₓ)`.

Mathlib leaves `Module.compHom` a reducible non-instance, because a restriction-of-scalars
structure along an arbitrary ring homomorphism clashes with the structures already carried by
the target. Here the ring homomorphism is not a parameter: it is determined by `R` and by the
`X.Over (Spec (.of R))` instance, both of which typeclass inference reads off the goal, and
`Γ(F, ⊤)` carries no other `R`-module structure. So this one is declared as an instance.

Only sections over `⊤` carry this structure: the analogous structure over an open `U` would
restrict scalars along `R → Γ(X, ⊤) → Γ(X, U)` and would give a second, non-definitionally-equal
`R`-module structure on `Γ(F, ⊤)` for `U = ⊤`. -/
noncomputable instance module_sections (F : X.Modules) : Module R Γ(F, ⊤) :=
  Module.compHom _ (Scheme.overRingHom R X)

lemma smul_sections_def (F : X.Modules) (r : R) (s : Γ(F, ⊤)) :
    r • s = Scheme.overRingHom R X r • s :=
  rfl

instance isScalarTower_sections (F : X.Modules) : IsScalarTower R Γ(X, ⊤) Γ(F, ⊤) :=
  ⟨fun _ r s ↦ mul_smul _ r s⟩

/-- An isomorphism of sheaves of modules on a scheme over `Spec R` identifies their global
sections as `R`-modules. -/
noncomputable def sectionsBaseEquivOfIso {F G : X.Modules} (e : F ≅ G) :
    Γ(F, ⊤) ≃ₗ[R] Γ(G, ⊤) where
  __ := (sectionsEquivOfIso e ⊤).toAddEquiv
  map_smul' r s := (sectionsEquivOfIso e ⊤).map_smul (Scheme.overRingHom R X r) s

variable {R}

/-- **The global functions of `X` are free of rank one over the base ring.** If the structure
morphism of `X` over `Spec R` identifies `R` with `Γ(X, 𝒪ₓ)`, then `Γ(X, 𝒪ₓ)` is a free
`R`-module of rank one, a generator being the unit. -/
noncomputable def sectionsUnitEquiv
    (hπ : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop)) :
    R ≃ₗ[R] Γ(unit X.ringCatSheaf, ⊤) where
  __ := (Scheme.overRingEquiv R X hπ).toAddEquiv
  map_smul' := map_mul (Scheme.overRingEquiv R X hπ)

/-- **`h⁰(X, 𝒪ₓ) = 1`.** If the structure morphism of `X` over `Spec R` identifies `R` with
`Γ(X, 𝒪ₓ)`, the global functions of `X` are a one-dimensional `R`-module. -/
theorem finrank_sections_unit_eq_one [Nontrivial R]
    (hπ : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop)) :
    Module.finrank R Γ(unit X.ringCatSheaf, ⊤) = 1 := by
  rw [← (sectionsUnitEquiv hπ).finrank_eq, Module.finrank_self]

end OverBase

section IsIsoLocal

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **A morphism of sheaves of modules which is locally an isomorphism is an isomorphism**: if
every point has an open neighbourhood `W` such that the morphism is invertible on sections over
every open subset of `W`, then it is an isomorphism. -/
theorem isIso_of_forall_exists_isIso_app (φ : M ⟶ N)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W → IsIso (Hom.app φ V)) :
    IsIso φ := by
  choose W hxW hW using h
  rw [Hom.isIso_iff_isIso_app]
  intro U
  let S : Sieve U :=
    { arrows V _ := ∃ x : X, V ≤ W x
      downward_closed hV g := hV.imp fun _ hx ↦ (leOfHom g).trans hx }
  have hS : S ∈ Opens.grothendieckTopology X U :=
    fun x hx ↦ ⟨U ⊓ W x, homOfLE inf_le_left, ⟨x, inf_le_right⟩, hx, hxW x⟩
  refine Presheaf.isIso_app_of_isIso_app_of_mem (Opens.grothendieckTopology X)
    M.isSheaf N.isSheaf φ.mapPresheaf S hS fun V f hV ↦ ?_
  obtain ⟨x, hx⟩ := hV
  exact hW x V hx

/-- **Being an isomorphism is local on the base**: a morphism of sheaves of modules whose
restriction to every member of an open cover of `X` is an isomorphism is an isomorphism. -/
theorem isIso_of_isOpenCover_restrict {ι : Type*} {U : ι → X.Opens} (hU : IsOpenCover U)
    (φ : M ⟶ N) (h : ∀ i, IsIso ((restrictFunctor (U i).ι).map φ)) : IsIso φ := by
  refine isIso_of_forall_exists_isIso_app φ fun x ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU.iSup_eq_top.ge (Opens.mem_top x))
  refine ⟨U i, hi, fun V hV ↦ ?_⟩
  obtain ⟨V', rfl⟩ := Scheme.Opens.exists_image_eq_of_le hV
  rw [← Hom.app_restrictFunctor_ι_map φ V']
  have := h i
  infer_instance

/-- **A morphism of sheaves of modules which vanishes on the sections over every small enough
open subset is zero.** This is the additive companion of
`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_isIso_app`. -/
theorem eq_zero_of_forall_exists_app_eq_zero (φ : M ⟶ N)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W → Hom.app φ V = 0) : φ = 0 := by
  choose W hxW hW using h
  have key (V : X.Opens) (m : Γ(M, V)) : Hom.app φ V m = 0 := by
    refine N.isSheaf.section_ext (U := .op V) (s := Hom.app φ V m) (t := 0) fun x hx ↦
      ⟨V ⊓ W x, inf_le_left, ⟨hx, hxW x⟩, ?_⟩
    have hnat := ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE (inf_le_left : V ⊓ W x ≤ V)).op) m
    simp only [mapPresheaf_app, ConcreteCategory.comp_apply] at hnat
    rw [← hnat, hW x (V ⊓ W x) inf_le_right]
    simp
  ext V m
  simpa using key V m

/-- **Vanishing is local on the base**: a morphism of sheaves of modules whose restriction to
every member of an open cover of `X` is zero is zero. This is the additive companion of
`AlgebraicGeometry.Scheme.Modules.isIso_of_isOpenCover_restrict`. -/
theorem eq_zero_of_isOpenCover_restrict {ι : Type*} {U : ι → X.Opens} (hU : IsOpenCover U)
    (φ : M ⟶ N) (h : ∀ i, (restrictFunctor (U i).ι).map φ = 0) : φ = 0 := by
  refine eq_zero_of_forall_exists_app_eq_zero φ fun x ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU.iSup_eq_top.ge (Opens.mem_top x))
  refine ⟨U i, hi, fun V hV ↦ ?_⟩
  obtain ⟨V', rfl⟩ := Scheme.Opens.exists_image_eq_of_le hV
  rw [← Hom.app_restrictFunctor_ι_map φ V', h i, Hom.zero_app]

end IsIsoLocal

section Subsingleton

variable {X : Scheme.{u}}

instance subsingleton_sections_bot (M : X.Modules) : Subsingleton Γ(M, ⊥) :=
  Module.subsingleton Γ(X, ⊥) Γ(M, ⊥)

instance subsingleton_sections_top_of_isEmpty [IsEmpty X] (M : X.Modules) :
    Subsingleton Γ(M, ⊤) := by
  have h : (⊤ : X.Opens) = ⊥ := by ext x; exact (IsEmpty.false x).elim
  rw [h]
  infer_instance

/-- On a scheme with at most one point, a morphism of `𝒪ₓ`-modules is an isomorphism as soon as
it is one on sections over `⊤`. -/
theorem isIso_of_isIso_app_top [Subsingleton X] {M N : X.Modules} (φ : M ⟶ N)
    (h : IsIso (φ.app ⊤)) : IsIso φ := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  -- the only open subsets of `X` are `⊥` and `⊤`, and all sections over `⊥` vanish
  rcases U.eq_bot_or_top with rfl | rfl
  · rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact h

/-- The compatible family of sections of an `𝒪ₓ`-module cut out by a single global section, by
restriction to the various open subsets. -/
noncomputable def sectionsMkTop (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun _ ↦ M.val.map (homOfLE le_top).op m) (fun _ _ _ ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    exact M.val.congr_map_apply (Subsingleton.elim _ _) m)

/-- The morphism `𝒪ₓ ⟶ M` of `𝒪ₓ`-modules determined by a global section `m` of `M`; it sends
a section `r` of the structure sheaf to `r • m`, see
`AlgebraicGeometry.Scheme.Modules.homOfSectionTop_app_top`. -/
noncomputable def homOfSectionTop (M : X.Modules) (m : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionsMkTop M m)

@[simp]
theorem homOfSectionTop_app_top (M : X.Modules) (m : Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    Hom.app (homOfSectionTop M m) ⊤ r = r • m := by
  have h₀ := SheafOfModules.unitHomEquiv_apply_coe M (homOfSectionTop M m) (.op ⊤)
  simp only [homOfSectionTop, Equiv.apply_symm_apply] at h₀
  have h : Hom.app (homOfSectionTop M m) ⊤ (1 : Γ(X, ⊤)) = m :=
    h₀.symm.trans (by simp [sectionsMkTop])
  calc Hom.app (homOfSectionTop M m) ⊤ r
      = Hom.app (homOfSectionTop M m) ⊤ (r • (1 : Γ(X, ⊤))) := by rw [smul_eq_mul, mul_one]
    _ = r • m := by rw [Hom.app_smul, h]

/-- **On a scheme with at most one point, a global section that generates the global sections
trivialises the module**: if `r ↦ r • m` is bijective on global sections, then the morphism
`𝒪ₓ ⟶ M` determined by `m` is an isomorphism. -/
theorem isIso_homOfSectionTop [Subsingleton X] {M : X.Modules} (m : Γ(M, ⊤))
    (hm : Function.Bijective fun r : Γ(X, ⊤) ↦ r • m) : IsIso (homOfSectionTop M m) := by
  refine isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective, funext (homOfSectionTop_app_top M m)]
  exact hm

end Subsingleton

section Vanishing

variable {X : Scheme.{u}}

/-- A global section `s` of a sheaf of `𝒪ₓ`-modules `F` **vanishes at** a point `x` of `X` if its
germ at `x` lies in `𝔪ₓ Fₓ`.

For the structure sheaf this is the complement of the basic open subset of `s`, by
`AlgebraicGeometry.Scheme.Modules.vanishesAt_structureModules_iff`. -/
def VanishesAt (F : X.Modules) (s : Γ(F, ⊤)) (x : X) : Prop :=
  F.presheaf.germ ⊤ x trivial s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
    (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))

lemma vanishesAt_iff (F : X.Modules) (s : Γ(F, ⊤)) (x : X) :
    F.VanishesAt s x ↔ F.presheaf.germ ⊤ x trivial s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
  Iff.rfl

/-- **The global sections vanishing at a point form a submodule** of `Γ(X, F)` over the global
functions `Γ(X, 𝒪ₓ)`. -/
noncomputable def vanishingSubmodule (F : X.Modules) (x : X) : Submodule Γ(X, ⊤) Γ(F, ⊤) where
  carrier := {s | F.VanishesAt s x}
  add_mem' hs ht := by simpa [VanishesAt, map_add] using Submodule.add_mem _ hs ht
  zero_mem' := by simp [VanishesAt]
  smul_mem' r s hs := by
    have h := germ_smul F (U := ⊤) x trivial r s
    change F.presheaf.germ ⊤ x trivial (r • s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))
    rw [h]
    exact Submodule.smul_mem _ _ hs

/-- Membership of `AlgebraicGeometry.Scheme.Modules.vanishingSubmodule` is vanishing at the
point. -/
@[simp]
lemma mem_vanishingSubmodule_iff (F : X.Modules) (s : Γ(F, ⊤)) (x : X) :
    s ∈ F.vanishingSubmodule x ↔ F.VanishesAt s x :=
  Iff.rfl

/-- **A sheaf of `𝒪ₓ`-modules whose sections are locally spanned by a family of global sections
is generated by that family.** If every section of `M` over every open subset `U` becomes, on a
neighbourhood `V ⊆ U` of any prescribed point, a `Γ(X, V)`-linear combination of the
restrictions of the global sections `m i`, then `M` is generated by its global sections.

This is `SheafOfModules.isGloballyGenerated_of_forall_exists_mem_span` in the section API of
`X.Modules`; it is the counterpart, in the opposite direction, of
`AlgebraicGeometry.Scheme.Modules.exists_mem_span_germ_eq`. -/
theorem isGloballyGenerated_of_forall_exists_mem_span {M : X.Modules} {I : Type u}
    (m : I → Γ(M, ⊤))
    (h : ∀ (U : X.Opens) (t : Γ(M, U)) (x : X), x ∈ U →
      ∃ V : X.Opens, ∃ hVU : V ≤ U, x ∈ V ∧
        M.presheaf.map (homOfLE hVU).op t ∈ Submodule.span Γ(X, V)
          (Set.range fun i ↦ M.presheaf.map (homOfLE (le_top (a := V))).op (m i))) :
    M.IsGloballyGenerated :=
  SheafOfModules.isGloballyGenerated_of_forall_exists_mem_span (fun i ↦ sectionsMkTop M (m i)) h

/-- A sheaf of modules is **generated by its global sections at a point** `x` if the germs at `x`
of its global sections span the stalk `Fₓ` over the local ring `𝒪_{X, x}`.

This is the pointwise shadow of `SheafOfModules.IsGloballyGenerated`, and follows from it by
`AlgebraicGeometry.Scheme.Modules.isGloballyGeneratedAt_of_isGloballyGenerated`. -/
def IsGloballyGeneratedAt (F : X.Modules) (x : X) : Prop :=
  Submodule.span (X.presheaf.stalk x) (Set.range (F.presheaf.germ ⊤ x trivial)) = ⊤

/-- Every element of a stalk of a sheaf of modules generated by its global sections is the germ
of a `Γ(X, V)`-linear combination of restrictions of global sections.

This is `SheafOfModules.exists_mem_span_germ_eq` in the germ API of `X.Modules`, with the
generating sections read as global sections of `F`. -/
theorem exists_mem_span_germ_eq (F : X.Modules) [F.IsGloballyGenerated] (x : X)
    (z : F.presheaf.stalk x) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (t : Γ(F, V)),
      t ∈ Submodule.span Γ(X, V)
          (Set.range fun s : Γ(F, ⊤) ↦ F.presheaf.map (homOfLE (le_top (a := V))).op s) ∧
        F.presheaf.germ V x hxV t = z := by
  obtain ⟨V, hxV, t, ht, hz⟩ := SheafOfModules.exists_mem_span_germ_eq F x z
  refine ⟨V, hxV, t, Submodule.span_mono ?_ ht, hz⟩
  rintro _ ⟨s, rfl⟩
  exact ⟨PresheafOfModules.sections.eval s (op ⊤), PresheafOfModules.sections_property s _⟩

/-- **A sheaf of modules generated by its global sections is generated by its global sections at
every point**: the germs at `x` of the global sections of `F` span the stalk `Fₓ` over the local
ring `𝒪_{X, x}`.

By `AlgebraicGeometry.Scheme.Modules.exists_mem_span_germ_eq`, every element of `Fₓ` is the germ
of a section over some open neighbourhood `V` of `x` which is a `Γ(X, V)`-linear combination of
restrictions of global sections; the germ map is semilinear over the germ map on functions
(`AlgebraicGeometry.Scheme.Modules.germₛₗ`), so it turns such a combination into an
`𝒪_{X, x}`-linear combination of germs of global sections. -/
theorem isGloballyGeneratedAt_of_isGloballyGenerated (F : X.Modules) [F.IsGloballyGenerated]
    (x : X) :
    F.IsGloballyGeneratedAt x := by
  refine Submodule.eq_top_iff'.2 fun z ↦ ?_
  obtain ⟨V, hxV, t, ht, rfl⟩ := exists_mem_span_germ_eq F x z
  refine Submodule.span_le.2 ?_
    (Submodule.image_span_subset_span (germₛₗ F ⟨x, hxV⟩) _ ⟨t, ht, rfl⟩)
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨s, (F.presheaf.germ_res_apply (homOfLE le_top) x hxV s).symm⟩

/-- **Nakayama's lemma in the form of a non-vanishing global section.** If `F` is generated by its
global sections at `x` and the stalk `Fₓ` is a non-zero finite module over the local ring
`𝒪_{X, x}`, then some global section of `F` does not vanish at `x`. -/
theorem exists_not_vanishesAt (F : X.Modules) (x : X) [Nontrivial (F.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x)]
    (hgg : F.IsGloballyGeneratedAt x) :
    ∃ s : Γ(F, ⊤), ¬ F.VanishesAt s x := by
  by_contra h
  push Not at h
  -- were every global section to vanish at `x`, the stalk they span would be `𝔪ₓ Fₓ`
  have hle : Submodule.span (X.presheaf.stalk x)
      (Set.range (F.presheaf.germ ⊤ x trivial)) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤ :=
    Submodule.span_le.2 (by rintro - ⟨s, rfl⟩; exact h s)
  rw [hgg] at hle
  exact absurd (le_antisymm le_top hle)
    (Submodule.ideal_smul_top_lt_top (M := F.presheaf.stalk x) le_rfl).ne

/-- The unit global function of `X`, as a section of the structure sheaf viewed as a sheaf of
modules over itself. -/
noncomputable def oneSection (X : Scheme.{u}) (U : X.Opens) : Γ(X.structureModules, U) :=
  (1 : Γ(X, U))

@[simp]
lemma map_oneSection (U V : X.Opens) (i : op U ⟶ op V) :
    X.structureModules.presheaf.map i (oneSection X U) = oneSection X V :=
  (X.presheaf.map i).hom.map_one

/-- **The unit section is the unit for the module structure**: acting by a function `r` on the
unit section of the structure sheaf gives back `r`. -/
@[simp]
lemma smul_oneSection (U : X.Opens) (r : Γ(X, U)) :
    r • oneSection X U = (r : Γ(X.structureModules, U)) :=
  mul_one r

lemma germ_oneSection_res (x : X) (U : X.Opens) (hx : x ∈ U) :
    X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤)
      = X.structureModules.presheaf.germ U x hx (oneSection X U) := by
  rw [← map_oneSection ⊤ U (homOfLE le_top).op, X.structureModules.presheaf.germ_res_apply]

/-- **The germ of a function is a multiple of the germ of the unit section**: in the structure
sheaf viewed as a sheaf of modules, the germ of `t` is the germ of `t` in the local ring
`𝒪_{X, x}` acting on the germ of `1`. -/
lemma germ_structureModules_eq_smul (x : X) (U : X.Opens) (hx : x ∈ U) (t : Γ(X, U)) :
    X.structureModules.presheaf.germ U x hx t
      = X.presheaf.germ U x hx t • X.structureModules.presheaf.germ U x hx (oneSection X U) := by
  conv_lhs => rw [← smul_oneSection U t]
  exact germ_smul X.structureModules x hx t (oneSection X U)

lemma germ_oneSection_ne_zero (x : X) :
    X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤) ≠ 0 := by
  intro h
  rw [show (0 : X.structureModules.presheaf.stalk x) =
    X.structureModules.presheaf.germ ⊤ x trivial 0 by simp] at h
  obtain ⟨W, hxW, iWU, _iWV, heq⟩ :=
    X.structureModules.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial _ _ h
  rw [map_zero, map_oneSection ⊤ W iWU.op] at heq
  have h1 : (1 : Γ(X, W)) = 0 := heq
  exact one_ne_zero (α := X.presheaf.stalk x)
    (by rw [← map_one (X.presheaf.germ W x hxW).hom, h1, map_zero])

instance nontrivial_stalk_structureModules (x : X) :
    Nontrivial (X.structureModules.presheaf.stalk x) :=
  nontrivial_of_ne _ _ (germ_oneSection_ne_zero x)

lemma span_germ_oneSection (x : X) :
    Submodule.span (X.presheaf.stalk x)
      {X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤)} = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨U, hxU, t, rfl⟩ := X.structureModules.presheaf.exists_germ_eq z
  rw [germ_oneSection_res x U hxU, germ_structureModules_eq_smul x U hxU t]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

instance finite_stalk_structureModules (x : X) :
    Module.Finite (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x) :=
  ⟨span_germ_oneSection x ▸ Submodule.fg_span_singleton _⟩

/-- A multiple of the germ of the unit section of the structure sheaf vanishes exactly when the
multiplier does. -/
lemma smul_germ_oneSection_eq_zero_iff (x : X) (r : X.presheaf.stalk x) :
    r • X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤) = 0 ↔ r = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_smul]⟩
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [germ_oneSection_res x U hxU, ← germ_structureModules_eq_smul x U hxU a,
    ← map_zero (ConcreteCategory.hom (X.structureModules.presheaf.germ U x hxU))] at h
  obtain ⟨V, hxV, iVU, _, heq⟩ := X.structureModules.presheaf.germ_eq x hxU hxU _ _ h
  rw [map_zero] at heq
  -- the sections of `X.structureModules` over an open are the functions there, and the
  -- restriction maps of the two sheaves agree, so `heq` is an equation in `Γ(X, V)`
  have hz : X.presheaf.map iVU.op a = 0 := heq
  rw [← X.presheaf.germ_res_apply iVU x hxV a, hz, map_zero]

/-- **The stalk of the structure sheaf, viewed as a sheaf of modules over itself, is the local
ring**, the unit section being a basis. -/
noncomputable def stalkStructureModulesLinearEquiv (X : Scheme.{u}) (x : X) :
    X.structureModules.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x)
      (X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤)))
    ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro r hr
      exact (smul_germ_oneSection_eq_zero_iff x r).1 hr,
    by
      rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range]
      exact span_germ_oneSection x⟩).symm

/-- Under the identification of the stalk of the structure sheaf as a sheaf of modules with the
local ring, the germ of a function is its germ. -/
@[simp]
lemma stalkStructureModulesLinearEquiv_germ (x : X) (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)) :
    stalkStructureModulesLinearEquiv X x (X.structureModules.presheaf.germ U x hx s) =
      X.presheaf.germ U x hx s := by
  apply (stalkStructureModulesLinearEquiv X x).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change X.structureModules.presheaf.germ U x hx s =
    LinearMap.toSpanSingleton _ _ (X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤))
      (X.presheaf.germ U x hx s)
  rw [LinearMap.toSpanSingleton_apply, germ_oneSection_res x U hx,
    germ_structureModules_eq_smul x U hx s]

instance flat_stalk_structureModules (x : X) :
    Module.Flat (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x) :=
  Module.Flat.of_linearEquiv (stalkStructureModulesLinearEquiv X x)

/-- **The structure sheaf is generated by its global sections at every point**, the unit section
already generating the stalk.

This is a special case of
`AlgebraicGeometry.Scheme.Modules.isGloballyGeneratedAt_of_isGloballyGenerated`, but the direct
proof is kept: it only uses `AlgebraicGeometry.Scheme.Modules.span_germ_oneSection`, whereas the
instance `SheafOfModules.IsGloballyGenerated (SheafOfModules.unit _)` lives in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, which this file does not
import. -/
theorem isGloballyGeneratedAt_structureModules (x : X) :
    X.structureModules.IsGloballyGeneratedAt x :=
  eq_top_iff.2 <| (span_germ_oneSection x).ge.trans
    (Submodule.span_mono (Set.singleton_subset_iff.2 ⟨oneSection X ⊤, rfl⟩))

/-- **A global function vanishes at `x` exactly when `x` is outside its basic open subset.** This
identifies `AlgebraicGeometry.Scheme.Modules.VanishesAt` for the structure sheaf with the notion
of vanishing used by `AlgebraicGeometry.Scheme.basicOpen`. -/
lemma vanishesAt_structureModules_iff (x : X) (r : Γ(X, ⊤)) :
    X.structureModules.VanishesAt r x ↔ x ∉ X.basicOpen r := by
  rw [Scheme.mem_basicOpen_top, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  have hr := germ_structureModules_eq_smul x ⊤ trivial r
  constructor
  · intro h
    replace h : X.structureModules.presheaf.germ ⊤ x trivial r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x)) := h
    by_contra hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
    obtain ⟨u, hu⟩ := hu
    -- the germ of `r` is a unit, so the germ of `1` would lie in `𝔪ₓ 𝒪_{X, x}` as well
    have hmem := Submodule.smul_mem (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x)))
      ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) h
    rw [hr, ← hu, smul_smul, Units.inv_mul, one_smul] at hmem
    have hspan : Submodule.span (X.presheaf.stalk x)
        {X.structureModules.presheaf.germ ⊤ x trivial (oneSection X ⊤)} ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤ :=
      Submodule.span_le.2 (Set.singleton_subset_iff.2 hmem)
    rw [span_germ_oneSection] at hspan
    exact absurd (le_antisymm le_top hspan)
      (Submodule.ideal_smul_top_lt_top (R := X.presheaf.stalk x)
        (M := X.structureModules.presheaf.stalk x)
        (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) le_rfl).ne
  · intro h
    change X.structureModules.presheaf.germ ⊤ x trivial r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (X.structureModules.presheaf.stalk x))
    rw [hr]
    exact Submodule.smul_mem_smul h Submodule.mem_top

end Vanishing

section UnitHom

variable {X : Scheme.{u}} {M : X.Modules}

/-- **A compatible family of sections of a sheaf of `𝒪ₓ`-modules is determined by its global
term.** Restriction to `⊤` identifies `M.sections` with `Γ(M, ⊤)`, because `⊤` is the terminal
object of `X.Opens`; the inverse bijection is
`AlgebraicGeometry.Scheme.Modules.sectionsMkTop`. -/
noncomputable def sectionsEquivTop (M : X.Modules) : M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun := sectionsMkTop M
  left_inv s := by
    ext U
    exact PresheafOfModules.sections_property s (homOfLE le_top).op
  right_inv m := by simp [sectionsMkTop]

/-- **A morphism from the structure sheaf is the same thing as a global section**: the bijection
`(𝒪ₓ ⟶ M) ≃ Γ(M, ⊤)` sends a morphism to the image of the unit function, and a global section
`m` to multiplication by `m`, that is to
`AlgebraicGeometry.Scheme.Modules.homOfSectionTop`.

This is Mathlib's `SheafOfModules.unitHomEquiv` followed by
`AlgebraicGeometry.Scheme.Modules.sectionsEquivTop`. -/
noncomputable def unitHomEquivTop (M : X.Modules) : (X.structureModules ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (sectionsEquivTop M)

@[simp]
lemma unitHomEquivTop_apply (φ : X.structureModules ⟶ M) :
    unitHomEquivTop M φ = Hom.app φ ⊤ (oneSection X ⊤) := rfl

@[simp]
lemma unitHomEquivTop_symm_apply (m : Γ(M, ⊤)) :
    (unitHomEquivTop M).symm m = homOfSectionTop M m := rfl

/-- **The morphism attached to a global section sends the unit function to that section.** -/
@[simp]
lemma app_homOfSectionTop_oneSection (M : X.Modules) (m : Γ(M, ⊤)) :
    Hom.app (homOfSectionTop M m) ⊤ (oneSection X ⊤) = m :=
  (unitHomEquivTop M).apply_symm_apply m

/-- **On stalks, multiplication by a global section is multiplication by its germ.** -/
lemma Hom.stalkMap_homOfSectionTop (M : X.Modules) (m : Γ(M, ⊤)) (x : X)
    (z : X.structureModules.presheaf.stalk x) :
    Hom.stalkMap (homOfSectionTop M m) x z =
      stalkStructureModulesLinearEquiv X x z • M.presheaf.germ ⊤ x trivial m := by
  obtain ⟨U, hx, s, rfl⟩ := X.structureModules.presheaf.exists_germ_eq z
  rw [stalkStructureModulesLinearEquiv_germ, germ_structureModules_eq_smul x U hx s,
    Hom.stalkMap_smul, ← germ_oneSection_res x U hx, Hom.germ_stalkMap_apply,
    app_homOfSectionTop_oneSection]

/-- **Multiplication by a global section is zero exactly when the section is.** -/
@[simp]
lemma homOfSectionTop_eq_zero_iff (M : X.Modules) (m : Γ(M, ⊤)) :
    homOfSectionTop M m = 0 ↔ m = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hval := app_homOfSectionTop_oneSection M m
    rw [h, Hom.zero_app] at hval
    simpa using hval.symm
  · subst h
    refine (unitHomEquivTop M).injective ?_
    simp

/-- **A morphism from the structure sheaf is multiplication by a global section**: over any open
`U` it sends a function `r` to `r` acting on the restriction to `U` of the global section
`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` attached to it. -/
lemma Hom.app_eq_smul_res (φ : X.structureModules ⟶ M) (U : X.Opens) (r : Γ(X, U)) :
    Hom.app φ U r =
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (unitHomEquivTop M φ) := by
  have hnat := Hom.naturality_apply φ (homOfLE (le_top : U ≤ ⊤)) (oneSection X ⊤)
  rw [map_oneSection] at hnat
  conv_lhs => rw [← smul_oneSection U r]
  rw [Hom.app_smul, hnat]
  rfl

/-- **Multiplication by a global section acts on sections by scalar multiplication**: over an
open `U` the morphism `AlgebraicGeometry.Scheme.Modules.homOfSectionTop M m` sends a function
`r` to `r` acting on the restriction of `m` to `U`. -/
@[simp]
lemma Hom.app_homOfSectionTop (M : X.Modules) (m : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    Hom.app (homOfSectionTop M m) U r =
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m := by
  rw [Hom.app_eq_smul_res, ← unitHomEquivTop_symm_apply, Equiv.apply_symm_apply]

/-- The global function attached to an endomorphism of the structure sheaf of a scheme: the
image of the unit function. The endomorphism is multiplication by it, see
`AlgebraicGeometry.Scheme.Modules.Hom.app_eq_mul_endSection`, and this identifies the
endomorphism ring of `𝒪ₓ` with `Γ(X, 𝒪ₓ)`, see
`AlgebraicGeometry.Scheme.Modules.endSectionRingEquiv`. -/
noncomputable def endSection (ψ : X.structureModules ⟶ X.structureModules) : Γ(X, ⊤) :=
  unitHomEquivTop X.structureModules ψ

/-- **An endomorphism of the structure sheaf is multiplication by a global function**, namely by
`AlgebraicGeometry.Scheme.Modules.endSection`. -/
lemma Hom.app_eq_mul_endSection (ψ : X.structureModules ⟶ X.structureModules) (U : X.Opens)
    (r : Γ(X, U)) :
    (Hom.app ψ U r : Γ(X, U)) =
      r * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (endSection ψ) :=
  Hom.app_eq_smul_res ψ U r

@[simp]
lemma endSection_id : endSection (𝟙 X.structureModules) = 1 := rfl

@[simp]
lemma endSection_comp (ψ ψ' : X.structureModules ⟶ X.structureModules) :
    endSection (ψ ≫ ψ') = endSection ψ * endSection ψ' := by
  have hid : X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op =
      𝟙 (X.presheaf.obj (op (⊤ : X.Opens))) := by
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (𝟙 (op (⊤ : X.Opens))),
      CategoryTheory.Functor.map_id]
  calc endSection (ψ ≫ ψ') = Hom.app ψ' ⊤ (endSection ψ) := rfl
    _ = endSection ψ * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (endSection ψ') :=
        Hom.app_eq_mul_endSection ψ' ⊤ (endSection ψ)
    _ = endSection ψ * endSection ψ' := by rw [hid, ConcreteCategory.id_apply]

/-- **The endomorphism ring of the structure sheaf is the ring of global functions.** An
endomorphism of `𝒪ₓ` as a sheaf of modules over itself is multiplication by the global function
`AlgebraicGeometry.Scheme.Modules.endSection`, and every global function arises this way, from
`AlgebraicGeometry.Scheme.Modules.homOfSectionTop`. -/
noncomputable def endSectionRingEquiv (X : Scheme.{u}) : End X.structureModules ≃+* Γ(X, ⊤) where
  toFun := endSection
  invFun := homOfSectionTop X.structureModules
  left_inv := (unitHomEquivTop X.structureModules).left_inv
  right_inv := (unitHomEquivTop X.structureModules).right_inv
  map_add' _ _ := rfl
  map_mul' ψ ψ' := (endSection_comp ψ' ψ).trans (mul_comm _ _)

@[simp]
lemma endSectionRingEquiv_apply (ψ : End X.structureModules) :
    endSectionRingEquiv X ψ = endSection ψ := rfl

@[simp]
lemma endSectionRingEquiv_symm_apply (a : Γ(X, ⊤)) :
    (endSectionRingEquiv X).symm a = homOfSectionTop X.structureModules a := rfl

/-- **An endomorphism of the structure sheaf is determined by the corresponding global
function.** -/
lemma endSection_injective : Function.Injective (endSection (X := X)) :=
  (endSectionRingEquiv X).injective

@[simp]
lemma endSection_homOfSectionTop (a : Γ(X, ⊤)) :
    endSection (homOfSectionTop X.structureModules a) = a :=
  app_homOfSectionTop_oneSection X.structureModules a

@[simp]
lemma homOfSectionTop_endSection (ψ : X.structureModules ⟶ X.structureModules) :
    homOfSectionTop X.structureModules (endSection ψ) = ψ :=
  (endSectionRingEquiv X).symm_apply_apply ψ

/-- **An endomorphism of the structure sheaf is an isomorphism exactly when the corresponding
global function is a unit**, the inverse then being multiplication by the inverse function. -/
theorem isIso_iff_isUnit_endSection (ψ : X.structureModules ⟶ X.structureModules) :
    IsIso ψ ↔ IsUnit (endSection ψ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ((isUnit_iff_isIso (ψ : End X.structureModules)).2 h).map (endSectionRingEquiv X)
  · refine (isUnit_iff_isIso (ψ : End X.structureModules)).1 ?_
    simpa using h.map (endSectionRingEquiv X).symm

/-- **The fibre of a global function.** The image in the fibre `𝒪ₓ(x)` of a global function `r`
is its value at `x` acting on the image of the unit function. -/
lemma fiberMk_structureModules_eq_smul (x : X) (r : Γ(X, ⊤)) :
    fiberMk X.structureModules x r =
      X.Γevaluation x r • fiberMk X.structureModules x (oneSection X ⊤) := by
  conv_lhs => rw [← smul_oneSection ⊤ r]
  exact (fiberMk X.structureModules x).map_smulₛₗ r (oneSection X ⊤)

end UnitHom

/-! ### Pulling back the morphism attached to a global section -/

section SectionHom

variable {X Y : Scheme.{u}}

/-- **Composing multiplication by a global section with a morphism** is multiplication by the
image of that section:

```
        homOfSectionTop M m
   𝒪ₓ ──────────────────────→ M
     ╲                        │
      ╲                       │ φ
       ╲ homOfSectionTop M' (φ.app ⊤ m)
        ↘                     ↓
                              M'
```
-/
@[reassoc, simp]
lemma homOfSectionTop_comp {M M' : X.Modules} (m : Γ(M, ⊤)) (φ : M ⟶ M') :
    homOfSectionTop M m ≫ φ = homOfSectionTop M' (Hom.app φ ⊤ m) :=
  (unitHomEquivTop M').injective <|
    ((ConcreteCategory.congr_hom (Hom.comp_app (homOfSectionTop M m) φ (U := ⊤))
        (oneSection X ⊤)).trans ((ConcreteCategory.comp_apply _ _ _).trans
      (congrArg (ConcreteCategory.hom (Hom.app φ ⊤)) (app_homOfSectionTop_oneSection M m)))).trans
      (app_homOfSectionTop_oneSection M' _).symm

/-- The unit section pulls back to the unit section. -/
lemma app_pullbackUnitIso_inv_oneSection (a : X ⟶ Y) :
    Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤) =
      sectionsPullback a (unit Y.ringCatSheaf) (oneSection Y ⊤) := by
  have h1 : Hom.app (pullbackUnitIso a).hom ⊤
      (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) = oneSection X ⊤ := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app,
      ConcreteCategory.id_apply]
  have h2 : Hom.app (pullbackUnitIso a).hom ⊤
      (sectionsPullback a (unit Y.ringCatSheaf) (oneSection Y ⊤)) = oneSection X ⊤ :=
    (app_pullbackUnitIso_hom_sectionsPullback a (oneSection Y ⊤)).trans
      (map_one (ConcreteCategory.hom a.appTop))
  exact (sectionsEquivOfIso (pullbackUnitIso a) ⊤).injective (h1.trans h2.symm)

/-- **The pullback of multiplication by a global section** is multiplication by the pullback of
that section, under the identification `a^* 𝒪ᵧ ≅ 𝒪ₓ`:

```
                 (pullbackUnitIso a).inv
            𝒪ₓ ───────────────────────────→ a^* 𝒪ᵧ
             │                                 │
             │ homOfSectionTop _ (a^* m)       │ a^* (homOfSectionTop M m)
             ↓                                 ↓
          a^* M ═════════════════════════════ a^* M
```
-/
@[reassoc]
lemma map_homOfSectionTop (a : X ⟶ Y) (M : Y.Modules) (m : Γ(M, ⊤)) :
    (pullbackUnitIso a).inv ≫ (pullback a).map (homOfSectionTop M m) =
      homOfSectionTop ((pullback a).obj M) (sectionsPullback a M m) := by
  refine (unitHomEquivTop _).injective ?_
  have h1 : Hom.app ((pullbackUnitIso a).inv ≫
      (pullback a).map (homOfSectionTop M m)) ⊤ (oneSection X ⊤) =
      Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤
        (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) :=
    (ConcreteCategory.congr_hom (Hom.comp_app (pullbackUnitIso a).inv
      ((pullback a).map (homOfSectionTop M m)) (U := ⊤)) (oneSection X ⊤)).trans
      (ConcreteCategory.comp_apply _ _ _)
  have h2 : Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤
      (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) = sectionsPullback a M m :=
    (congrArg (ConcreteCategory.hom
        (Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤))
      (app_pullbackUnitIso_inv_oneSection a)).trans
      ((sectionsPullback_naturality_apply a (homOfSectionTop M m) (oneSection Y ⊤)).trans
        (congrArg (ConcreteCategory.hom (sectionsPullback a M))
          (app_homOfSectionTop_oneSection M m)))
  exact (h1.trans h2).trans (app_homOfSectionTop_oneSection _ _).symm

section Over

variable {X' W : Scheme.{u}}

/-- **The pullback over a base of multiplication by a global section** is multiplication by the
pullback of that section. This is
`AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop` with the target read through the triangle
isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackTriangle` of `u ≫ p' = p`:

```
              (pullbackUnitIso u).inv        u^* (homOfSectionTop _ m) ≫ pullbackTriangle
         𝒪ₓ ──────────────────────────→ u^* 𝒪 ─────────────────────────────────────────→ p^* F
           ╲                                                                             ↑
            ╲  homOfSectionTop _ (sectionsPullbackOver u hu F m)                        ╱
             ───────────────────────────────────────────────────────────────────────────
```
-/
@[reassoc]
lemma map_homOfSectionTop_over (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) :
    (pullbackUnitIso u).inv ≫ (pullback u).map (homOfSectionTop ((pullback p').obj F) m) ≫
        (pullbackTriangle hu).hom.app F =
      homOfSectionTop ((pullback p).obj F) (sectionsPullbackOver u hu F m) := by
  rw [← Category.assoc, map_homOfSectionTop]
  exact (homOfSectionTop_comp _ _).trans
    (congrArg (homOfSectionTop ((pullback p).obj F)) (sectionsPullbackOver_apply hu F m).symm)

/-- **Multiplication by a global section vanishes on the fibre at `u x` exactly when
multiplication by the pulled back section vanishes on the fibre at `x`.** -/
lemma fiberMap_homOfSectionTop_eq_zero_iff_over (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W}
    (hu : u ≫ p' = p) (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) (x : X)
    [IsIso (u.residueFieldMap x)] :
    fiberMap (homOfSectionTop ((pullback p').obj F) m) (u x) = 0 ↔
      fiberMap (homOfSectionTop ((pullback p).obj F) (sectionsPullbackOver u hu F m)) x = 0 := by
  refine (fiberMap_pullback_map_eq_zero_iff u x
    (homOfSectionTop ((pullback p').obj F) m)).symm.trans ?_
  refine (fiberMap_isoComp_eq_zero_iff ((pullback u).map (homOfSectionTop ((pullback p').obj F) m))
    (pullbackUnitIso u).symm ((pullbackTriangle hu).app F) x).symm.trans ?_
  exact Iff.of_eq (congrArg (fun ψ ↦ fiberMap ψ x = 0) (map_homOfSectionTop_over u hu F m))

end Over

end SectionHom

/-! ### Epimorphisms of sheaves of modules -/

section Epi

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **A morphism of sheaves of `𝒪_X`-modules is an epimorphism exactly when it is locally
surjective**, that is, when every section of the target is, near every point, the image of a
section of the source. -/
theorem epi_iff_isLocallySurjective (φ : M ⟶ N) :
    Epi φ ↔ TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf :=
  SheafOfModules.epi_iff_isLocallySurjective φ

/-- **A morphism of sheaves of `𝒪_X`-modules is an epimorphism exactly when it is surjective on
every stalk.** -/
theorem epi_iff_surjective_stalkMap (φ : M ⟶ N) :
    Epi φ ↔ ∀ x : X, Function.Surjective (φ.stalkMap x) :=
  (epi_iff_isLocallySurjective φ).trans
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.mapPresheaf)

/-- **A morphism of sheaves of `𝒪_X`-modules surjective on the sections over every affine open
subset is an epimorphism.**

Surjectivity over *all* opens would be far too strong a demand — it already fails for the
restriction `𝒪_X ⟶ g_* 𝒪_Y` to a closed subscheme — whereas the affine opens form a basis, so
surjectivity over them implies the local surjectivity that being an epimorphism means. The
converse fails in general: lifting a section over an affine `U` needs `H¹(U, ker φ)` to vanish,
which holds for a quasi-coherent kernel but not for an arbitrary one. -/
theorem epi_of_surjective_app (φ : M ⟶ N)
    (h : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (φ.app U)) : Epi φ :=
  (epi_iff_isLocallySurjective φ).mpr
    (TopCat.Presheaf.isLocallySurjective_of_isBasis X.isBasis_affineOpens _ h)

end Epi

/-! ### Morphisms out of the pushforward of a free sheaf of modules -/

section PushforwardFree

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type u} [Finite ι] {P : X.Modules}

/-- **The pushforward of a free sheaf of modules is a coproduct of copies of `g_* 𝒪_Y`.**
`Modules.pushforward g` is additive, hence preserves finite coproducts. -/
noncomputable def isColimitMapFreeModulesCofan :
    IsColimit ((pushforward g).mapCocone (Y.freeModulesCofan ι)) :=
  isColimitOfPreserves (pushforward g) (Y.isColimitFreeModulesCofan ι)

/-- **A morphism out of the pushforward of a free sheaf of modules is the same thing as a
family of morphisms out of the pushforward of the structure sheaf.**

A morphism out of `g_* M` cannot be written down on sections, because over a non-affine open
`U` the sections `Γ(𝒪_Y, g ⁻¹ᵁ U)` are not built from `Γ(𝒪_X, U)`. But `𝒪_Y^ι` is the coproduct
of `ι` copies of `𝒪_Y` and `Modules.pushforward g` is additive, hence preserves finite
coproducts, so `g_* (𝒪_Y^ι)` is the coproduct of `ι` copies of `g_* 𝒪_Y` and a morphism out of
it is a family of morphisms out of `g_* 𝒪_Y`.

```
  g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^ι)
        ╲                         │
   β j   ╲                        │ pushforwardFreeDesc g β
          ╲                       ▼
           ╲────────────────────▶ P
```
-/
noncomputable def pushforwardFreeDesc (β : ι → ((pushforward g).obj Y.structureModules ⟶ P)) :
    (pushforward g).obj (Y.freeModules ι) ⟶ P :=
  (isColimitMapFreeModulesCofan g).desc (Cocone.mk P (Discrete.natTrans fun j ↦ β j.as))

/-- **The `j`-th component of the descended morphism is `β j`**: the triangle

```
  g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^ι)
        ╲                         │
   β j   ╲                        │ pushforwardFreeDesc g β
          ╲                       ▼
           ╲────────────────────▶ P
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_ιFree_comp_pushforwardFreeDesc
    (β : ι → ((pushforward g).obj Y.structureModules ⟶ P)) (j : ι) :
    (pushforward g).map (SheafOfModules.ιFree j) ≫ pushforwardFreeDesc g β = β j :=
  (isColimitMapFreeModulesCofan g).fac _ ⟨j⟩

/-- **Two morphisms out of the pushforward of a free sheaf of modules agreeing on every
summand are equal.** -/
lemma pushforwardFree_hom_ext {χ χ' : (pushforward g).obj (Y.freeModules ι) ⟶ P}
    (h : ∀ j : ι, (pushforward g).map (SheafOfModules.ιFree j) ≫ χ =
      (pushforward g).map (SheafOfModules.ιFree j) ≫ χ') : χ = χ' :=
  (isColimitMapFreeModulesCofan g).hom_ext fun j ↦ h j.as

/-- **The descended morphism is the only one restricting to the given family on the
summands.** -/
lemma eq_pushforwardFreeDesc (β : ι → ((pushforward g).obj Y.structureModules ⟶ P))
    (χ : (pushforward g).obj (Y.freeModules ι) ⟶ P)
    (hχ : ∀ j : ι, (pushforward g).map (SheafOfModules.ιFree j) ≫ χ = β j) :
    χ = pushforwardFreeDesc g β :=
  pushforwardFree_hom_ext g fun j ↦ by rw [hχ, map_ιFree_comp_pushforwardFreeDesc]

/-- **Every germ of the pushforward of a free sheaf of modules is the sum of its components**:
the identity

```
  ∑ⱼ ( g_* (𝒪_Y^κ) ──g_* (πFree j)──▶ g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^κ) )  =  𝟙
```

evaluated on a germ at `x`. -/
lemma sum_stalkMap_map_ιFree {κ : Type u} [Fintype κ] (x : X)
    (w : ((pushforward g).obj (Y.freeModules κ)).presheaf.stalk x) :
    ∑ j : κ, Hom.stalkMap ((pushforward g).map (SheafOfModules.ιFree j)) x
      (Hom.stalkMap ((pushforward g).map (SheafOfModules.πFree j)) x w) = w := by
  -- the pushforward is additive, so it takes the biproduct decomposition of `𝒪_Y^κ` to one of
  -- `g_* (𝒪_Y^κ)`
  have h : ∑ j : κ, (pushforward g).map (SheafOfModules.πFree (R := Y.ringCatSheaf) j) ≫
      (pushforward g).map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) =
      𝟙 ((pushforward g).obj (Y.freeModules κ)) := by
    rw [← CategoryTheory.Functor.map_id (pushforward g) (Y.freeModules κ),
      ← SheafOfModules.sum_πFree_comp_ιFree (R := Y.ringCatSheaf) κ, Functor.map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ ((pushforward g).map_comp _ _).symm
  simpa only [Hom.stalkMap_sum, Hom.stalkMap_comp_apply, Hom.stalkMap_id,
    ConcreteCategory.id_apply] using congrArg (fun χ : ((pushforward g).obj (Y.freeModules κ) ⟶
      (pushforward g).obj (Y.freeModules κ)) ↦ Hom.stalkMap χ x w) h

end PushforwardFree


end Scheme.Modules

/-! ### The comparison morphism `𝒪_X ⟶ g_* 𝒪_Y` -/

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **The comparison morphism `𝒪_X ⟶ g_* 𝒪_Y`** of sheaves of `𝒪_X`-modules attached to a
morphism of schemes `g : Y ⟶ X`: the pullback of functions along `g`, read as a morphism of
`𝒪_X`-modules. -/
noncomputable def toPushforwardStructure :
    X.structureModules ⟶ (Modules.pushforward g).obj Y.structureModules :=
  SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom

@[simp]
lemma toPushforwardStructure_app (U : X.Opens) (s : Γ(X.structureModules, U)) :
    g.toPushforwardStructure.app U s = g.app U s :=
  rfl

variable {P : X.Modules} (ψ : X.structureModules ⟶ P)

/-- **A morphism out of `𝒪_X` kills the kernel of `𝒪_X ⟶ g_* 𝒪_Y` exactly when it kills every
function vanishing on `Y`**: the sections of that kernel over an open subset `U` are precisely
the sections of `𝒪_X` over `U` killed by `g.app U`.

```
  ker (𝒪_X ⟶ g_* 𝒪_Y) --- kernel.ι ---> 𝒪_X --- ψ ---> P
```
-/
lemma kernelι_toPushforwardStructure_comp_eq_zero_iff :
    kernel.ι g.toPushforwardStructure ≫ ψ = 0 ↔
      ∀ (U : X.Opens) (s : Γ(X.structureModules, U)), g.app U s = 0 → ψ.app U s = 0 := by
  have key (U : X.Opens) : Set.range ((kernel.ι g.toPushforwardStructure).app U) =
      { s : Γ(X.structureModules, U) | g.app U s = 0 } :=
    Modules.range_map_kernelι U g.toPushforwardStructure
  constructor
  · intro h U s hs
    obtain ⟨z, rfl⟩ := (key U).ge hs
    have hz : (kernel.ι g.toPushforwardStructure ≫ ψ).app U z = 0 := by rw [h]; simp
    simpa using hz
  · intro hψ
    ext U z
    exact hψ U _ ((key U).le ⟨z, rfl⟩)

variable [Epi g.toPushforwardStructure]

/-- **The descent of a morphism through `𝒪_X ⟶ g_* 𝒪_Y`**: a morphism `ψ : 𝒪_X ⟶ P` killing the
kernel of the comparison morphism factors through it.

```
            ψ
  𝒪_X ---------------> P
   |                  ↗
   |                 /
   |   descPushforwardStructure ψ hψ
   v                /
  g_* 𝒪_Y ---------
```
-/
noncomputable def descPushforwardStructure
    (hψ : kernel.ι g.toPushforwardStructure ≫ ψ = 0) :
    (Modules.pushforward g).obj Y.structureModules ⟶ P :=
  -- an epimorphism in an abelian category is the cokernel of its kernel
  Abelian.epiDesc g.toPushforwardStructure ψ hψ

/-- The defining property of `AlgebraicGeometry.Scheme.Hom.descPushforwardStructure`: the upper
triangle
```
            ψ
  𝒪_X ---------------> P
   |                  ↗
   v                 /
  g_* 𝒪_Y ---------
```
commutes. -/
@[reassoc (attr := simp)]
lemma toPushforwardStructure_descPushforwardStructure
    (hψ : kernel.ι g.toPushforwardStructure ≫ ψ = 0) :
    g.toPushforwardStructure ≫ g.descPushforwardStructure ψ hψ = ψ :=
  Abelian.comp_epiDesc _ _ _

/-- **The descent through `𝒪_X ⟶ g_* 𝒪_Y` is unique**: any `χ : g_* 𝒪_Y ⟶ P` making
```
            ψ
  𝒪_X ---------------> P
   |                  ↗
   v         χ       /
  g_* 𝒪_Y ---------
```
commute is `AlgebraicGeometry.Scheme.Hom.descPushforwardStructure`. -/
lemma eq_descPushforwardStructure (hψ : kernel.ι g.toPushforwardStructure ≫ ψ = 0)
    (χ : (Modules.pushforward g).obj Y.structureModules ⟶ P)
    (hχ : g.toPushforwardStructure ≫ χ = ψ) :
    χ = g.descPushforwardStructure ψ hψ := by
  rw [← cancel_epi g.toPushforwardStructure, hχ,
    toPushforwardStructure_descPushforwardStructure]

/-- **The descent computes on the functions pulled back from `X`.** Together with
`AlgebraicGeometry.Scheme.Hom.eq_descPushforwardStructure` this is what pins the descent down
on sections: over an open on which `g.app` is surjective it determines it completely. -/
@[simp]
lemma app_descPushforwardStructure_app (hψ : kernel.ι g.toPushforwardStructure ≫ ψ = 0)
    (U : X.Opens) (s : Γ(X.structureModules, U)) :
    (g.descPushforwardStructure ψ hψ).app U (g.toPushforwardStructure.app U s) = ψ.app U s := by
  rw [← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app,
    toPushforwardStructure_descPushforwardStructure]

/-- **`g_* 𝒪_Y` is the quotient of `𝒪_X` by the ideal sheaf of `Y`**: the sequence
```
0 ⟶ ker (𝒪_X ⟶ g_* 𝒪_Y) ⟶ 𝒪_X ⟶ g_* 𝒪_Y ⟶ 0
```
is a short exact sequence of sheaves of `𝒪_X`-modules. -/
lemma shortExact_kernelSequence_toPushforwardStructure :
    (ShortComplex.kernelSequence g.toPushforwardStructure).ShortExact where
  exact := ShortComplex.kernelSequence_exact _
  mono_f := inferInstance
  epi_g := ‹_›

end Scheme.Hom

end AlgebraicGeometry
