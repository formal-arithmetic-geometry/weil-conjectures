/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.GeometricPointFieldExtension
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-! # The strict-local base-change mate on the closed stalk

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

/-- On the closed stalk of any chosen strict-henselization model, homology of the
base-change mate is invertible. This concerns only the single lower cartesian square;
it does not involve a cube or any further inverse image.
Source: Stacks Project, Tag 03Q9 (theorem-higher-direct-images), restriction of injective
section complexes, and Tag 03QO (lemma-cohomology-strictly-henselian).
(blueprint: lem-weil-pbc-strict-local-base-change-closed-stalk).

Proof:
1. Apply `isIso_strictHenselization_baseChange_globalHomology` to f, s, G[0], and q.
The canonical derived mate there equals `derivedBaseChangeMapPlus`: compare their
components on bounded-below complexes using `Adjunction.derivedPlus_mateEquiv_app_fac`
and `pullbackSquareComparison_hom_app_factorsh`, then use
`derivedBaseChangeMapPlus_ext`. Thus global sections of homology of the canonical
strict-local base-change map are invertible, without a torsion assumption.
2. Put j = strictHenselizationStructuralMap s, P = pullback f j, p = pullback.fst f j,
and v = pullback.snd f j. The map b : X₀ → P is the pullback lift of p₀ and f₀ ≫ eA.hom.
It satisfies b ≫ p = p₀ and b ≫ v = f₀ ≫ eA.hom. Pullback cancellation gives the
cartesian square (b, f₀, v, eA.hom); because eA.hom is invertible, b is invertible too.
Its derived base-change map is invertible: inverse image along an isomorphism is an
exact equivalence preserving injectives, so `derivedBaseChangeMapPlus_fac_app` on an
injective representative expresses this map as a composite of isomorphisms.
3. The horizontal pasting formula writes the outer mate at K = G[0] as
C(eA.hom,j).hom followed by D(eA.hom) of the canonical mate, the mate of the square
in step 2 at D(p)K, and R(f₀) of C(b,p).inv. Here C is `upperStarCompDerivedPlus`;
the equation b ≫ p = p₀ identifies the outer square with sq₀. Global sections after
inverse image along eA.hom are naturally isomorphic to global sections before it:
whisker the invertible adjunction unit with global sections, and apply
`lowerStarCompGlobalSectionsIso`. Homology commutes with exact inverse image by
`mapDerivedCategoryPlusHomologyFunctorIso`. Consequently the middle factor remains
invertible after global sections of homology, by step 1. All other factors are images
of isomorphisms under functors. Thus global sections of homology of the sq₀ mate are
invertible.
4. The point t = a followed by the residue closed-point map lies over the closed point
of Spec A (`IsLocalRing.PrimeSpectrum.comap_residue`). Enlarge k to AlgebraicClosure k.
`isIso_pointSmallEtalePrecomp_sheafFiber` and its naturality identify stalk maps before
and after this enlargement. Apply `strictlyHenselianSections_geometricStalk_isIso` to
the enlarged point and both homology sheaves. Its naturality states that the source
global germ followed by the stalk map is the section map followed by the target global
germ. The section map is invertible by step 3, using `ΓNatIsoSheafSections`. Both germs
are invertible by 03QO. Cancel the source germ, then the field-extension comparison,
to obtain invertibility of the displayed stalk map.
The argument applies to q = 0, zero sheaves, and empty total spaces; no relation of the
chosen point field k to Ω is required. -/
theorem isIso_strictHenselization_baseChange_closedStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    {k : Type u} [Field k] [IsSepClosed k]
    (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso ((pointSmallEtale
      (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by sorry

end AlgebraicGeometry.Etale
