/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import Mathlib.Topology.Constructible

/-!
# Constructible finite-coefficient sheaves on oriented products

Source: Lu--Zheng, Duality and nearby cycles over general bases, arXiv:1712.10216v7,
definition following Theorem 4.27 (printed p. 38), with the general oriented-product
form after Corollary 1.26 (printed p. 12); ILO XI §§1.1--1.7
(blueprint: def-trf-oriented-constructible-sheaf).

The site and coefficient universes follow `OrientedNearbyCycles`. Restriction uses
sheafified left Kan extension along the actual base-change functor on triples. The
fixed-ring/constant-ring equivalence only changes the presentation of module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedConstructibleSheaf

/-- The left oriented product's triple category, on the recorded transported étale sites.
Source: ILO XI §1.1 (blueprint: def-trf-oriented-constructible-sheaf). -/
abbrev ProductSite {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  OrientedProduct.largeTriples (etaleBaseChange.{u, v} a) (etaleBaseChange.{u, v} b)

/-- The three covering types of the left oriented product, with their generated topology.
Source: ILO XI §1.1(ii) (blueprint: def-trf-oriented-constructible-sheaf). -/
def productTopology {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    GrothendieckTopology (ProductSite.{u, v} a b) :=
  OrientedProduct.largeTopology (etaleTopology X).toPretopology
    (etaleTopology Y).toPretopology (etaleBaseChange a) (etaleBaseChange b)

/-- Modules over the constant ring sheaf on this very oriented product.
`Coeff` is the recorded canonical universe lift of the coefficient ring.
Source: Lu--Zheng, definition after Theorem 4.27; Stacks 03CY
(blueprint: def-trf-oriented-constructible-sheaf). -/
abbrev Modules {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (Λ : Type v) [CommRing Λ] :=
  ringedSiteModules.{max (u + 1) v}
    ((constantSheaf (productTopology.{u, v} a b) RingCat.{max (u + 1) v}).obj
      (RingCat.of (Coeff.{u, v} Λ)))

/-- Pull back both outer components of a triple, leaving its middle component fixed.
The two structural arrows use the canonical fibre-product composition identifications.
This is the site functor for the oriented-product map induced by the two scheme maps:
its projection maps are base change by `i` and `j`, and it retains the orientation.
Source: ILO XI §§1.1, 1.6, 1.9; Lu--Zheng, definition after Theorem 4.27
(blueprint: def-trf-oriented-constructible-sheaf). -/
def stratumBaseChange {X' Y' X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (i : X' ⟶ X) (j : Y' ⟶ Y) :
    ProductSite.{u, v} a b ⥤ ProductSite.{u, v} (i ≫ a) (j ≫ b) :=
  Comma.map
    (F₁ := (etaleBaseChange.{u, v} i).prod (etaleBaseChange.{u, v} j))
    (F₂ := 𝟭 (EtaleSite.{u, v} S))
    (F := (etaleBaseChange.{u, v} i).prod (etaleBaseChange.{u, v} j))
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    (NatTrans.prod' (etaleBaseChangeComp.{u, v} i a).inv
      (etaleBaseChangeComp.{u, v} j b).inv)

/-- The inverse image along the induced oriented-product map on constant-ring modules.
First use the recorded equivalence with fixed-ring module-valued sheaves, then the usual
sheafified left Kan extension along the concrete triple-site base change, and finally
return through the same equivalence on the target site. This is the canonical site
inverse image, rather than an arbitrary functor or a choice of a map of topoi.
The equivalence's forward functor is prescribed scalar restriction, so its inverse is
uniquely determined up to the natural isomorphism used by local constancy.
Source: ILO XI §§1.6--1.9; Stacks 03CY; Lu--Zheng, definition after Theorem 4.27
(blueprint: def-trf-oriented-constructible-sheaf). -/
def stratumRestriction {X' Y' X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (i : X' ⟶ X) (j : Y' ⟶ Y) (Λ : Type v) [CommRing Λ] :
    Modules a b Λ ⥤ Modules (i ≫ a) (j ≫ b) Λ :=
  constantRingModuleRestriction (productTopology a b) (Coeff Λ) ⋙
    sheafToPresheaf (productTopology a b) (ModuleCat.{max (u + 1) v} (Coeff Λ)) ⋙
    (stratumBaseChange.{u, v} a b i j).op.lan ⋙
    presheafToSheaf (productTopology (i ≫ a) (j ≫ b))
      (ModuleCat.{max (u + 1) v} (Coeff Λ)) ⋙
    (constant_ring_module_sheaves (productTopology (i ≫ a) (j ≫ b))
      (Coeff Λ)).1.choose.inverse

/-- Constructibility on the left oriented product: finite constructible locally closed
stratifications of both schemes make all oriented stratum restrictions locally constant
with finite module values. The existing local-constancy predicate asks on every site
object for a covering sieve with constant finite-type module models on its slices.
For a finite ring, finite type is equivalent to being finite as a set. Covering site
objects refine a cover of the final topos object, so this is exactly the stated slice
condition, including for empty topoi. For `Y = S`, `b = 𝟙 S`, the canonical identity
base-change comparison identifies this with constructibility on the recorded vanishing
topos `OrientedNearbyCycles.VanishingTopos a`.
Source: Lu--Zheng, definition following Theorem 4.27, printed p. 38
(blueprint: def-trf-oriented-constructible-sheaf). -/
def IsConstructible {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (Λ : Type v) [CommRing Λ] [Finite Λ] (F : Modules a b Λ) : Prop :=
  ∃ (sX : X.FiniteLocallyClosedStratification) (sY : Y.FiniteLocallyClosedStratification),
    (∀ i : Fin sX.n, Topology.IsConstructible (sX.stratum i)) ∧
    (∀ j : Fin sY.n, Topology.IsConstructible (sY.stratum j)) ∧
    ∀ (i : Fin sX.n) (j : Fin sY.n),
      SheafOfModules.IsFiniteTypeLocallyConstant
        (productTopology (sX.immersion i ≫ a) (sY.immersion j ≫ b)) (Coeff Λ)
        ((stratumRestriction a b (sX.immersion i) (sY.immersion j) Λ).obj F)

end AlgebraicGeometry.OrientedConstructibleSheaf
