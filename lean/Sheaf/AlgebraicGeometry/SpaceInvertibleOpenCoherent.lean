/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeFiniteFreeLocusBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import WeilConjectures.FieldTheory.CommonExtensionFields

/-! # Invertible modules are open in the coherent stack of an algebraic space

Source: Stacks Project, quot.tex, Tag 0D03, lemma-picard-stack-open-in-coh
(blueprint: lem-sfb-space-invertible-open-coherent).

The line predicate uses the existing small-etale-site definition. The total category
and its arrows are the full subcategory of the existing coherent-family category.
The theorem also retains eligibility of every line module and the universal open locus.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The line predicate on coherent families: local isomorphism to the structure module
on the small etale ringed site, with the existing tensor-pullback arrows.
Source: Stacks, Tag 0D03 (blueprint: lem-sfb-space-invertible-open-coherent). -/
def CoherentModuli.isLine (f : X ⟶ schemeSpace (Over.mk (𝟙 S)))
    (F : CoherentModuli f) : Prop :=
  (properQuotFibre f F.base).IsLineModule F.module

/-- The full total category of line families, over the original category of S-schemes.
Eligibility of all line modules is asserted by `invertible_open_coherent`.
Source: Stacks, Tag 0D03 (blueprint: lem-sfb-space-invertible-open-coherent). -/
def lineModuliCategory (f : X ⟶ schemeSpace (Over.mk (𝟙 S))) :
    BasedCategory (Over S) :=
  fullModuliSubcategory (CoherentModuli.category f) (CoherentModuli.isLine f)

/-- Forgetting invertibility is the actual full inclusion and keeps every arrow.
Source: Stacks, Tag 0D03 (blueprint: lem-sfb-space-invertible-open-coherent). -/
def lineModuliInclusion (f : X ⟶ schemeSpace (Over.mk (𝟙 S))) :
    BasedFunctor (lineModuliCategory f) (CoherentModuli.category f) :=
  fullModuliInclusion (CoherentModuli.category f) (CoherentModuli.isLine f)

/-- Invertible modules form a full open substack. Every raw line module is an object
of the coherent stack with exactly that base and module; heterogeneous equality only
transports the module along the displayed equality of bases. The final equivalence
holds for every test map, without any flatness or finiteness assumption on that map.
The `open_pullback` field of the specified open substack gives representation of each
2-fibre product by an open immersion; the universal criterion identifies that open
with the one displayed here.
Source: Stacks, Tag 0D03 (blueprint: lem-sfb-space-invertible-open-coherent).

Proof:
1. By lem-sfb-space-flat-proper-fp-locality, every X_T -> T is flat, proper and
   finitely presented. A line module is locally the structure module, hence is
   quasi-coherent and finitely presented. It is relatively flat because X_T -> T is
   flat. Its proper-support presentation is the identity closed immersion with the
   line module itself, which is of finite type. This supplies the coherent object
   on the identical base with the identical module. Tensor pullback carries a local
   generator e to 1 tensor e, so preserves lines. The forgetful functor is full and
   faithful since its arrows are the same tensor-pullback isomorphisms, using
   def-trf-space-etale-module-functors.
2. Apply lem-sfb-space-relative-finite-free-locus-base-change to F. Its finite locally
   free locus W is open and commutes with every base change. Inside W the rank-one
   locus V is open: local finite free trivializations have constant rank, determined
   by geometric fibres, and their etale chart images are open by
   lem-a1-space-affine-etale-cover. Pulling back a trivialization preserves its rank;
   geometric fibre dimensions are unchanged under field extensions. Thus the closed
   complement C of V pulls back to the complement of the rank-one locus.
3. Properness makes p(C) closed; take U_F = T minus p(C). For a test map v, its
   pullback of C is empty exactly when its image avoids p(C). The reverse implication
   uses lem-weil-common-extension-fields to lift compatible points to the sheaf fibre
   product, as in lem-trf-space-fibre-products-etale-covers. Consequently v-pullback F
   is a line precisely when v factors through U_F. Open immersions are monomorphisms,
   so the factorization is unique. Empty spaces and empty fibres are included.
4. An object in the 2-fibre product is a line module together with an isomorphism to
   the pulled-back F. It exists exactly on U_F. Between any two such pairs the unique
   compatible arrow is the composite of their comparison isomorphisms, so every
   nonempty fibre is contractible. Sending the pair to its unique factorization
   through U_F, with inverse given by pulled-back F and its identity isomorphism,
   commutes with pullback. This is the representing equivalence over T and supplies
   `OpenModuliSubstack` as in def-sfb-open-moduli-substack. -/
theorem invertible_open_coherent (f : X ⟶ schemeSpace (Over.mk (𝟙 S)))
    (hflat : MapIsFlat f) (hproper : MapIsProper f) (hfp : ProperQuotFinitePresentation f) :
    (∀ (T : ProperQuotTest (schemeSpace (Over.mk (𝟙 S))))
        (L : (properQuotFibre f T).Modules),
      (properQuotFibre f T).IsLineModule L →
        ∃ F : CoherentModuli f, F.base = T ∧ HEq F.module L) ∧
    (lineModuliInclusion f).toFunctor.Full ∧
    (lineModuliInclusion f).toFunctor.Faithful ∧
    ∃ U : OpenModuliSubstack (CoherentModuli.category f),
      U.property = CoherentModuli.isLine f ∧
      ∀ F : CoherentModuli f, ∃ W : F.base.left.left.Opens,
        ∀ (T' : ProperQuotTest (schemeSpace (Over.mk (𝟙 S)))) (v : T' ⟶ F.base),
          (properQuotFibre f T').IsLineModule
              ((moduleTensorPullback (properQuotFibreMap f v)).obj F.module) ↔
            ∃ a : T'.left.left ⟶ W.toScheme, a ≫ W.ι = v.left.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
