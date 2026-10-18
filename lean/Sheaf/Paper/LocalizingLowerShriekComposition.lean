/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Compactification.Dense
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.DerivedDirectImageOpenCoherence
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Paper.ProEtaleProperOpenInterchange
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.CompactificationRefinementLocalizing
import Sheaf.Compactification.CommonDenseRefinement
import Sheaf.Compactification.DenseRefinementMorphisms
import Sheaf.Paper.InterchangeProperPasting

/-!
# Composition of rational lower shriek on localizing constructible categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
clause (1), rational cases, and its proof, paragraphs "The composition isomorphism" and
"Canonicity and associativity"
(blueprint: lem-sfb-localizing-lower-shriek-composition).

The statement is recorded here as the canonical project interface for this composition.

The coefficients are exactly a finite subextension or the finite-subextension-valued
condensed algebraic closure. The functors are the existing restrictions of `Rp_* D(j_!)`.
Compatibility is expressed using the canonical refinement components of the recorded
compactification cocycle. Every triple of compactifications is allowed, including
nondense ones. Common dense refinements and the cocycle law identify the final equation
with compatibility with all compactification comparison isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- There is a natural composition isomorphism on the ordinary localizing closures for
rational condensed coefficients, compatible with change of compactification. The witnesses
`hf`, `hg`, `hgf` only certify preservation by the actual ambient compactification functors;
`localizingLowerShriek` uses those same objects and maps. The equation is an equality in the
ambient derived category, hence also in its full localizing subcategory. Its refinement
maps are exactly those used to normalize the comparisons in
`compactification_coherence_cocycle`, rather than arbitrary isomorphisms of their endpoints.

Source: blueprint sk-thm-sf-comp-composition, clause (1), rational cases, and its proof
(blueprint: lem-sfb-localizing-lower-shriek-composition).

Proof, following all seven steps of the DAG:
1. Finite type and separatedness give qcqs. Choose dense compactifications f = pj,
   g = qi, and ip = ru by sk-thm-nagata-compactification. Proper maps compose by
   lem-weil-pbc-proper-fp-permanence; quasi-compact opens compose. Thus (uj,qr)
   compactifies gf. The composite of the two injections of structure sheaves proves
   schematic density of uj (sk-def-nagata-sketch-data).
2. The exact open module adjunction (sk-def-sfb-module-lower-shriek), cartesian
   coefficients (sk-prop-sfb-cartesian-coefficients), exact derived factorization
   (lem-weil-pbc-exact-functor-derived-factorization), termwise homotopy adjunction
   (lem-weil-pbc-termwise-adjunction-homotopy) and localized adjunction
   (lem-sfb-adjunction-localization) give D(j!) left adjoint to D(j*). Transposing
   units gives the composition of open extensions, normalized by identity on the open.
   Use lem-weil-pbc-ringed-topoi-derived-pushforward-composition and
   lem-sfb-derived-direct-image-open-coherence for direct-image reassociation and
   open restriction, with their coefficient actions (sk-def-sfb-module-pushforward-pullback).
3. det-proper-image-localizing-open puts j!K in the localizing closure. Apply
   det-sf-comp-composition-interchange to p,i,(u,r): the inverse image of Y is the
   original proper source, and the unique map i! Rp_* A to Rr_* u! A restricting to
   identity is an isomorphism there. Its uniqueness gives naturality. Apply Rq_* at
   A = j!K and Step 2 to obtain the composition isomorphism. By
   det-sf-comp-coherence-single both endpoints lie in the target closure; fullness
   restricts the isomorphism to that closure.
4. For a dense refinement of the auxiliary compactification, push its normalized
   open refinement map (det-sf-comp-coherence-refinement) by Rr_*. Both resulting
   interchange maps restrict to identity, so uniqueness in interchange equates them.
   At j!K the composite-open refinement is the same map by its identity normalization.
   For any two auxiliary choices use det-nagata-refinement-common-dense and the
   det-sf-comp-coherence-cocycle comparison, with properness from
   det-nagata-refinement-morphisms. This removes the auxiliary choice.
5. For a dense refinement of f, compactify its composite with u. Apply
   lem-sfb-interchange-proper-pasting to identify the two interchange composites.
   Open preservation puts the input in the required closure, and single-compactification
   preservation puts its proper image there. Naturality of interchange and uniqueness
   of the normalized refinement map identify the remaining composite. Push by Rq_* Rr_*
   to obtain the refinement square for f; Step 4 removes the auxiliary choice.
6. For a dense refinement t of g, compactify i'p = r'u' and use r = tr' for the old
   auxiliary model. The two composite compactifications of gf are literally the same.
   The old interchange and the new interchange after the normalized refinement map
   have the same identity restriction on Y. Uniqueness in interchange equates them.
   Apply Rq_* at j!K. This is the refinement square for g, again independent of the
   special auxiliary choice by Step 4.
7. For arbitrary cf,cg,cgf choose dense refinements and conjugate the dense composition
   isomorphism by the comparisons of det-sf-comp-coherence-cocycle. Common dense
   refinements, Steps 4--6 and cancellation show independence of all dense choices.
   Changing any compactification composes only its prescribed comparison, by the
   cocycle law. In particular this gives the displayed simultaneous refinement square.
   Conversely that square at a common dense refinement of two triples, followed by
   cancellation of the three invertible refinement maps, gives compatibility with
   the prescribed comparisons between the triples, including nondense ones. -/
theorem exists_localizingLowerShriekComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ (hf : ∀ (c : Compactification.BoundaryCompactification f) K,
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hg : ∀ (c : Compactification.BoundaryCompactification g) K,
          localizingClosureProEtale Λ Y K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hgf : ∀ (c : Compactification.BoundaryCompactification (f ≫ g)) K,
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
      ∃ α : ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g)),
          localizingLowerShriek Λ cf.obj.obj (hf cf) ⋙
              localizingLowerShriek Λ cg.obj.obj (hg cg) ≅
            localizingLowerShriek Λ cgf.obj.obj (hgf cgf),
        ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g))
          (df : Compactification.DenseBoundaryCompactification f)
          (dg : Compactification.DenseBoundaryCompactification g)
          (dgf : Compactification.DenseBoundaryCompactification (f ≫ g))
          (rf : df.obj ⟶ cf) (rg : dg.obj ⟶ cg) (rgf : dgf.obj ⟶ cgf)
          (K : (localizingClosureProEtale Λ X).FullSubcategory),
          (rightDerivedLowerShriekOfCompactification Λ cg.obj.obj).map
              (compactificationRefinementComponent Λ rf K.obj) ≫
            compactificationRefinementComponent Λ rg
              ((rightDerivedLowerShriekOfCompactification Λ df.obj.obj.obj).obj K.obj) ≫
            ((α df.obj dg.obj dgf.obj).hom.app K).hom =
          ((α cf cg cgf).hom.app K).hom ≫
            compactificationRefinementComponent Λ rgf K.obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
