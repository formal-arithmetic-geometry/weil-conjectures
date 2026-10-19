/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
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
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Paper.ProEtaleProperOpenInterchange
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.CompactificationRefinementLocalizing
import Sheaf.Compactification.CommonDenseRefinement
import Sheaf.Compactification.DenseRefinementMorphisms
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Composition of finite and integral lower shriek on localizing constructible categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
clause (1), finite and integral cases, and its proof, paragraphs "The composition isomorphism" and
"Canonicity and associativity"
(blueprint: lem-sfb-nonrational-localizing-lower-shriek-composition).

The coefficients are exactly finite torsion rings, ℤ_ℓ, and valuation rings of finite
subextensions of ℚ_ℓ, with the condensed topologies specified in the statement.
The functors are the existing restrictions of `Rp_* D(j_!)`.
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
finite and integral condensed coefficients, compatible with change of
compactification. The witnesses
`hf`, `hg`, `hgf` only certify preservation by the actual ambient compactification functors;
`localizingLowerShriek` uses those same objects and maps. The equation is an equality in the
ambient derived category, hence also in its full localizing subcategory. Its refinement
maps are exactly those used to normalize the comparisons in
`compactification_coherence_cocycle`, rather than arbitrary isomorphisms of their endpoints.

Source: blueprint sk-thm-sf-comp-composition, clause (1), finite and integral cases, and its proof
(blueprint: lem-sfb-nonrational-localizing-lower-shriek-composition).

Proof, following the nine steps of the DAG:
1. Finite type and separatedness give qcqs. Choose dense compactifications f = pj,
   g = qi by sk-thm-nagata-compactification; ip is separated of finite type by
   lem-weil-pbc-proper-fp-permanence, so Nagata gives a dense ip = ru. Then (uj, qr)
   compactifies gf: qr is proper, uj is a quasi-compact open, and uj is scheme-theoretically
   dense because the injections O_W → u_* O and O → j_* O compose to an injection
   (sk-def-nagata-sketch-data, sk-def-sfb-dc-setting).
2. Open composition. The exact module adjunction a_! ⊣ a^* (sk-def-sfb-module-lower-shriek,
   sk-prop-sfb-cartesian-coefficients) passes to complexes
   (lem-weil-pbc-exact-functor-derived-factorization,
   lem-weil-pbc-termwise-adjunction-homotopy) and descends to D(a_!) ⊣ D(a^*) on the
   unbounded categories (lem-weil-pbc-localization-universal-property (2),
   sk-def-sfb-derived-categories). As a^* b^* ≅ (ba)^* (sk-def-sfb-module-pushforward-pullback),
   b_! a_! ≅ (ba)_! by transposing units; it restricts to the identity on the source open.
3. Direct-image composition. Use lem-weil-pbc-ringed-topoi-derived-pushforward-composition
   for the morphisms of ringed sites of def-weil-proetale-inverse-image with module direct
   image def-sfb-module-lower-star. Exact inverse images (sk-prop-sfb-cartesian-coefficients)
   make direct images preserve K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective),
   so one K-injective I computes all iterates and the comparison is the underived
   def-sfb-module-lower-star-comp; the reassociations agree sectionwise, hence as natural
   transformations (lem-weil-pbc-localization-universal-property (3)).
4. Open restriction. Restriction to an open V is localization
   (lem-weil-proetale-weakly-etale-localization (1),
   def-sfb-finite-extension-by-zero-adjunction); lem-weil-pbc-localize-ringed-site-morphism
   gives the sectionwise identity of def-sfb-finite-lower-star with the action of
   def-sfb-module-lower-star. With lem-pur-kinjective-restrict-localized and
   lem-weil-pbc-right-adjoint-preserves-kinjective this gives D(V^*) Ra_* ≅ R(a_V)_* D(U^*)
   on the unbounded categories, compatibly with Step 3 and further restriction.
5. For K in T_X, det-proper-image-localizing-open gives j_! K in T_{X̄}. Apply
   det-sf-comp-composition-interchange to p, i, (u, r): r⁻¹(Y) = X̄, r restricts to p, and
   there is a unique I_A : i_! Rp_* A → Rr_* u_! A restricting to the identity on Y, an
   isomorphism for A in T_{X̄}, natural by uniqueness. Put α(K) = Rq_*(I_{j_! K}) followed
   by the comparisons of Steps 2--4, Rq_* Rr_* u_! j_! ≅ R(qr)_* (uj)_!. Its endpoints lie in
   T_Z by det-sf-comp-coherence-single, and fullness types α on the localizing closures.
6. Auxiliary choice. For a dense refinement s of (u, r) (proper by
   det-nagata-refinement-morphisms), Rr_*(e_s) ∘ I_A and the interchange map for (u', rs) both
   restrict to the identity on Y, where e_s is the normalized map of
   det-sf-comp-coherence-refinement; uniqueness in det-sf-comp-composition-interchange equates
   them. At A = j_! K, e_s is the refinement map of uj by its identity normalization. Common
   dense refinements (det-nagata-refinement-common-dense) and the cocycle of
   det-sf-comp-coherence-cocycle make α independent of the auxiliary choice.
7. Refinement of f. For a dense refinement h of (j, p), compactify uh densely as (v, s)
   (lem-weil-pbc-proper-fp-permanence, sk-thm-nagata-compactification). Interchange for h, u
   gives J_A : u_! Rh_* A ≅ Rs_* v_! A with s restricting to h. Then Rr_* J_A ∘ I_{Rh_* A} = I'_A,
   as both restrict to the identity on Y. Rh_* preserves the localizing closures
   (det-sf-comp-coherence-single) and j'_! K lies in T_{X̄'} (det-proper-image-localizing-open);
   naturality of I and det-sf-comp-coherence-refinement (1) identify J ∘ u_!(e_h) with e_s.
   Pushing by Rq_* Rr_* gives the refinement square for f.
8. Refinement of g. For a dense refinement t of (i, q), compactify i'p densely as (u', r') and
   use (u', tr') as auxiliary model for ip; both composite compactifications of gf are
   (u'j, qtr'). The maps Rt_*(I'_A) ∘ e_t and I_A both restrict to the identity on Y, so
   uniqueness in det-sf-comp-composition-interchange equates them. Apply Rq_* at A = j_! K;
   Step 6 removes the special auxiliary choice. This is the refinement square for g.
9. For arbitrary cf, cg, cgf choose dense refinements (det-nagata-refinement-common-dense)
   and conjugate the dense α by the comparisons φ of det-sf-comp-coherence-cocycle. Steps 6--8
   and the cocycle law show independence of the dense choices, and changing any one
   compactification composes only its φ. As φ_{c,d} is the refinement component for a dense
   refinement d → c, this is the displayed simultaneous refinement square; conversely the
   square at a common dense refinement of two triples gives compatibility with every
   prescribed comparison, including nondense ones. -/
theorem exists_nonrationalLocalizingLowerShriekComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
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
    ∃ (hf : ∀ (c : Compactification.BoundaryCompactification f)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hg : ∀ (c : Compactification.BoundaryCompactification g)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
          localizingClosureProEtale Λ Y K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hgf : ∀ (c : Compactification.BoundaryCompactification (f ≫ g))
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
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
