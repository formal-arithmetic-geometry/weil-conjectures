/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Paper.EtaleFiniteDataDescent

/-! # Compatible cocone legs across prime localization -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Every global cocone has a unique local cocone with compatible pointed legs.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-extension)

Proof: Express R_p as the filtered colimit of R_s for s outside p. Descend each
finitely presented etale R_p-algebra to an etale R_s-algebra. Restrict its pointing
into K; its kernel and residue field factorization make it an R-triple. The global
cocone leg on this model inverts the other denominators, by naturality on pointed
principal refinements. Extend it uniquely to the original local algebra. Descend
morphisms, equalities, and both directions and inverse relations of comparison
isomorphisms to common principal stages. These facts imply independence of model,
naturality of the extended legs, and compatibility with every pointed R-map into
a local triple. Every local triple has such a descended model, and the localization
extension is unique, so any other compatible local cocone has exactly these legs. -/
theorem etaleResidueTriples_primeLocalization_cocone_extension
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V) :
    ∃! θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ := by sorry

end AlgebraicGeometry.Scheme
