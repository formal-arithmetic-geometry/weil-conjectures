/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.RingTheory.GeneralizedHenselizationAtPrime
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.RingTheory.StrictlyHenselianNormal
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Mathlib.RingTheory.Etale.Field

/-! # Henselization, decomposition and residue inertia

Source: Stacks Project, Tag 0BSW (lemma-identify-inertia), and Tag 0BNE with
remark-variance (blueprint: lem-dl-a1-henselian-decomposition-inertia).

The finite-etale fibre model of the fundamental group is used. The recorded
finite-etale/FLC comparison identifies this model with `Scheme.flcFiber`.
`j` is the chosen residue embedding; its surjectivity is a conclusion.
`L` and `M` are chosen fraction fields of the embedded henselizations, not
additional finite extensions. All groups carry their existing Krull or evaluation topology.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped Pointwise

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Henselian decomposition, residue exactness and the compatible fundamental-group diagram.
Source: Stacks Project, Tag 0BSW and Tag 0BNE, remark-variance
(blueprint: lem-dl-a1-henselian-decomposition-inertia).

The equations for `eD` and `eI` identify the actual subgroups inside `Gal(Ω/F)`.
The residue formula determines `res` on the whole residue closure because the
pointed strict-henselization residue map is onto. The path `τ` is specified by
extension to `B_q` and reduction, so the fundamental-group identification is
compatible with the chosen embeddings, rather than an unspecified group isomorphism.
The equations for `eF` and `eL` specify the field identifications on every cover;
precomposition with the same field automorphism gives compatibility with `F → L`.

Proof (the ten steps of the node):
1. Integral closure in an algebraic extension is normal with fraction field Ω
   (lem-weil-pbc-integral-closure-algebraic-extension-normal). The Gabber localization
   lemma at the zero ideal makes B_q strictly henselian. Its residue field is algebraic
   over κ by reduction of monic equations, separable by perfection, and separably closed
   by strict henselianity. It is therefore an algebraic closure of κ.
2. The pointed ordinary-neighbourhood limit and its henselization comparison present H
   as a local ind-etale algebra with residue κ. The strict-henselization triples present
   S with residue κs. The etale-colimit normal-local-domain lemma makes both normal
   domains. Their embedded fraction fields are separable algebraic subfields of Ω.
3. A decomposition element acts locally on B_q. Uniqueness in the henselization
   universal property makes its action fix H, hence L.
4. Conversely an automorphism fixing L acts on each finite H-algebra H ⊗ A[b].
   The finite-over-henselian-local product theorem splits this into local factors.
   The two maps into B_q select the same factor, since their generic maps differ
   by a field automorphism. Their inverse images of the maximal ideal are maximal
   in that local factor, hence equal. Thus b belongs to q exactly when its image does.
5. For an inertia element, uniqueness of maps from the strict ind-etale colimit
   with fixed residue map makes it fix S and M. Conversely fixing M fixes L and
   the surjective residue of S, hence gives inertia.
6. The Krull group acts continuously on the discrete integral closure. Galois
   fixed fields and normality give B^Gal(Ω/F) = A. The profinite invariant-ring
   residue-surjection theorem gives the surjective residue map with inertia kernel.
7. Lift finitely many residue elements to B. Their stabilizers contain open finite
   field stabilizers, proving continuity. Finite-element stabilizers also identify
   each intrinsic Krull topology with the subgroup topology.
8. Finite-etale lifting for the henselian pair (H,m_H), using the proper identity,
   identifies finite-etale H-algebras with finite-etale κ-algebras. Over B_q each
   such algebra splits into copies of B_q, since its residue is separably closed.
9. Extending a generic geometric point uniquely to B_q and reducing gives the
   natural path τ. The finite-etale/FLC equivalence identifies the two models of π₁.
   Evaluation stabilizers show that all resulting group identifications are topological.
10. The lift of g composed with a point reduces to the residue automorphism composed
    with its reduction. This proves the residue/fundamental-group comparison. The field
    fibre formulas give the commuting maps to π₁(Spec F). Finally the purely inseparable
    complement of Ω in an algebraic closure of L has unique automorphism extensions;
    finite-element stabilizers show restriction is a topological group isomorphism.
-/
theorem henselian_decomposition_inertia
    (A F Ω H S L M κs : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [PerfectField (ResidueField A)]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    [Algebra A Ω] [IsScalarTower A F Ω]
    (q : Ideal (integralClosure A Ω)) [q.IsMaximal]
    (hq : q.comap (algebraMap A (integralClosure A Ω)) = maximalIdeal A)
    [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (maximalIdeal A)) H]
    [Algebra A H] [IsScalarTower A (Localization.AtPrime (maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (maximalIdeal A) H)
    [Field κs] [Algebra (ResidueField A) κs] [IsSepClosure (ResidueField A) κs]
    [Algebra A κs] [IsScalarTower A (ResidueField A) κs]
    [CommRing S] [IsLocalRing S] [Algebra A S]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A κs S)
    (h : H →+* Localization.AtPrime q) (c : H →+* S)
    (i : S →+* Localization.AtPrime q)
    (j : κs →+* ResidueField (Localization.AtPrime q))
    (hh : IsLocalHom h) (hc : IsLocalHom c) (hi : IsLocalHom i)
    (hinj : Function.Injective h) (iinj : Function.Injective i)
    (hhA : h.comp (algebraMap A H) = algebraMap A (Localization.AtPrime q))
    (hcA : c.comp (algebraMap A H) = algebraMap A S)
    (hich : i.comp c = h)
    (hj : ∀ a : A, j (algebraMap A κs a) =
      IsLocalRing.residue (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a))
    (hij : (IsLocalRing.residue (Localization.AtPrime q)).comp i = j.comp P.residueMap)
    [Field L] [Algebra H L] [IsFractionRing H L] [Algebra L Ω]
    [Algebra H Ω] [IsScalarTower H L Ω]
    (hL : ∀ x : H, algebraMap H Ω x = Ideal.atPrimeToField q (h x))
    [Algebra F L] [IsScalarTower F L Ω]
    [Field M] [Algebra S M] [IsFractionRing S M] [Algebra M Ω]
    [Algebra S Ω] [IsScalarTower S M Ω]
    (hM : ∀ x : S, algebraMap S Ω x = Ideal.atPrimeToField q (i x))
    [Algebra F M] [IsScalarTower F M Ω] :
    ∃ (_ : IsSepClosed Ω) (_ : IsSepClosed κs),
    IsDomain H ∧ IsIntegrallyClosed H ∧ IsDomain S ∧ IsIntegrallyClosed S ∧
    Algebra.IsSeparable F L ∧ Algebra.IsAlgebraic F L ∧
    Algebra.IsSeparable F M ∧ Algebra.IsAlgebraic F M ∧
    IsSepClosure L Ω ∧ IsSepClosure M Ω ∧ IsAlgClosed κs ∧
    Function.Surjective j ∧ Function.Surjective P.residueMap ∧
    (∃ e : (integralClosure A Ω ⧸ q) ≃+* κs,
      ∀ b : integralClosure A Ω, j (e (Ideal.Quotient.mk q b)) =
        IsLocalRing.residue (Localization.AtPrime q) (algebraMap _ (Localization.AtPrime q) b)) ∧
    ∃ (eD : MulAction.stabilizer Gal(Ω/F) q ≃ₜ* Gal(Ω/L))
      (eI : q.inertia Gal(Ω/F) ≃ₜ* Gal(Ω/M))
      (res : MulAction.stabilizer Gal(Ω/F) q →* Gal(κs/ResidueField A)),
      (∀ (g : MulAction.stabilizer Gal(Ω/F) q) (x : Ω), eD g x = g.val x) ∧
      (∀ (g : q.inertia Gal(Ω/F)) (x : Ω), eI g x = g.val x) ∧
      Continuous res ∧ Function.Surjective res ∧
      (∀ (g : MulAction.stabilizer Gal(Ω/F) q) (s : S),
        j (res g (P.residueMap s)) = IsLocalRing.residue (Localization.AtPrime q)
          (Ideal.atPrimeMap q g.val g.property (i s))) ∧
      res.ker.map (MulAction.stabilizer Gal(Ω/F) q).subtype = q.inertia Gal(Ω/F) ∧
      ∃ (rH : H →+* ResidueField A)
        (τ : fiber (pointOfAlgebra Ω (𝟙 (Spec (.of H)))) ≅
          fiber (pointOfAlgebra κs (Spec.map (CommRingCat.ofHom rH))))
        (eπ : Aut (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of H))))) ≃ₜ*
          Gal(κs/ResidueField A))
        (eF : Gal(Ω/F) ≃ₜ* Aut (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of F))))))
        (eL : Gal(Ω/L) ≃ₜ* Aut (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L))))))
        (β : fiber (pointOfAlgebra Ω (𝟙 (Spec (.of F)))) ≅
          fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap F L))))),
        (∀ x : H, algebraMap (ResidueField A) κs (rH x) = P.residueMap (c x)) ∧
        (∀ (Q : (Spec (.of H)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of H))))).obj Q),
          ∃! v : Spec (.of (Localization.AtPrime q)) ⟶ Q.obj.left,
            v ≫ Q.obj.hom = Spec.map (CommRingCat.ofHom h) ∧
            Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField q)) ≫ v = t.left ∧
            Spec.map (CommRingCat.ofHom j) ≫ (τ.hom.app Q t).left =
              Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Localization.AtPrime q))) ≫ v) ∧
        (∀ ρ : Gal(κs/ResidueField A),
          eπ.symm ρ = Iso.conjAut τ.symm (galoisToAut (Spec.map (CommRingCat.ofHom rH)) ρ)) ∧
        (∀ g : MulAction.stabilizer Gal(Ω/F) q,
          eπ (galoisToAut (𝟙 (Spec (.of H))) ((eD g).restrictScalars H)) = res g) ∧
        (∀ σ : Gal(Ω/F), eF σ = galoisToAut (𝟙 (Spec (.of F))) σ) ∧
        (∀ σ : Gal(Ω/L), eL σ = galoisToAut (𝟙 (Spec (.of L))) σ) ∧
        (∀ (σ : Gal(Ω/L)) (Q : (Spec (.of F)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L))))).obj
            ((pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q)),
          (pullbackFiberIso (Spec.map (CommRingCat.ofHom (algebraMap F L)))
            (pointOfAlgebra Ω (𝟙 (Spec (.of L))))).hom.app Q
              ((eL σ).hom.app _ t) =
          (galoisToAut (Spec.map (CommRingCat.ofHom (algebraMap F L)))
            σ).hom.app Q
              ((pullbackFiberIso (Spec.map (CommRingCat.ofHom (algebraMap F L)))
                (pointOfAlgebra Ω (𝟙 (Spec (.of L))))).hom.app Q t)) ∧
        (∀ (Q : (Spec (.of F)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of F))))).obj Q),
          (β.hom.app Q t).left = t.left) ∧
        (∀ (g : MulAction.stabilizer Gal(Ω/F) q) (Q : (Spec (.of F)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of F))))).obj Q),
          β.hom.app Q ((eF g.val).hom.app Q t) =
            (galoisToAut (Spec.map (CommRingCat.ofHom (algebraMap F L)))
              (eD g)).hom.app Q (β.hom.app Q t)) ∧
        (∀ (Ωbar : Type u) [Field Ωbar] [Algebra L Ωbar] [IsAlgClosure L Ωbar]
          [Algebra Ω Ωbar] [IsScalarTower L Ω Ωbar],
          ∃ e : Gal(Ωbar/L) ≃ₜ* Gal(Ω/L),
            ∀ (σ : Gal(Ωbar/L)) (x : Ω),
              algebraMap Ω Ωbar (e σ x) = σ (algebraMap Ω Ωbar x)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
