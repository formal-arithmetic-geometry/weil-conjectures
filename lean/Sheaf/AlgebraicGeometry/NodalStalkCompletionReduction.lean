module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.LocalCompletionQuotient

/-!
# Completed stalks and the closed fibre of a flat finite type morphism

Source: Stacks Project, Tag 0CBX, `lemma-formal-local-structure-nodal-family`,
first proof paragraph (blueprint: lem-trf-nodal-stalk-completion-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Completed stalks of a flat locally finite type morphism have the expected closed fibre.

Source: Stacks Project, Tag 0CBX, first proof paragraph; Algebra Tags 0316, 05GI,
05GG, 00MA; More on Algebra Tag 0C4G; Schemes Tag 0HA1.
(blueprint: lem-trf-nodal-stalk-completion-reduction)

The Noetherian instance quantified inside the conclusion is available from its first
conjunct; it is not an additional hypothesis. It lets Mathlib construct the local-ring
instances on the completions. The residue equivalences are specified on original germs.
The map `φ` is specified at every finite quotient, so it is the induced completion map.
The coefficient homomorphisms `cQ` and `cD` are specified after the surjective residue map
of the base stalk, hence are the canonical coefficient actions, rather than arbitrary
algebra structures. The ring equivalence `e` commuting with these coefficient maps is
exactly a residue-field algebra equivalence. Its final two clauses specify the square
on original germs and the square at every finite completion level.

Proof:
1. The stalk map is local and flat. By
   `lem-trf-locally-finite-type-stalk-essentially-finite-type`, the target stalk is a
   localization of a finite type algebra over the base stalk. Apply
   `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-localization-noetherian` to obtain its Noetherianity.
2. Apply `lem-weil-pbc-adic-completion-noetherian` and
   `lem-weil-pbc-local-completion-local-ring` to both stalks. Their extended maximal
   ideals are the maximal ideals of the completions, and completion preserves residue
   fields. Combine this with the given residue-field isomorphism. Finite generation
   and `lem-weil-pbc-adic-completion-mod-ideal` give completeness for these ideals.
3. Apply `lem-weil-pbc-flat-completion` to the flat local stalk map. Its levelwise
   characterization gives `φ`, the commuting completion square, and flatness.
   Images of the extended base maximal ideal lie in the target maximal ideal, so `φ`
   is local; its residue map is the given residue-field map.
4. By `lem-sbc-scheme-fibre-stalk-quotient`, the fibre projection on stalks is onto
   with kernel the base maximal ideal extended to the target stalk. As a surjective
   local map it carries the target maximal ideal onto the fibre maximal ideal.
   Apply `lem-weil-pbc-local-completion-quotient` to this surjection to obtain `e`
   and its coordinatewise compatibility with completion.
5. Extending the stalk kernel to the completion equals extending the maximal ideal
   of the completed base, by the commuting square for `φ`. The scalar maps descend
   from the base stalk along its residue map. On a representative from the base
   stalk the square for `e` proves that the scalar actions agree, so `e` is a
   residue-field algebra equivalence. The same square gives compatibility on germs,
   and the coordinatewise construction gives compatibility at every finite level.
-/
theorem nodal_stalk_completion_reduction
    {T S : Scheme.{u}} (f : T ⟶ S) (t : T) [LocallyOfFiniteType f]
    [IsNoetherianRing (S.presheaf.stalk (f t))]
    (hflat : (f.stalkMap t).hom.Flat)
    (hresidue : IsIso (f.residueFieldMap t)) :
    IsNoetherianRing (T.presheaf.stalk t) ∧
    ∀ [IsNoetherianRing (T.presheaf.stalk t)],
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))) ∧
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk
    t)) ∧
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))) = ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))).map (algebraMap
    (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))))) ∧
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)) = ((IsLocalRing.maximalIdeal (T.presheaf.stalk t)).map (algebraMap
    (T.presheaf.stalk t) (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)))) ∧
    IsAdicComplete ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))).map (algebraMap
    (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))))) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))) ∧
    IsAdicComplete ((IsLocalRing.maximalIdeal (T.presheaf.stalk t)).map (algebraMap
    (T.presheaf.stalk t) (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)))) (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)) ∧
    ∃ eA : (S.residueField (f t)) ≃+* IsLocalRing.ResidueField (AdicCompletion
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t))),
    (∀ a : (S.presheaf.stalk (f t)), eA ((IsLocalRing.residue (S.presheaf.stalk (f t))) a) =
    IsLocalRing.residue (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))) ((algebraMap (S.presheaf.stalk (f t)) (AdicCompletion
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t)))) a)) ∧
    ∃ eB : (S.residueField (f t)) ≃+* IsLocalRing.ResidueField (AdicCompletion
    (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t)),
    (∀ a : (S.presheaf.stalk (f t)), eB ((IsLocalRing.residue (S.presheaf.stalk (f t))) a) =
    IsLocalRing.residue (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t)) ((algebraMap (T.presheaf.stalk t) (AdicCompletion
    (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t))) ((f.stalkMap t).hom a)))
    ∧
    ∃ φ : (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) (S.presheaf.stalk (f
    t))) →+* (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t)),
    IsLocalHom φ ∧ φ.Flat ∧
    (φ.comp (algebraMap (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal
    (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t)))) = (algebraMap (T.presheaf.stalk t)
    (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t))).comp
    (f.stalkMap t).hom) ∧
    (∀ (r : ℕ) (x : (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t)))) (a : (S.presheaf.stalk (f t))), AdicCompletion.evalₐ
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) r x = Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) ^ r) a → AdicCompletion.evalₐ
    (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) r (φ x) = Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (T.presheaf.stalk t)) ^ r) ((f.stalkMap t).hom a)) ∧
    ∃ (cQ : (S.residueField (f t)) →+* ((AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk
    t)) (T.presheaf.stalk t)) ⧸ ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))).map (algebraMap
    (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))))).map φ)) (cD : (S.residueField (f t)) →+* (AdicCompletion
    (IsLocalRing.maximalIdeal ((f.fiber (f t)).presheaf.stalk (f.asFiber t))) ((f.fiber (f
    t)).presheaf.stalk (f.asFiber t)))) (e : ((AdicCompletion (IsLocalRing.maximalIdeal
    (T.presheaf.stalk t)) (T.presheaf.stalk t)) ⧸ ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f
    t))).map (algebraMap (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal
    (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t))))).map φ) ≃+* (AdicCompletion
    (IsLocalRing.maximalIdeal ((f.fiber (f t)).presheaf.stalk (f.asFiber t))) ((f.fiber (f
    t)).presheaf.stalk (f.asFiber t)))),
    (∀ a : (S.presheaf.stalk (f t)), cQ ((IsLocalRing.residue (S.presheaf.stalk (f t))) a) =
    (Ideal.Quotient.mk (((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))).map (algebraMap
    (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))))).map φ)) (φ ((algebraMap (S.presheaf.stalk (f t)) (AdicCompletion
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t)))) a))) ∧
    (∀ a : (S.presheaf.stalk (f t)), cD ((IsLocalRing.residue (S.presheaf.stalk (f t))) a) =
    (algebraMap ((f.fiber (f t)).presheaf.stalk (f.asFiber t)) (AdicCompletion
    (IsLocalRing.maximalIdeal ((f.fiber (f t)).presheaf.stalk (f.asFiber t))) ((f.fiber (f
    t)).presheaf.stalk (f.asFiber t)))) ((f.fiberStalkMap t).hom ((f.stalkMap t).hom a))) ∧
    e.toRingHom.comp cQ = cD ∧
    (∀ b : (T.presheaf.stalk t), e ((Ideal.Quotient.mk (((IsLocalRing.maximalIdeal (S.presheaf.stalk
    (f t))).map (algebraMap (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal
    (S.presheaf.stalk (f t))) (S.presheaf.stalk (f t))))).map φ)) ((algebraMap (T.presheaf.stalk t)
    (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t))) b)) =
    (algebraMap ((f.fiber (f t)).presheaf.stalk (f.asFiber t)) (AdicCompletion
    (IsLocalRing.maximalIdeal ((f.fiber (f t)).presheaf.stalk (f.asFiber t))) ((f.fiber (f
    t)).presheaf.stalk (f.asFiber t)))) ((f.fiberStalkMap t).hom b)) ∧
    (∀ (r : ℕ) (x : (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
    (T.presheaf.stalk t))) (b : (T.presheaf.stalk t)), AdicCompletion.evalₐ
    (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) r x = Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (T.presheaf.stalk t)) ^ r) b → AdicCompletion.evalₐ
    (IsLocalRing.maximalIdeal ((f.fiber (f t)).presheaf.stalk (f.asFiber t))) r (e
    ((Ideal.Quotient.mk (((IsLocalRing.maximalIdeal (S.presheaf.stalk (f t))).map (algebraMap
    (S.presheaf.stalk (f t)) (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f t)))
    (S.presheaf.stalk (f t))))).map φ)) x)) = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal ((f.fiber
    (f t)).presheaf.stalk (f.asFiber t))) ^ r) ((f.fiberStalkMap t).hom b)) := by
  sorry

end AlgebraicGeometry
