module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Affine comparison of local dimension and transcendence degree

Source: Stacks Project, Morphisms, Tag 02JU, affine reduction of the dimension formula;
Schemes, Tags 01HV and 01HY; Algebra, Tags 00E3, 00KF and 00CT; Morphisms, Tag 01RV;
Fields, Tags 030G and 030H (blueprint: lem-trf-affine-local-dimension-term-comparison).

The residue fields of primes are Mathlib's `Ideal.ResidueField`, equipped with their
canonical fraction-ring structures over the quotient domains. All algebra structures
in the transcendence degrees below are specified by the actual induced ring maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Affine charts identify both local dimensions and both transcendence-degree terms,
including the naturality of the germ and residue-field isomorphisms.
Source: Stacks Project, Morphisms, Tag 02JU, affine reduction; Schemes, Tags 01HV and
01HY; Algebra, Tags 00E3, 00KF and 00CT; Morphisms, Tag 01RV; Fields, Tags 030G and
030H (blueprint: lem-trf-affine-local-dimension-term-comparison).

Proof:
1. Apply `lem-weil-pbc-affine-open-stalk-localization` to the two charts. The germ
   maps localize at the corresponding primes. The germ square for `f` and the
   localness of its stalk map imply contraction of the primes.
2. The two maps from the base localization to the source stalk agree on every
   fraction `a/t`, by the germ square, so the localization square commutes.
3. Ring isomorphisms preserve chains of primes. Apply
   `lem-weil-pbc-localization-dimension-chains-below-prime` to both rings. Appending
   the specified prime to a shorter chain identifies this supremum with its height,
   also for unbounded lengths.
4. Quotient the local-ring isomorphisms by their maximal ideals. By
   `lem-weil-pbc-prime-residue-field-algebra` these residue fields are fraction
   fields of the quotient domains. The square descends to the residue-field square;
   on the residue of `a/t` it is the residue of `phi(a)/phi(t)`.
5. Transport polynomial relations in both directions through the commuting field
   isomorphisms. Algebraically independent subsets and their cardinalities agree,
   giving the equality of residue-field transcendence degrees.
6. By `lem-sc-integral-function-field-affine-fraction`, the affine section rings
   are domains whose fraction fields are the generic stalks. Dominance sends the
   generic point to the generic point. The germ square identifies the actual
   generic stalk map with the fraction-field extension of the affine map and
   proves that the latter map is injective.
7. A fraction `a/t` satisfies the nonzero polynomial `t*T-a`. Thus the function
   field of the base has transcendence degree zero over its affine section ring;
   the same holds for the source and its affine section ring.
8. Apply `lem-exc-domain-transcendence-degree-tower` to the two injective towers
   `A -> B -> R(X)` and `A -> R(S) -> R(X)`. Substituting the two zeros proves the
   generic transcendence-degree comparison. This uses only cardinal addition of
   zero, so infinite transcendence degrees are included.

The point `x : V` witnesses nonemptiness of `V`, and its image witnesses
nonemptiness of `U`. The parameters `p` and `q` are fixed to the chart primes by
`hp` and `hq`. No Noetherian or finite-type assumption is imposed. -/
theorem affine_local_dimension_term_comparison
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f]
    (U : S.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : V)
    (p : PrimeSpectrum Γ(S, U)) (q : PrimeSpectrum Γ(X, V))
    (hp : p = hU.primeIdealOf ⟨f x, hVU x.property⟩)
    (hq : q = hV.primeIdealOf x) :
    ∃ hc : p.asIdeal = q.asIdeal.comap (f.appLE U V hVU).hom,
      ∃ (eS : Localization.AtPrime p.asIdeal ≃+* S.presheaf.stalk (f x))
        (eX : Localization.AtPrime q.asIdeal ≃+* X.presheaf.stalk x),
        eS.toRingHom.comp (algebraMap Γ(S, U) (Localization.AtPrime p.asIdeal)) =
          (S.presheaf.germ U (f x) (hVU x.property)).hom ∧
        eX.toRingHom.comp (algebraMap Γ(X, V) (Localization.AtPrime q.asIdeal)) =
          (X.presheaf.germ V x x.property).hom ∧
        (f.stalkMap x).hom.comp eS.toRingHom =
          eX.toRingHom.comp
            (Localization.localRingHom p.asIdeal q.asIdeal (f.appLE U V hVU).hom hc) ∧
        ringKrullDim (S.presheaf.stalk (f x)) = (p.asIdeal.height : WithBot ℕ∞) ∧
        ringKrullDim (X.presheaf.stalk x) = (q.asIdeal.height : WithBot ℕ∞) ∧
        ∃ (rS : S.residueField (f x) ≃+* p.asIdeal.ResidueField)
          (rX : X.residueField x ≃+* q.asIdeal.ResidueField),
          rS.toRingHom.comp (S.residue (f x)).hom =
            (IsLocalRing.residue (Localization.AtPrime p.asIdeal)).comp eS.symm.toRingHom ∧
          rX.toRingHom.comp (X.residue x).hom =
            (IsLocalRing.residue (Localization.AtPrime q.asIdeal)).comp eX.symm.toRingHom ∧
          rX.toRingHom.comp (f.residueFieldMap x).hom =
            (Ideal.ResidueField.map p.asIdeal q.asIdeal (f.appLE U V hVU).hom hc).comp
              rS.toRingHom ∧
          @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _
              (f.residueFieldMap x).hom.toAlgebra =
            @Algebra.trdeg p.asIdeal.ResidueField q.asIdeal.ResidueField _ _
              (Ideal.ResidueField.map p.asIdeal q.asIdeal
                (f.appLE U V hVU).hom hc).toAlgebra ∧
          @Algebra.trdeg Γ(S, U) Γ(X, V) _ _ (f.appLE U V hVU).hom.toAlgebra =
            @Algebra.trdeg S.functionField X.functionField _ _
              (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra := by
  sorry

end AlgebraicGeometry
