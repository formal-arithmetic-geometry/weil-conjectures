module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Invariant semilocal generalizations for a finite descent datum

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1, reduction 6,
p. 5-21, and Lemma 4.3, p. 5-17; Stacks Tags 00DS and 00E3.
(blueprint: lem-sfb-finite-datum-semilocal-generalizations)

The relation maps are the first projection and the recorded descent datum's `toHom`.
Equality of the two pullback subfunctors is expressed on every scheme-valued point by
existence of the corresponding factorization through the monomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite invariant subset in a quasi-affine open has an invariant affine semilocal
scheme of generalizations. The finite covering morphism need not be flat, and the subset
may be empty. Source: Raynaud, Theorem 4.1, reduction 6, p. 5-21, and Lemma 4.3, p. 5-17.
(blueprint: lem-sfb-finite-datum-semilocal-generalizations)

Proof:
1. For the empty subset use Spec of the zero ring; both pullbacks are empty and its
   maximal spectrum is empty.
2. Embed the given quasi-affine open into an affine scheme. Prime avoidance
   (lem-weil-pbc-prime-avoidance, Stacks 00DS) gives a principal affine open containing
   the finite subset and contained in that open. Its affineness is clause (0) of
   lem-weil-pbc-affine-ideals-closed-subscheme (Stacks 01I3).
3. In this affine chart Spec A, localize at the complement of the union of the finitely
   many point primes. By lem-weil-pbc-localization-spectrum-embedding and prime avoidance,
   the image consists exactly of primes contained in one of those point primes: these
   are precisely the points specializing to a point of E (Stacks 00E3).
4. The maximal primes of the localization are exactly the inclusion-maximal members of
   the finite family of point primes. Thus the coordinate ring has finitely many
   maximal ideals, including when some of the original points specialize to others.
5. The localization map is flat and monic by lem-sfb-localization-spectrum-flat-monomorphism.
   Its composite with the affine chart inclusion has the same properties. The source is
   quasi-compact by lem-weil-pbc-affine-scheme-qcqs; the target is quasi-separated by
   lem-weil-pbc-locally-noetherian-quasi-separated. Apply clause (1) of
   lem-weil-pbc-qcqs-morphism-permanence to obtain quasi-compactness of the composite.
6. Both relation maps are finite base changes of q, the second via the descent
   isomorphism (lem-weil-pbc-finite-morphism-permanence). They are therefore closed by
   lem-weil-pbc-finite-closed-map-finite-fibres. Lifting specializations along a closed
   map (lem-trf-closed-map-specializing) shows that inverse image commutes with taking
   these generalizations. The assumed equality for E gives equality for its generalizations.
7. The two pullbacks of j are quasi-compact flat monomorphisms by base change
   (lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence).
   Their images are equal by lem-weil-pbc-base-change-image and step 6. The uniqueness
   and factorization clauses of lem-sfb-qc-flat-monomorphism-ringed-image identify their
   subfunctors. Reflexivity and transitivity of specialization give containment of E
   and stability under generalization.
-/
theorem exists_invariant_semilocal_generalizations
    {Q S : Scheme.{u}} [IsAffine Q] [IsAffine S]
    (q : Q ⟶ S) [IsFinite q] [Surjective q]
    (V : Over Q) [IsLocallyNoetherian V.left] [CompactSpace V.left]
    (D : Over.DescentDatum q V) (E : Set V.left) (hE : E.Finite)
    (hInvariant : pullback.fst (V.hom ≫ q) q ⁻¹' E = D.toHom ⁻¹' E)
    (hQuasiAffine : ∃ W : V.left.Opens, E ⊆ (W : Set V.left) ∧
      ∃ (A : Scheme.{u}) (i : W.toScheme ⟶ A),
        IsAffine A ∧ IsOpenImmersion i ∧ CompactSpace W.toScheme) :
    ∃ (L : Scheme.{u}) (j : L ⟶ V.left),
      IsAffine L ∧ QuasiCompact j ∧ Flat j ∧ Mono j ∧
      Set.range j = {z | ∃ e ∈ E, z ⤳ e} ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ pullback (V.hom ≫ q) q),
        (∃ a : T ⟶ L, a ≫ j = g ≫ pullback.fst (V.hom ≫ q) q) ↔
          ∃ a : T ⟶ L, a ≫ j = g ≫ D.toHom) ∧
      E ⊆ Set.range j ∧ StableUnderGeneralization (Set.range j) ∧
      Finite (MaximalSpectrum Γ(L, ⊤)) := by
  sorry

end AlgebraicGeometry
