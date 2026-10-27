module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Sheaf.FieldTheory.FieldTower
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite Galois splitting into geometrically integral clopen components

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed p.150; Stacks Project,
Tags 054R, 033C, 0357, 09DT and 0EXM.
(blueprint: lem-sfb-galois-geometrically-integral-splitting)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A normal geometrically reduced integral finite type scheme over a field has normal
geometrically integral clopen components after a finite Galois extension. Every field base
change is Noetherian, the splitting projection is finite etale surjective, and properness
of the original scheme implies properness of each component.

Source: ILO X 2.3 Step 2, printed p.150; Stacks Tags 054R, 033C, 0357, 09DT and 0EXM.
(blueprint: lem-sfb-galois-geometrically-integral-splitting)

Proof:
1. Finite type is stable under base change (`lem-sfb-finite-type-composition-base-change`).
   A finite affine cover has finite type algebras over the extension field, which are
   Noetherian by `lem-wf-affine-noetherian-components`. This works for every extension F.
2. Apply `lem-sbc-generic-components-split` (054R) to get a finite etale extension L whose
   components stay irreducible and nonempty after every extension. The residue-field lemma
   `lem-weil-pbc-etale-algebra-residue-field-separable` makes L/e finite separable.
3. Base change gives a finite etale surjective projection B_L to B, using finite-morphism
   permanence, etale base change, and surjective base change. Its source is Noetherian by
   step 1. Apply `lem-fin-etale-normal-components` to partition B_L into finitely many
   nonempty normal integral clopen opens D_i. An irreducible subset cannot meet two such
   opens, so maximality identifies them exactly with the irreducible components. Nonemptiness
   of B_L makes the index set nonempty.
4. Every (D_i)_E is irreducible by step 2 and reduced because it is open in B_E, which is
   reduced by geometric reducedness. Thus every (D_i)_E is integral, even for inseparable E/L.
5. Apply `lem-weil-pbc-finite-galois-receiving-separable-extensions` to L/e. This gives a
   finite separable normal e0/e and an e-embedding L into e0. Pullback associativity identifies
   B_e0 with (B_L)_e0. The inverse images X_i of D_i remain disjoint clopen opens covering
   B_e0 by open-immersion base change. Their further field base changes identify with those
   of D_i, hence are integral by step 4. They are exactly the irreducible components.
6. By `lem-weil-pbc-spec-finite-ring-map-finite` and finite-separable-extension-etale, the
   spectrum map for e0/e is finite etale and surjective. Base change gives those properties
   for p. Applying the etale normal-component theorem once more gives normal local rings
   on B_e0; restriction gives the same local rings on each X_i.
7. If B/e is proper, proper base change makes B_e0/e0 proper. Each clopen inclusion is an
   immersion with closed image, hence a closed immersion by the closed-image criterion.
   `lem-weil-pbc-closed-immersion-proper` then gives properness of X_i/e0.
-/
theorem exists_finite_galois_geometrically_integral_clopen_components
    {e : Type u} [Field e] {B : Scheme.{u}}
    (f : B ⟶ Spec (CommRingCat.of e)) [IsIntegral B]
    [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyReduced f]
    (hB : ∀ b : B, IsDomain (B.presheaf.stalk b) ∧
      IsIntegrallyClosed (B.presheaf.stalk b)) :
    (∀ (F : Type u) [Field F] [Algebra e F],
      IsNoetherian (pullback f (Spec.map (CommRingCat.ofHom (algebraMap e F))))) ∧
    ∃ (e0 : Type u) (_ : Field e0) (_ : Algebra e e0),
      FiniteDimensional e e0 ∧ Algebra.IsSeparable e e0 ∧ Normal e e0 ∧
      IsFinite (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))) ∧
      Etale (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))) ∧
      Surjective (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))) ∧
      ∃ (n : ℕ) (U : Fin n →
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))).Opens),
        0 < n ∧
        (∀ i, IsClosed (U i : Set ↥
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))))) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
        (⨆ i, U i) = ⊤ ∧
        Set.range (fun i ↦ (U i : Set ↥
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))))) =
          irreducibleComponents ↥
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap e e0)))) ∧
        (∀ i, ∀ x : (U i).toScheme,
          IsDomain ((U i).toScheme.presheaf.stalk x) ∧
            IsIntegrallyClosed ((U i).toScheme.presheaf.stalk x)) ∧
        (∀ i, GeometricallyIntegral
          ((U i).ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap e e0))))) ∧
        (IsProper f → ∀ i, IsProper
          ((U i).ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap e e0))))) := by
  sorry

end AlgebraicGeometry
