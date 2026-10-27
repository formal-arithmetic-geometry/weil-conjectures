module

public import Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Sheaf.AlgebraicGeometry.CartierDivisorFinite
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import Sheaf.AlgebraicGeometry.Curve.SmoothCurveClosedStalkStructure
import WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Etale.Kaehler

/-! # A geometric witness for a pair of orbit norms

Source: Stacks Project, Curves, Tag 0C1E, `lemma-uniformizer-works`; Modules, Tag 01AM;
Coherent, Tag 02O5. The finite-zero-set and single-simple-factor norm argument is the
agent assembly in the node's proof.
(blueprint: lem-sfb-norm-pair-geometric-witness)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A simple zero at a free orbit point gives a second section whose norm forms a generating
pair with the first norm, and whose ratio has nonzero differential at that point.
The vector space of global sections uses restriction of scalars along the structure map.
Properness includes finite type. A proper evaluation kernel is expressed equivalently by
existence of a section with nonzero residue value. Generation by `s, t` is epi of the free-sheaf
map of the two-entry family `(s, t)` indexed by `ULift (Fin 2)`. The final differential
clause quantifies all local representatives of the germ `α / β`, and uses the actual sheaf
derivation and fibre.

Source: Stacks Project, Curves, Tag 0C1E; Modules, Tags 01AM, 01CA, 01CD;
Coherent, Tag 02O5; agent norm-pair computation of this node.
(blueprint: lem-sfb-norm-pair-geometric-witness)

Proof, in the order of the node's ten steps:
1. Tensor powers of L are invertible. Proper-field invertible coherence
   (lem-trf-proper-field-invertible-coherent) and proper coherent cohomology finiteness
   (lem-pc-euler-characteristic-well-defined, pqf-def-cohomology), in degree zero, give
   finite-dimensional global sections; no ampleness is used.
2. The simple zero implies a is nonzero. By lem-pc-nonzero-section-integral-cartier its
   zero scheme E is an effective Cartier divisor with underlying set Z(a). Use
   lem-pc-scheme-dimension-local-rings to convert topological dimension one to local-ring
   dimension, then lem-pc-cartier-divisor-finite-over-field makes E zero dimensional.
3. By lem-sc-noetherian-closed-subset-finite-components, E has finitely many irreducible
   components. Each has one point, since its points are closed and its dimension is zero.
   Thus Z(a) is finite and closed in D. The finite-type closed-point residue-field lemma
   lem-weil-pbc-closed-point-residue-field-base makes these points k-rational.
4. The finite union S of inverse translates of Z(a) is finite and consists of rational
   closed points. For h in G, (g*h⁻¹)(h*y)=g*y proves stability; the inverse gives equality.
5. Global generation prevents evaluation at a point from vanishing identically: reduce a
   local generating expression for a frame modulo the maximal ideal to get a contradiction.
   Thus each evaluation has a proper kernel.
6. Algebraic closedness makes k infinite (otherwise the product of T-c, minus 1, has no
   root). Apply lem-pc-finite-linear-avoidance to the finitely many proper kernels to get b.
7. In tensor products of pulled-back frames, the norm coefficient is the product of the
   translated coefficients, by induction over pencilGroupElements. Pullback identifies
   residue fields, so this product vanishes exactly on the union of translated zero sets.
8. Stability of S makes every translated b nonzero on S. Outside S the norm of a is
   nonzero. Hence the norms have no common zero and locally generate the invertible power;
   equivalently the free-sheaf map for their two-entry family is epi (Tag 01AM).
9. At x the identity factor for a lies in m minus m² and every other factor is a unit.
   Their product therefore lies in m minus m². All factors for b are units. Changing a
   frame multiplies both coefficients by the same unit, preserving these assertions and
   the quotient germ.
10. By lem-a1-smooth-curve-closed-stalk-structure the closed stalk is Noetherian with
    residue k. Apply lem-weil-pbc-separable-residue-cotangent-injective to the nonzero
    class of α/β in m/m². The comparisons lem-trf-affine-chart-stalk-differentials and
    lem-weil-pbc-kahler-differentials-localization identify this nonzero differential
    with the value of the sheaf derivation on any local representative. No step divides
    by the group order, so every characteristic is included. -/
theorem norm_pair_geometric_witness
    (k : Type u) [Field k] [IsAlgClosed k] (D : Scheme.{u})
    (f : D ⟶ Spec (.of k)) [Smooth f] [IsProper f] [IsIntegral D]
    (hdim : topologicalKrullDim D = 1)
    (G : Type v) [Group G] [Finite G] (ρ : G →* Aut D)
    (hρ : ∀ g : G, (ρ g).hom ≫ f = f)
    (x : D) (hx : IsClosed ({x} : Set D))
    (hxr : Function.Bijective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        D.presheaf.germ ⊤ x trivial ≫ D.residue x).hom))
    (hfree : Function.Injective (fun g : G ↦ (ρ g).hom x))
    (L : D.Modules) [L.IsInvertible] (n : ℕ) (hn : 1 ≤ n)
    (hgen : Nonempty (SheafOfModules.GeneratingSections (L.tensorPow n)))
    (a : (L.tensorPow n).sections)
    (ha : ∀ (U : D.Opens) (hxU : x ∈ U) (e : Γ(L.tensorPow n, U)),
      IsFreeGenerator e → ∀ α : Γ(D, U), a.val (op U) = α • e →
        D.presheaf.germ U x hxU α ∈ IsLocalRing.maximalIdeal (D.presheaf.stalk x) ∧
        D.presheaf.germ U x hxU α ∉ IsLocalRing.maximalIdeal (D.presheaf.stalk x) ^ 2)
    (haorbit : ∀ g : G, g ≠ 1 →
      (ρ g).hom x ∈ nonvanishingLocus (L.tensorPow n) (a.val (op ⊤))) :
    (⋃ g : G, (ρ g).hom ⁻¹'
      (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ).Finite ∧
    (∀ (h : G) (y : D),
      (ρ h).hom y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
        (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ) ↔
      y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
        (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ)) ∧
    (∀ y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
        (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ),
      IsClosed ({y} : Set D) ∧ Function.Bijective
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          D.presheaf.germ ⊤ y trivial ≫ D.residue y).hom)) ∧
    @FiniteDimensional k Γ(L.tensorPow n, ⊤) _ _
      (Module.compHom _ (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)) ∧
    (∀ y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
        (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ),
      ∃ c : (L.tensorPow n).sections, residueValue (c.val (op ⊤)) y trivial ≠ 0) ∧
    (∃ b : (L.tensorPow n).sections, ∀ y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
        (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ),
      y ∈ nonvanishingLocus (L.tensorPow n) (b.val (op ⊤))) ∧
    ∀ b : (L.tensorPow n).sections,
      (∀ y ∈ (⋃ g : G, (ρ g).hom ⁻¹'
          (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ),
        y ∈ nonvanishingLocus (L.tensorPow n) (b.val (op ⊤))) →
      (nonvanishingLocus ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n)
        ((pencilNormSection (fun g ↦ ρ g) L n a).val (op ⊤)))ᶜ =
        (⋃ g : G, (ρ g).hom ⁻¹'
          (nonvanishingLocus (L.tensorPow n) (a.val (op ⊤)))ᶜ) ∧
      Disjoint
        (nonvanishingLocus ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n)
          ((pencilNormSection (fun g ↦ ρ g) L n a).val (op ⊤)))ᶜ
        (nonvanishingLocus ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n)
          ((pencilNormSection (fun g ↦ ρ g) L n b).val (op ⊤)))ᶜ ∧
      Epi (((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n).freeHomEquiv.symm
        (fun i : ULift.{u} (Fin 2) ↦ if i.down = 0 then
          pencilNormSection (fun g ↦ ρ g) L n a else pencilNormSection (fun g ↦ ρ g) L n b)) ∧
      ∀ (U : D.Opens) (hxU : x ∈ U)
        (e : Γ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow n, U)),
        IsFreeGenerator e → ∀ α β : Γ(D, U),
        (pencilNormSection (fun g ↦ ρ g) L n a).val (op U) = α • e →
        (pencilNormSection (fun g ↦ ρ g) L n b).val (op U) = β • e →
        (D.presheaf.germ U x hxU α ∈ IsLocalRing.maximalIdeal (D.presheaf.stalk x) ∧
          D.presheaf.germ U x hxU α ∉ IsLocalRing.maximalIdeal (D.presheaf.stalk x) ^ 2) ∧
        IsUnit (D.presheaf.germ U x hxU β) ∧
        ∀ (V : D.Opens) (hxV : x ∈ V) (q : Γ(D, V)),
          D.presheaf.germ V x hxV q = D.presheaf.germ U x hxU α *
            Ring.inverse (D.presheaf.germ U x hxU β) →
          residueValue (M := f.relativeDifferentials)
            (f.relativeDifferentialsDerivation.d q) x hxV ≠ 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
