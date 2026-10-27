module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Uniform vertical order normalizes a generic line-bundle frame

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, 4.3, printed p.104 (PDF p.110).
(blueprint: lem-sfb-trait-line-section-order-normalization)

The generic fibre is represented by its canonical open D(pi). Equalities involving
integer powers are cleared using the positive and negative parts of the exponent.
The local order condition means extension to a frame on a neighborhood of the point,
exactly the germ formulation in BLR. The special fibre is the actual fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The image of the uniformizer in global functions.
Source: BLR 4.3, p.104 (blueprint: lem-sfb-trait-line-section-order-normalization). -/
noncomputable def traitUniformizerSection {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (π : R) : Γ(Z, ⊤) :=
  f.appTop ((ΓSpecIso (.of R)).inv π)

/-- The generic fibre as the canonical principal open D(pi); over a DVR this is Z_E.
Source: BLR 4.3, p.104 (blueprint: lem-sfb-trait-line-section-order-normalization). -/
noncomputable def traitGenericOpen {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (π : R) : Z.Opens :=
  Z.basicOpen (traitUniformizerSection f π)

/-- The special fibre Z times Spec(k), with k the canonical residue field R/m.
Source: BLR 4.3, p.104 (blueprint: lem-sfb-trait-line-section-order-normalization). -/
noncomputable def traitSpecialFiber {R : Type u} [CommRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))

/-- The canonical inclusion of the special fibre.
Source: BLR 4.3, p.104 (blueprint: lem-sfb-trait-line-section-order-normalization). -/
noncomputable def traitSpecialFiberι {R : Type u} [CommRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R)) : traitSpecialFiber f ⟶ Z :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))

/-- On V intersect D(pi), t equals pi^(-n) s. Both signs of n are expressed using
nonnegative powers, so no inverse of pi is chosen in functions on V.
Source: BLR 4.3, p.104 (blueprint: lem-sfb-trait-line-section-order-normalization). -/
def TraitLineSectionNormalizedOn {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (π : R) (L : Z.Modules)
    (s : Γ(L, traitGenericOpen f π)) (n : ℤ) (V : Z.Opens) (t : Γ(L, V)) : Prop :=
  (Z.presheaf.map (homOfLE (le_top : V ⊓ traitGenericOpen f π ≤ ⊤)).op
      (traitUniformizerSection f π)) ^ n.toNat •
      L.presheaf.map (homOfLE (inf_le_left : V ⊓ traitGenericOpen f π ≤ V)).op t =
    (Z.presheaf.map (homOfLE (le_top : V ⊓ traitGenericOpen f π ≤ ⊤)).op
      (traitUniformizerSection f π)) ^ (-n).toNat •
      L.presheaf.map
        (homOfLE (inf_le_right : V ⊓ traitGenericOpen f π ≤ traitGenericOpen f π)).op s

/-- Order n at z: the normalized generic section extends to a local frame at z.
This uses the existing IsFreeGenerator, rather than a second definition of a frame.
Source: BLR 4.3, p.104, definition of order.
(blueprint: lem-sfb-trait-line-section-order-normalization). -/
def TraitLineSectionHasOrder {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (π : R) (L : Z.Modules)
    (s : Γ(L, traitGenericOpen f π)) (z : Z) (n : ℤ) : Prop :=
  ∃ (V : Z.Opens), z ∈ V ∧ ∃ t : Γ(L, V),
    Modules.IsFreeGenerator t ∧ TraitLineSectionNormalizedOn f π L s n V t

/-- pi^(-m) a is the restriction of a global unit; the equality is denominator-cleared.
Source: BLR 4.3, p.104, generic-unit normalization.
(blueprint: lem-sfb-trait-line-section-order-normalization). -/
def TraitUnitNormalization {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (π : R) (a : Γ(Z, traitGenericOpen f π)) (m : ℤ) : Prop :=
  ∃ b : Γ(Z, ⊤), IsUnit b ∧
    (Z.presheaf.map (homOfLE (le_top : traitGenericOpen f π ≤ ⊤)).op
      (traitUniformizerSection f π)) ^ m.toNat *
        Z.presheaf.map (homOfLE (le_top : traitGenericOpen f π ≤ ⊤)).op b =
      (Z.presheaf.map (homOfLE (le_top : traitGenericOpen f π ≤ ⊤)).op
        (traitUniformizerSection f π)) ^ (-m).toNat * a

/-- Evaluation of a generic function at the generic point of a trait-valued point.
The proof h records that the generic point lands in D(pi); appLE and GammaSpecIso
are the canonical pullback of functions and the affine global-sections identification.
Source: BLR 4.3, p.104, evaluation paragraph.
(blueprint: lem-sfb-trait-line-section-order-normalization). -/
noncomputable def traitGenericUnitValue {R A : Type u} [CommRing R] [CommRing A]
    [IsDomain A] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R)) (π : R)
    (a : Γ(Z, traitGenericOpen f π)) (x : Spec (.of A) ⟶ Z)
    (h : (⊤ : (Spec (.of (FractionRing A))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ x) ⁻¹ᵁ
        traitGenericOpen f π) : FractionRing A :=
  (ΓSpecIso (.of (FractionRing A))).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ x).appLE
      (traitGenericOpen f π) ⊤ h a)

/-- Equal vertical orders normalize a generic frame; a generic unit on an irreducible
nonempty special fibre has a unique normalization exponent, equal to every unramified
trait evaluation's normalized valuation.
Source: BLR 4.3, printed p.104 (PDF p.110).
(blueprint: lem-sfb-trait-line-section-order-normalization).

Proof:
1. DVR factorization (lem-weil-pbc-dvr-unit-times-uniformizer-power) identifies E
   with R[1/pi], the generic fibre with D(pi), and makes R regular.
2. On smooth affine charts, smooth-affine comparison and regular smooth ascent
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   lem-weil-pbc-regular-ring-smooth-ascent) give regular local rings. Smooth flatness
   and flat tensor injectivity (lem-weil-pbc-smooth-ring-map-flat,
   lem-trf-flat-tensor-preserves-injection) make pi a nonzerodivisor.
3. The fibre-stalk quotient and regularity of smooth fibres
   (lem-sbc-scheme-fibre-stalk-quotient, lem-weil-pbc-smooth-fibre-regular-local)
   give regular A and A/pi. Regular local rings are domains
   (lem-sc-regular-local-domain). Thus pi is prime and exactly one special component
   passes through each special point. Affine stalk localization
   (lem-weil-pbc-affine-open-stalk-localization) identifies its generic stalk with A_(pi).
4. Trivialize L Zariski locally (def-sc-invertible-module). Principal-open sections
   (lem-weil-pbc-spec-module-tilde-sections) express the generic frame and its inverse
   as b/pi^r and c/pi^t. Injectivity gives bc = pi^(r+t).
5. Induct on r+t: primality of pi and cancellation show b is a unit times pi^j.
   Hence the generic coefficient is a unit times pi^(j-r). Its order at the component
   is j-r = n, so the normalized germ is a unit at every special point.
6. Represent this unit germ and its inverse on a neighborhood, and shrink until the
   inverse identity and the denominator-cleared agreement with s hold as sections.
7. These local frames and the generic frame glue: differences vanish after inverting
   the nonzerodivisor pi. The same injectivity proves uniqueness among all global
   sections extending pi^(-n) s, not only among frames. If the special fibre
   is empty, D(pi) is all of Z, so every integer works, also for the empty scheme.
8. For a generic unit and a nonempty irreducible special fibre, DVR factorization at
   its unique generic point supplies a unique exponent m. Steps 1--7 give a global
   unit b. Any other exponent would differ by a nonzero power of a nonunit pi in
   this DVR, so cannot normalize to a unit.
9. Pull b back along x. It remains a unit of A, and a(x_E) = pi^m x*(b).
   The maximal-ideal adic valuation has additive normalization -WithZero.log;
   a uniformizer has value 1 and a unit has value 0, giving value m for either sign.
-/
theorem trait_line_section_order_normalization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (Z : Scheme.{u}) (f : Z ⟶ Spec (.of R))
    [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hstalk : ∀ z : traitSpecialFiber f,
      closure ({z} : Set (traitSpecialFiber f)) ∈ irreducibleComponents (traitSpecialFiber f) →
      ∃ hd : IsDomain (Z.presheaf.stalk (traitSpecialFiberι f z)),
        @IsDiscreteValuationRing (Z.presheaf.stalk (traitSpecialFiberι f z)) _ hd ∧
        Irreducible (Z.presheaf.germ ⊤ (traitSpecialFiberι f z) (by trivial)
          (traitUniformizerSection f π))) :
    (∀ (L : Z.Modules) [L.IsInvertible] (s : Γ(L, traitGenericOpen f π)),
      Modules.IsFreeGenerator s → ∀ n : ℤ,
      (∀ z : traitSpecialFiber f,
        closure ({z} : Set (traitSpecialFiber f)) ∈
          irreducibleComponents (traitSpecialFiber f) →
        TraitLineSectionHasOrder f π L s (traitSpecialFiberι f z) n) →
      ∃ t : Γ(L, ⊤), Modules.IsFreeGenerator t ∧
        TraitLineSectionNormalizedOn f π L s n ⊤ t ∧
        ∀ t' : Γ(L, ⊤), TraitLineSectionNormalizedOn f π L s n ⊤ t' → t' = t) ∧
    (IrreducibleSpace (traitSpecialFiber f) →
      ∀ a : Γ(Z, traitGenericOpen f π), IsUnit a →
      ∃ m : ℤ, TraitUnitNormalization f π a m ∧
        (∀ m' : ℤ, TraitUnitNormalization f π a m' → m' = m) ∧
        ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A],
          Irreducible (algebraMap R A π) →
          ∀ x : Spec (.of A) ⟶ Z,
            x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            ∃ h : (⊤ : (Spec (.of (FractionRing A))).Opens) ≤
                (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ x) ⁻¹ᵁ
                  traitGenericOpen f π,
              -WithZero.log ((IsDiscreteValuationRing.maximalIdeal A).valuation (FractionRing A)
                (traitGenericUnitValue f π a x h)) = m) := by
  sorry

end AlgebraicGeometry.Scheme
