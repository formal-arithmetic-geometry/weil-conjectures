module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.TraceFormula.SmoothComponentPureTranscendental
import Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange

/-!
# Components of a smooth self-product

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Lemma 4.3(i)-(ii),
March 31, 2026 version, printed p.10; Stacks Project, Tags 0357, 057K, 0556.
(blueprint: lem-sfb-smooth-self-product-component-rank)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The number of geometric irreducible components over a point. At the generic point
of an integral base this is the geometric generic component count rho. The extended natural
value retains infinite counts; the theorem below asserts a positive finite value.

Source: Guo, Lemma 4.3, notation immediately preceding the lemma, printed p.10.
(blueprint: lem-sfb-smooth-self-product-component-rank) -/
noncomputable def Scheme.Hom.geometricComponentRankAt {Z T : Scheme.{u}}
    (t : Z ⟶ T) (x : T) : ℕ∞ :=
  ENat.card (irreducibleComponents
    ↥(pullback t (Spec.map (CommRingCat.ofHom
      (algebraMap (T.residueField x) (AlgebraicClosure (T.residueField x)))) ≫
        T.fromSpecResidueField x)))

/-- The diagonal component of a smooth integral self-product has geometrically integral
generic fibre. Its geometric generic component count is one; the other components have
strictly smaller positive counts. These properties persist over every nonempty affine
open of the first factor, with the same section and the same counts.

Source: Guo, Lemma 4.3(i)-(ii), with both factors Y and g = id; printed p.10.
(blueprint: lem-sfb-smooth-self-product-component-rank)

Proof:
1. Base change preserves smoothness, separatedness and finite type
(lem-pc-proper-base-change, lem-pod-separated-finite-type-base-change). Finite type over
Noetherian schemes is Noetherian (lem-weil-pbc-finite-type-over-noetherian), and smooth
morphisms preserve normality (lem-sfb-smooth-normal-ascent). Apply
lem-sfb-normal-locally-finite-components using the finiteness of Noetherian components
(lem-weil-pbc-noetherian-finite-components and its open-subscheme version) to W.
2. Each clopen inclusion is both open and closed. Restriction preserves smoothness
(lem-weil-pbc-smooth-restrict-open-subschemes). Closed immersions are finite type
(lem-weil-pbc-closed-immersion-proper); composition preserves finite type
(lem-sfb-finite-type-composition-base-change). The restricted diagonal is a base change
of the closed diagonal (lem-weil-pbc-closed-immersion-base-change), so is closed.
3. Smooth maps are flat and locally finitely presented (lem-pc-smooth-flat), hence open
(lem-weil-pbc-flat-lfp-open). A nonempty open image in an integral target is dense and
contains its generic point. This proves dominance without surjectivity.
4. Each component's generic fibre is nonempty and irreducible: two nonempty fibre opens
lift to opens in the integral component; their intersection is nonempty and its open
image contains the target generic point. Use the subspace topology of def-pc-scheme-fibre.
5. The irreducible image of the diagonal lies in exactly one clopen component. Factor
through it by lem-weil-pbc-morphism-factors-through-open-subscheme. The pullback identities
make this factor a section, hence give a rational point in its connected generic fibre.
6. Apply lem-trf-smooth-component-pure-transcendental to this rational point (the residue
extension has zero transcendence variables). The component's generic fibre is geometrically
integral, and its geometric count is one.
7. All geometric generic fibres are finite type over fields, hence Noetherian. They are
nonempty by dominance and lem-sfb-field-extension-irreducible-components. The component
covering lemma lem-sc-irreducible-components-cover and Noetherian finiteness make every
count positive and finite.
8. Apply lem-trf-geometric-fibre-component-count-base-change to f and Y to identify the
count of W over the generic point of Y with N. The finite clopen partition remains a
partition after base change (lem-weil-pbc-open-fibre-product). Every irreducible component
lies in one piece, so counts sum to N. Subtract the diagonal summand one to bound the rest.
9. Over a nonempty affine open B, lem-weil-pbc-open-fibre-product identifies the pullback
with the inverse-image open in each component. Dominance makes it nonempty. Normality and
integrality restrict to nonempty opens; smoothness, separatedness and finite type are
preserved by base change. The generic point lies in B with unchanged residue field, so
the generic counts agree. Base change of the diagonal section supplies its restriction. -/
theorem smooth_self_product_component_rank {S Y : Scheme.{u}}
    [IsAffine S] [IsNoetherian S] [IsIntegral S] [IsIntegral Y]
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x))
    (f : Y ⟶ S) [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (_hη : IsGenericPoint η Set.univ)
    (ξ : Y) (_hξ : IsGenericPoint ξ Set.univ) :
    ∃ N : ℕ, 0 < N ∧ f.geometricComponentRankAt η = (N : ℕ∞) ∧
      IsNoetherian (pullback f f) ∧
      (∀ w : ↥(pullback f f), IsDomain ((pullback f f).presheaf.stalk w) ∧
        IsIntegrallyClosed ((pullback f f).presheaf.stalk w)) ∧
      ∃ (m : ℕ) (U : Fin (m + 1) → (pullback f f).Opens),
        Set.range (fun i ↦ (U i : Set ↥(pullback f f))) =
          irreducibleComponents ↥(pullback f f) ∧
        (∀ i, IsClosed (U i : Set ↥(pullback f f)) ∧ IsIntegral (U i).toScheme ∧
          (∀ z : (U i).toScheme, IsDomain ((U i).toScheme.presheaf.stalk z) ∧
            IsIntegrallyClosed ((U i).toScheme.presheaf.stalk z))) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ i, U i) = ⊤ ∧
        (∀ i, Set.range (pullback.diagonal f) ⊆ (U i : Set ↥(pullback f f)) ↔ i = 0) ∧
        (∀ i, Smooth ((U i).ι ≫ pullback.fst f f) ∧
          IsSeparated ((U i).ι ≫ pullback.fst f f) ∧
          LocallyOfFiniteType ((U i).ι ≫ pullback.fst f f) ∧
          QuasiCompact ((U i).ι ≫ pullback.fst f f) ∧
          DenseRange ((U i).ι ≫ pullback.fst f f)) ∧
        ((U 0).ι ≫ pullback.fst f f).geometricComponentRankAt ξ = 1 ∧
        (∑ i, ((U i).ι ≫ pullback.fst f f).geometricComponentRankAt ξ) = (N : ℕ∞) ∧
        (∀ i, i ≠ 0 → 1 ≤ ((U i).ι ≫ pullback.fst f f).geometricComponentRankAt ξ ∧
          ((U i).ι ≫ pullback.fst f f).geometricComponentRankAt ξ < (N : ℕ∞)) ∧
        GeometricallyIntegral
          (pullback.snd ((U 0).ι ≫ pullback.fst f f) (Y.fromSpecResidueField ξ)) ∧
        ∃ s : Y ⟶ (U 0).toScheme,
          s ≫ (U 0).ι = pullback.diagonal f ∧
          s ≫ (U 0).ι ≫ pullback.fst f f = 𝟙 Y ∧
          ∀ (B : Y.Opens), Nonempty B → IsAffineOpen B →
            ∃ b : B.toScheme, B.ι b = ξ ∧
              (∀ i, IsIntegral (pullback ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                (∀ z : ↥(pullback ((U i).ι ≫ pullback.fst f f) B.ι),
                  IsDomain
                    ((pullback ((U i).ι ≫ pullback.fst f f) B.ι).presheaf.stalk z) ∧
                  IsIntegrallyClosed
                    ((pullback ((U i).ι ≫ pullback.fst f f) B.ι).presheaf.stalk z)) ∧
                IsOpenImmersion (pullback.fst ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                Smooth (pullback.snd ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                IsSeparated (pullback.snd ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                LocallyOfFiniteType (pullback.snd ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                QuasiCompact (pullback.snd ((U i).ι ≫ pullback.fst f f) B.ι) ∧
                (pullback.snd ((U i).ι ≫ pullback.fst f f) B.ι).geometricComponentRankAt b =
                  ((U i).ι ≫ pullback.fst f f).geometricComponentRankAt ξ) ∧
              ∃ sB : B.toScheme ⟶ pullback ((U 0).ι ≫ pullback.fst f f) B.ι,
                sB ≫ pullback.snd ((U 0).ι ≫ pullback.fst f f) B.ι = 𝟙 B.toScheme ∧
                sB ≫ pullback.fst ((U 0).ι ≫ pullback.fst f f) B.ι = B.ι ≫ s := by
  sorry

end AlgebraicGeometry
