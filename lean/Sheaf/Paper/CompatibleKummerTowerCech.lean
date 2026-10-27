/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FullParameterRootTower
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.UnitRootCoordinateTowerComparison
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Compatible punctured Kummer towers and their Čech coordinates

Source: ILO, Travaux de Gabber, IX Proposition 2.1, printed p.133, simultaneous
root presentation and rotations; the explicit CRT and inverse-limit calculation in
(blueprint: lem-sfb-compatible-kummer-tower-cech).

Finite and full rings are the existing `UnitRootCoordinates.view p t k none true`:
`k = some n` means the nth punctured root quotient; `k = none` means the punctured
compatible-root quotient. All arrows below are conclusions specified on coefficients
and root generators. In particular no torsor, action, or comparison is a hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open AlgebraicGeometry.Scheme.UniversalCover
open AlgebraicGeometry.ProEtale.UnitRootCoordinates
namespace AlgebraicGeometry.ProEtale.KummerCech

/-- Positive orders give nonzero finite residue moduli. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance orderNeZero {p : ℕ} (n : TameRootOrder p) : NeZero n.val :=
  ⟨Nat.ne_of_gt n.property.1⟩

/-- The finite label groups, or the existing product of q-adic groups at the full level.
The universe lift changes only the finite parameter index, not any coefficient universe.
Source: ILO IX 2.1, p.133, rotation coordinates
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
abbrev Label (p r : ℕ) (k : Option (TameRootOrder p)) : Type u :=
  match k with
  | some n => Multiplicative (ULift.{u} (Fin r) → ZMod n.val)
  | none => ParameterRootDeckGroup p (ULift.{u} (Fin r))

/-- Coordinatewise multiplication of labels. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelGroup (p r : ℕ) (k : Option (TameRootOrder p)) : Group (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Product topology on labels. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelTopology (p r : ℕ) (k : Option (TameRootOrder p)) :
    TopologicalSpace (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Compactness of finite labels and of the product of adic integers.
Source: the inverse-limit calculation following ILO IX 2.1
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelCompact (p r : ℕ) (k : Option (TameRootOrder p)) :
    CompactSpace (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Hausdorffness of the label product topology. Source: the ILO IX 2.1 limit calculation
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelT2 (p r : ℕ) (k : Option (TameRootOrder p)) :
    T2Space (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Total disconnectedness of finite labels and products of adic integers.
Source: the ILO IX 2.1 limit calculation
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelDisconnected (p r : ℕ) (k : Option (TameRootOrder p)) :
    TotallyDisconnectedSpace (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Continuous coordinatewise group operations. Source: the ILO IX 2.1 limit calculation
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
instance labelTopologicalGroup (p r : ℕ) (k : Option (TameRootOrder p)) :
    IsTopologicalGroup (Label.{u} p r k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- The reduction transition on finite rotation labels. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def reduction {p r : ℕ} (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    Profinite.of (Label.{u} p r (some m)) ⟶ Profinite.of (Label.{u} p r (some n)) :=
  CompHausLike.ofHom _ ⟨fun a ↦ Multiplicative.ofAdd
    (fun i ↦ ZMod.castHom h _ (a.toAdd i)), continuous_of_discreteTopology⟩

/-- The finite residue projection of the existing q-adic character data.
Source: the CRT residue construction following ILO IX 2.1
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def residueMap {p r : ℕ} {H : Type u} [CommRing H]
    (c : ParameterRootCharacters p (ULift.{u} (Fin r)) H) (n : TameRootOrder p) :
    Profinite.of (Label.{u} p r none) ⟶ Profinite.of (Label.{u} p r (some n)) :=
  CompHausLike.ofHom _ ⟨c.residue n, c.continuous_residue n⟩

/-- The exponent of a specified root for a finite or full rotation label.
Source: ILO IX 2.1, p.133, coordinate formula
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def exponent {p r : ℕ} {H : Type u} [CommRing H]
    (c : ParameterRootCharacters p (ULift.{u} (Fin r)) H)
    (k : Option (TameRootOrder p)) : Label.{u} p r k → labels p r k → ℕ :=
  match k with
  | some _ => fun a i ↦ (a.toAdd ⟨i⟩).val
  | none => fun g j ↦ ((c.residue j.2 g).toAdd ⟨j.1⟩).val

/-- The punctured finite or full scheme, using the existing actual quotient/localization.
Source: ILO IX 2.1, p.133 (blueprint: lem-sfb-compatible-kummer-tower-cech). -/
abbrev cover {p : ℕ} {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) : Scheme.{u} :=
  Spec (.of (view p t k none true))

/-- Projection to the first of two successive labels. Source: the triple-coordinate
calculation following ILO IX 2.1 (blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def firstLabel (P : Profinite.{u}) : Profinite.of (P × P) ⟶ P :=
  CompHausLike.ofHom _ ⟨Prod.fst, continuous_fst⟩

/-- Projection to the second successive label. Source: the triple-coordinate calculation
following ILO IX 2.1 (blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def secondLabel (P : Profinite.{u}) : Profinite.of (P × P) ⟶ P :=
  CompHausLike.ofHom _ ⟨Prod.snd, continuous_snd⟩

/-- The direct label of (x,gx,hgx) is hg. Source: the triple-coordinate calculation
following ILO IX 2.1 (blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def composedLabel (p r : ℕ) (k : Option (TameRootOrder p)) :
    Profinite.of (Label.{u} p r k × Label.{u} p r k) ⟶
      Profinite.of (Label.{u} p r k) :=
  CompHausLike.ofHom _ ⟨fun a ↦ a.2 * a.1, continuous_snd.mul continuous_fst⟩

/-- Send (x,g,h) to (gx,h) using the actual scheme action arrow a.
This uses both projections of the recorded profinite test object, so its label may vary.
Source: the triple-coordinate calculation following ILO IX 2.1
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
def nextVertex {X : Scheme.{u}} {P : Profinite.{u}}
    (a : profiniteProduct X P ⟶ X) :
    profiniteProduct X (Profinite.of (P × P)) ⟶ profiniteProduct X P :=
  pullback.lift (pullback.fst _ _ ≫ profiniteToScheme.map (secondLabel P))
    (profiniteProductMap (𝟙 X) (firstLabel P) ≫ a)
    (specULiftZIsTerminal.hom_ext _ _)

/-- Precisely the rotation, inverse-limit, comparison and triple-coordinate conclusions.
Maps are specified on every coefficient and every root; no arbitrary action is assumed.
The limit property quantifies over schemes, not just geometric points. The final triple
identity also allows varying labels on arbitrary test schemes.
Source: ILO IX 2.1, p.133, with the explicit CRT/limit supplement
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
structure Coordinates (p : ℕ) {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (ζ : TameRootOrder p → H) where
  characters : ParameterRootCharacters p (ULift.{u} (Fin r)) H
  roots_eq : characters.roots = ζ
  residueHomeo : Label.{u} p r none ≃ₜ
    {a : (n : TameRootOrder p) → Label.{u} p r (some n) //
      ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val), reduction n m h (a m) = a n}
  residue_eq : ∀ g n, (residueHomeo g).val n = characters.residue n g
  base : ∀ k, Localization.Away (∏ i, t i) →+* view p t k none true
  base_coeff : ∀ k a, base k (algebraMap H _ a) =
    viewMap p t k none true (algebraMap H _ a)
  transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    view p t (some n) none true →+* view p t (some m) none true
  transition_coeff : ∀ n m h a,
    transition n m h (viewMap p t (some n) none true (algebraMap H _ a)) =
      viewMap p t (some m) none true (algebraMap H _ a)
  transition_root : ∀ n m h i,
    transition n m h (viewMap p t (some n) none true (root p t (some n) i)) =
      viewMap p t (some m) none true (root p t (some m) i) ^ (m.val / n.val)
  transition_id : ∀ n, transition n n (dvd_refl n.val) = RingHom.id _
  transition_comp : ∀ n m l h₁ h₂,
    (transition m l h₂).comp (transition n m h₁) = transition n l (dvd_trans h₁ h₂)
  inclusion : ∀ n, view p t (some n) none true →+* view p t none none true
  inclusion_coeff : ∀ n a,
    inclusion n (viewMap p t (some n) none true (algebraMap H _ a)) =
      viewMap p t none none true (algebraMap H _ a)
  inclusion_root : ∀ n i,
    inclusion n (viewMap p t (some n) none true (root p t (some n) i)) =
      viewMap p t none none true (root p t none (i, n))
  inclusion_transition : ∀ n m h, (inclusion m).comp (transition n m h) = inclusion n
  inclusion_base : ∀ n, (inclusion n).comp (base (some n)) = base none
  limit : ∀ (Y : Scheme.{u}) (a : ∀ n, Y ⟶ cover t (some n)),
    (∀ n m h, a m ≫ Spec.map (CommRingCat.ofHom (transition n m h)) = a n) →
      ∃! f : Y ⟶ cover t none,
        ∀ n, f ≫ Spec.map (CommRingCat.ofHom (inclusion n)) = a n
  rotation : ∀ k, Label.{u} p r k → (view p t k none true →+* view p t k none true)
  rotation_coeff : ∀ k g a,
    rotation k g (viewMap p t k none true (algebraMap H _ a)) =
      viewMap p t k none true (algebraMap H _ a)
  rotation_root : ∀ k g j,
    rotation k g (viewMap p t k none true (root p t k j)) =
      viewMap p t k none true
        (algebraMap H _ (ζ (labelOrder p r k j) ^ exponent characters k g j) * root p t k j)
  rotation_one : ∀ k, rotation k 1 = RingHom.id _
  rotation_mul : ∀ k g h, rotation k (h * g) = (rotation k g).comp (rotation k h)
  rotation_transition : ∀ n m h g,
    (transition n m h).comp (rotation (some n) (reduction n m h g)) =
      (rotation (some m) g).comp (transition n m h)
  rotation_inclusion : ∀ n g,
    (inclusion n).comp (rotation (some n) (characters.residue n g)) =
      (rotation none g).comp (inclusion n)
  comparison : ∀ k,
    profiniteProduct (cover t k) (Profinite.of (Label.{u} p r k)) ≅
      pullback (Spec.map (CommRingCat.ofHom (base k)))
        (Spec.map (CommRingCat.ofHom (base k)))
  comparison_fst : ∀ k, (comparison k).hom ≫ pullback.fst _ _ =
    profiniteProductBase (cover t k) (Profinite.of (Label.{u} p r k))
  comparison_slice : ∀ k g,
    profiniteProductSection (cover t k) (Profinite.of (Label.{u} p r k)) g ≫
      (comparison k).hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (rotation k g))
  comparison_transition : ∀ n m h,
    profiniteProductMap (Spec.map (CommRingCat.ofHom (transition n m h))) (reduction n m h) ≫
        (comparison (some n)).hom ≫ pullback.snd _ _ =
      (comparison (some m)).hom ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (transition n m h))
  comparison_inclusion : ∀ n,
    profiniteProductMap (Spec.map (CommRingCat.ofHom (inclusion n))) (residueMap characters n) ≫
        (comparison (some n)).hom ≫ pullback.snd _ _ =
      (comparison none).hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (inclusion n))
  triple : ∀ k,
    nextVertex ((comparison k).hom ≫ pullback.snd _ _) ≫
        (comparison k).hom ≫ pullback.snd _ _ =
      profiniteProductMap (𝟙 (cover t k)) (composedLabel p r k) ≫
        (comparison k).hom ≫ pullback.snd _ _
  /-- The triple comparison with successive vertices (x,gx,hgx), at every level. -/
  tripleComparison : ∀ k,
    profiniteProduct (cover t k) (Profinite.of (Label.{u} p r k × Label.{u} p r k)) ≅
      pullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (base k)))
          (Spec.map (CommRingCat.ofHom (base k))))
        (pullback.fst (Spec.map (CommRingCat.ofHom (base k)))
          (Spec.map (CommRingCat.ofHom (base k))))
  /-- The first edge has vertices (x,gx). -/
  tripleComparison_fst : ∀ k, (tripleComparison k).hom ≫ pullback.fst _ _ =
    profiniteProductMap (𝟙 (cover t k)) (firstLabel (Profinite.of (Label.{u} p r k))) ≫
      (comparison k).hom
  /-- The second edge has vertices (gx,hgx), with the same varying labels. -/
  tripleComparison_snd : ∀ k, (tripleComparison k).hom ≫ pullback.snd _ _ =
    nextVertex ((comparison k).hom ≫ pullback.snd _ _) ≫ (comparison k).hom
  empty_base : r = 0 → ∀ k, Function.Bijective (base k)
  empty_group : r = 0 → Subsingleton (Label.{u} p r none)
  empty_comparison : r = 0 → ∀ k,
    (comparison k).hom ≫ pullback.snd _ _ =
      profiniteProductBase (cover t k) (Profinite.of (Label.{u} p r k))

/-- Naturality for the specified coefficient map and compatible unit-root substitution.
Both comparison projections, every root coordinate and every rotation are fixed explicitly.
Taking all units and their roots to be one is ordinary parameter-preserving base change.
Source: ILO IX 2.1, p.133, and the generator calculation in proof step 10
(blueprint: lem-sfb-compatible-kummer-tower-cech). -/
structure Substitution {p : ℕ} {H K : Type u} [CommRing H] [CommRing K] {r : ℕ}
    {t : Fin r → H} {s : Fin r → K} {ζ : TameRootOrder p → H} {η : TameRootOrder p → K}
    (D : Coordinates p t ζ) (E : Coordinates p s η) (φ : H →+* K)
    (v : Fin r → TameRootOrder p → K) where
  residue_eq : ∀ n g, D.characters.residue n g = E.characters.residue n g
  map : ∀ k, view p t k none true →+* view p s k none true
  map_coeff : ∀ k a, map k (viewMap p t k none true (algebraMap H _ a)) =
    viewMap p s k none true (algebraMap K _ (φ a))
  map_root : ∀ k j, map k (viewMap p t k none true (root p t k j)) =
    viewMap p s k none true
      (algebraMap K _ (v (labelIndex p r k j) (labelOrder p r k j)) * root p s k j)
  baseMap : Localization.Away (∏ i, t i) →+* Localization.Away (∏ i, s i)
  baseMap_coeff : ∀ a, baseMap (algebraMap H _ a) = algebraMap K _ (φ a)
  base_natural : ∀ k, (map k).comp (D.base k) = (E.base k).comp baseMap
  transition_natural : ∀ n m h,
    (map (some m)).comp (D.transition n m h) =
      (E.transition n m h).comp (map (some n))
  inclusion_natural : ∀ n,
    (map none).comp (D.inclusion n) = (E.inclusion n).comp (map (some n))
  rotation_natural : ∀ k g, (map k).comp (D.rotation k g) =
    (E.rotation k g).comp (map k)
  comparison_fst : ∀ k,
    profiniteProductMap (Spec.map (CommRingCat.ofHom (map k))) (𝟙 _) ≫
        (D.comparison k).hom ≫ pullback.fst _ _ =
      (E.comparison k).hom ≫ pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (map k))
  comparison_snd : ∀ k,
    profiniteProductMap (Spec.map (CommRingCat.ofHom (map k))) (𝟙 _) ≫
        (D.comparison k).hom ≫ pullback.snd _ _ =
      (E.comparison k).hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (map k))

/-- Compatible Kummer rotations give the finite and full Čech comparisons, with the
successive-label convention (x,gx,hgx), and naturality under compatible unit substitutions.
No nonzero-ring, nonempty-parameter or nonempty-puncture hypothesis is imposed.

Source: ILO, Travaux de Gabber, IX Proposition 2.1, printed p.133, simultaneous root
presentation; explicit CRT, residue, limit and substitution supplement
(blueprint: lem-sfb-compatible-kummer-tower-cech).

Proof:
1. If H is zero all punctured algebras are zero and every scheme diagram is unique.
   Otherwise put A=H[1/f]. Localization identifies the finite root algebra with
   A[x_i]/(x_i^n-t_i). Each t_i is a unit, with inverse the product of the other
   parameters divided by f; each root is a unit with inverse x_i^(n-1)/t_i.
   Positive orders prime to p are directed under divisibility by common multiples.
   These localization formulas also hold for zero punctured algebras
   [def-weil-ring-localization-away, def-weil-pbc-mv-polynomial-ring].
2. A compatible family of maps from localized finite stages is precisely a compatible
   family from the root quotients whose common image of f is invertible. The colimit
   and localization universal properties identify it with a map from the localized
   compatible-root quotient. Applying Spec identifies its scheme with the inverse
   limit [def-weil-pbc-category-colimit, lem-weil-pbc-spec-small-colimit-limit].
3. Evaluation x_i ↦ ζ_n^(a_i)x_i preserves the root relations, is independent of residue
   representatives, and has inverse label -a. Composition gives the action law.
   The compatibility ζ_m^(m/n)=ζ_n intertwines rotations with every power transition.
   The compatible-root presentation gives the full rotation on all labelled generators
   [def-weil-pbc-mv-polynomial-ring, def-weil-affine-spectrum].
4. Divide T^n-1 successively by the monic factors T-ζ_n^a. At every next root, the
   other evaluated factors are units by the unit-difference hypothesis, so the
   remaining quotient vanishes. Monicity gives the final quotient 1. These linear
   ideals are pairwise comaximal; CRT gives the product of copies of the coefficient
   ring. This argument includes rings with zero divisors and the zero ring
   [lem-pc-crt-ideal-quotient-product].
5. The affine self-product ring is B_n tensor_A B_n, presented by new roots y_i.
   The substitution z_i=y_i/x_i, with inverse y_i=x_i*z_i, changes its relations to
   z_i^n=1. Iterated CRT gives b tensor c ↦ (b*r_a(c))_a. The finite affine coproduct
   comparison identifies this with precisely (x,a) ↦ (x,ax), on both projections
   [lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-finite-affine-coproduct-spectrum].
6. CRT reconstructs each residue modulo n from the finitely many q-adic residues at
   q^v_q(n). Conversely the compatible q-power residues determine a unique adic
   integer by PadicInt.lift. Separation and CRT uniqueness make the maps inverse.
   Residue cylinders are open by the adic norm criterion, and agreement modulo q^b
   bounds the norm of the difference by q^(-b), proving continuity both ways.
   Integral vectors have their ordinary residues; modulus 1 is a singleton
   [lem-pc-crt-ideal-quotient-product, lem-exc-padic-residue-universal-property].
7. Any map from the compact profinite group to a finite discrete set is constant on
   sufficiently small residue cylinders. A finite cylinder cover and a common
   multiple of its levels show that it factors through some finite label group.
   These residue maps are surjective. Finite products commute with this filtered
   ring colimit: choose one common stage for finitely many entries, or finitely
   many equalities. Thus the recorded X[G] is the limit of the finite labelled
   copies of X [def-sfb-profinite-test-objects,
   lem-pc-filtered-colimit-commrings-elementwise,
   lem-weil-pbc-finite-affine-coproduct-spectrum].
8. Finite comparisons commute with power transitions by the root formula in step 3.
   For the double diagram of finite labels and finite root stages, common multiples
   make its diagonal cofinal: a cone at any pair of levels is recovered from a
   common upper level, independently after a further common upper level. The limit
   of the self-products is the self-product of the limit, by its two-projection
   universal property. Taking the compatible finite isomorphisms and their inverses
   gives the specified full comparison. Action identities follow after every finite
   projection [def-pc-fibre-product, def-sfb-profinite-test-objects].
9. The second successive vertex is gx and the third is h(gx)=(hg)x. At every finite
   root coordinate this is ζ_n^b*ζ_n^a*x_i=ζ_n^(b+a)*x_i. Apply the limit projections
   to obtain the same identity on X[G×G], including varying labels on arbitrary
   test schemes. This proves the triple identity as an equality of scheme maps
   [def-pc-fibre-product, def-sfb-profinite-test-objects]. The triple fibre product
   is the pullback of the two double fibre products along the second and first
   vertex projections. Pull back the double comparison on both factors. Its domain
   is X[G] times_X X[G], using the action on the left and first vertex on the right.
   The profinite test-object construction identifies this with X[G×G]: on finite
   label quotients it is the disjoint union indexed by pairs, and these product
   quotients are cofinal by the cylinder argument of step 7. This yields the triple
   isomorphism, whose two edge projections are (x,gx) and (gx,hgx).
10. Under φ(t_i)=u_i*s_i, substitute x_i ↦ v_(i,n)*x'_i. Its nth power is u_i*s_i,
    and the image of f is a product of units times the target boundary product,
    so the substitution extends to the puncture. Compatibility of v makes it commute
    with divisibility transitions. Preservation of ζ makes it commute with rotations,
    on coefficients and roots. The finite comparison squares commute on both
    projections; pass to the limit for the full square and every rotation coordinate.
    With u=v=1 these are ordinary base changes [def-weil-pbc-mv-polynomial-ring,
    def-weil-ring-localization-away, def-weil-affine-spectrum,
    def-pc-fibre-product, def-sfb-profinite-test-objects].
11. If r=0 all presentations are H, f=1, and all power maps are identities. Finite
    and full groups are singletons. Both comparison projections are the same
    structural projection, hence the comparison is the identity under the canonical
    singleton and self-product identifications. Substitutions and triples reduce
    to identities.
-/
theorem compatible_kummer_tower_cech (p : ℕ) (hp : p.Prime)
    {H : Type u} [CommRing H] [CharP H p] (r : ℕ) (t : Fin r → H)
    (ζ : TameRootOrder p → H) (hζ : ∀ n, IsPrimitiveRoot (ζ n) n.val)
    (hcompat : ∀ (n m : TameRootOrder p), n.val ∣ m.val → ζ m ^ (m.val / n.val) = ζ n)
    (hunit : ∀ (n : TameRootOrder p) (a b : ZMod n.val), a ≠ b →
      IsUnit (ζ n ^ a.val - ζ n ^ b.val)) :
    ∃ D : Coordinates p t ζ,
      ∀ (K : Type u) [CommRing K] [CharP K p] (s : Fin r → K)
        (η : TameRootOrder p → K) (_hη : ∀ n, IsPrimitiveRoot (η n) n.val)
        (_hcompat : ∀ (n m : TameRootOrder p), n.val ∣ m.val → η m ^ (m.val / n.val) = η n)
        (_hunit : ∀ (n : TameRootOrder p) (a b : ZMod n.val), a ≠ b →
          IsUnit (η n ^ a.val - η n ^ b.val))
        (φ : H →+* K) (_hroots : ∀ n, φ (ζ n) = η n)
        (unit : Fin r → Kˣ) (v : Fin r → TameRootOrder p → K)
        (_ht : ∀ i, φ (t i) = (unit i : K) * s i)
        (_hv : ∀ i n, v i n ^ n.val = (unit i : K))
        (_hvcompat : ∀ i (n m : TameRootOrder p), n.val ∣ m.val →
          v i m ^ (m.val / n.val) = v i n)
        (E : Coordinates p s η), Nonempty (Substitution D E φ v) := by
  sorry

end AlgebraicGeometry.ProEtale.KummerCech
