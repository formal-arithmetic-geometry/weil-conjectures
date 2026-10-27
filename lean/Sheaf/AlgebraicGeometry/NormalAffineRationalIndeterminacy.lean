module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection
import Sheaf.RingTheory.ReflexiveHeightOneIntersection

/-!
# Indeterminacy of an affine-target rational map on a normal scheme

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.4 Lemma 2, printed p.109
(scan PDF p.115); Stacks Project, Tag 031T(2).
(blueprint: lem-sfb-normal-affine-rational-indeterminacy)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The maximal extension to an affine target exists uniquely, and each irreducible component
of its indeterminacy locus has a generic point with one-dimensional local ring.

Source: BLR, Néron Models, §4.4 Lemma 2, printed p.109 (scan PDF p.115), using
Stacks Project, Tag 031T(2).
(blueprint: lem-sfb-normal-affine-rational-indeterminacy)

The binder `hE` specifies the union in the node, rather than assuming any extension on it.
The existential inclusion `i` in the first conclusion expresses that restricting the glued
morphism to each extension open is defined. Components are taken in the closed subspace
`W ∖ E`; their images in `W` are the closed subsets whose generic points are asserted.

Proof:
1. Let η be the generic point and K its stalk. By
   `lem-sc-integral-scheme-stalks-in-function-field`, every nonempty open contains η and
   sections inject into K. The affine adjunction
   `lem-a1-locally-ringed-space-affine-adjunction` sends h to a ring map A → K. Every
   extension has this generic map, so injectivity makes extensions agree on overlaps.
   Empty overlaps have a unique map. Apply `lem-weil-pbc-scheme-morphism-gluing` to obtain
   the unique h_E. The open D itself occurs in the union, so h_E restricts to h on D.
2. By `lem-sc-noetherian-closed-subset-finite-components`, the closed complement has
   finitely many components. For one component C take its generic point ξ using
   `lem-sc-scheme-sober`. It lies in no other component. Choose an affine neighbourhood
   U of ξ avoiding all other components. Write R = Γ(U, O_W) and p for the prime of ξ.
   Then the complement in U is V(p), and `lem-weil-pbc-affine-open-stalk-localization`
   identifies the stalk at ξ with R_p.
3. Integrality makes R a domain, `pqf-lem-affine-open-locnoeth` makes it Noetherian,
   and `lem-sc-integral-function-field-affine-fraction` identifies its fraction field with K.
   To see integral closedness, an integral fraction a/b is a section on the dense principal
   open D(b) by `lem-weil-pbc-affine-open-section-vanishing-prime`. Apply
   `lem-sbc-normal-dense-open-integral-section` to extend it to R, with the same generic germ.
4. Apply `lem-per-reflexive-height-one-intersection-criterion` to M = R. Evaluation
   identifies R with its bidual (both dual identifications evaluate at 1), and R is finite
   and torsion free. Thus R is the intersection of its height-one local rings inside K,
   including the empty-intersection convention. This is Tag 031T(2).
5. The prime p is nonzero since η belongs to D and hence to E. If a nonzero prime lay
   strictly below p, no height-one prime q could contain p. Every such q would therefore
   lie in E. The germ of each coordinate h_E*(a) there, and
   `lem-weil-pbc-affine-open-stalk-localization`, put its generic value in R_q.
   Step 4 puts all coordinate values in R.
6. Injectivity R → K makes these coordinate preimages a ring map A → R. The affine
   adjunction gives a map U → Spec A, which agrees with h on U ∩ D by generic-germ
   injectivity. Hence U occurs in E, contradicting ξ outside E. There is no nonzero prime
   strictly below p; since p is nonzero, its height is one.
   `lem-weil-pbc-localization-dimension-chains-below-prime` and the stalk identification
   give the required dimension. If the complement is empty there are no components. -/
theorem existsUnique_affine_extension_and_indeterminacy_dim_one
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (_hnormal : ∀ x : W, IsDomain (W.presheaf.stalk x) ∧
      IsIntegrallyClosed (W.presheaf.stalk x))
    (A : Type u) [CommRing A]
    (D : W.Opens) (_hD : Dense (D : Set W))
    (h : D.toScheme ⟶ Spec (CommRingCat.of A))
    (E : W.Opens)
    (_hE : E = sSup {V : W.Opens | ∃ hV : V.toScheme ⟶ Spec (CommRingCat.of A),
      W.homOfLE (inf_le_left : V ⊓ D ≤ V) ≫ hV =
        W.homOfLE (inf_le_right : V ⊓ D ≤ D) ≫ h}) :
    (∃! hE : E.toScheme ⟶ Spec (CommRingCat.of A),
      ∀ (V : W.Opens) (hV : V.toScheme ⟶ Spec (CommRingCat.of A)),
        W.homOfLE (inf_le_left : V ⊓ D ≤ V) ≫ hV =
          W.homOfLE (inf_le_right : V ⊓ D ≤ D) ≫ h →
        ∃ i : V ≤ E, W.homOfLE i ≫ hE = hV) ∧
    ∀ C ∈ irreducibleComponents {x : W // x ∉ E},
      ∃ ξ : W, IsGenericPoint ξ (Subtype.val '' C) ∧
        ringKrullDim (W.presheaf.stalk ξ) = 1 := by
  sorry

end AlgebraicGeometry.Scheme
