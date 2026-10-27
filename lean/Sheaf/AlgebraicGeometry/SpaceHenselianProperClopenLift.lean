/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent

/-! # Lifting a proper clopen fibre part over a henselian pair

Source: Stacks Project, More on Morphisms of Spaces, Tag 0CWI,
lemma-split-off-proper-part-henselian
(blueprint: lem-sfb-space-henselian-proper-clopen-lift).

Clopen subspaces are presented by morphisms representable by both open and closed
immersions. The open-immersion condition retains the restricted structure sheaf.
The conclusion identifies subspaces by a pullback square, including their inclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual quotient-spectrum inclusion, regarded as a map of algebraic spaces over A.
Source: Stacks Project, Tag 0CWI, the map Spec(A/I) → Spec(A)
(blueprint: lem-sfb-space-henselian-proper-clopen-lift). -/
def henselianPairClosedFibreBaseMap {A : Type u} [CommRing A] (I : Ideal A) :
    schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶
      schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over (Spec (CommRingCat.of A))).yoneda.map
    (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))))

/-- The second projection of Spec(A/I) ×_Spec(A) X, the closed-fibre inclusion into X.
The fibre product is the existing sheaf fibre product bundled by `enlargedFibreProduct`.
Source: Stacks Project, Tag 0CWI, definition of X_0
(blueprint: lem-sfb-space-henselian-proper-clopen-lift). -/
def henselianPairClosedFibreInclusion {A : Type u} [CommRing A] (I : Ideal A)
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    enlargedFibreProduct (henselianPairClosedFibreBaseMap I) f ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.snd (henselianPairClosedFibreBaseMap I).hom f.hom)

/-- A proper clopen subspace of the closed fibre lifts to a proper clopen subspace.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0CWI,
lemma-split-off-proper-part-henselian
(blueprint: lem-sfb-space-henselian-proper-clopen-lift).

Proof, following the seven steps of the node:
1. Choose a universally surjective proper scheme cover X' → X by weak Chow
   [lem-sfb-space-weak-chow]. Composition preserves separatedness and finite type
   [lem-sfb-space-separated-fp-composition, lem-sfb-space-finite-type-composition];
   chartwise finite type agrees with scheme finite type
   [lem-sfb-space-local-properties-chart-test]. Thus X' is separated of finite type over A.
2. Pull back Z to a clopen subscheme Z' of X'_0. Proper base change and composition
   [lem-sfb-space-proper-base-change, lem-sfb-space-proper-composition] make Z' proper.
   Apply the scheme lifting theorem [lem-sfb-scheme-henselian-proper-clopen-lift] to
   obtain a proper clopen W' in X' with closed fibre Z'.
3. The images Q1 of W' and Q2 of its complement in X are closed and cover X.
   In W', the inverse image of Q2 is closed. Its image in Spec(A) is closed because
   W' is proper, and is exactly the image of Q1 ∩ Q2.
4. If that intersection were nonempty, the closed image would meet V(I) by
   [lem-weil-pbc-henselian-pair-prime-connected]. The fibre-product point-image
   formula [lem-a1-space-point-open-calculus] would then give a closed-fibre point
   with lifts in both W'_0 and its complement. The closed-fibre inclusion is a
   monomorphism, hence injective on field-valued point classes
   [def-a1-space-point-topology]. These lifts would lie over both Z and its complement,
   a contradiction. Therefore Q1 and Q2 are disjoint and both clopen.
5. Realize Q1 by an open subspace W: pull it back to a scheme atlas and descend the
   invariant open using [lem-trf-etale-open-chart-morphism-descent]. Its complement
   is open as well. On every scheme test the inclusion has the restricted structure
   sheaf and is also a closed immersion [def-weil-closed-immersion].
6. The inverse image of W in X' is W', so W' → W is universally surjective
   [lem-a1-space-point-open-calculus]. After any base change, a closed subset of W
   has the same image as its closed inverse image in the proper W'. Its image is
   therefore closed [lem-sfb-space-proper-base-change]. The closed inclusion W → X
   is proper [lem-sfb-space-closed-subspace-proper]; composition gives separatedness
   and finite type for W over A. Together these prove properness.
7. After closed-fibre base change the two open subspaces W_0 and Z have identical
   inverse images Z' along the surjective cover X'_0 → X_0. Point-image calculus
   detects their equality as open subfunctors, hence with their restricted structure
   sheaves [lem-a1-space-point-open-calculus]. This gives the displayed pullback square.
-/
theorem exists_proper_clopen_lift_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (hsep : MapIsSeparated f) (hft : MapIsFiniteType f)
    (Z : AlgebraicSpace (Spec (CommRingCat.of A)))
    (i : Z ⟶ enlargedFibreProduct (henselianPairClosedFibreBaseMap I) f)
    (hopen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) i.hom.hom)
    (hclosed : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hproper : MapIsProper (i ≫ enlargedFibreProductFst (henselianPairClosedFibreBaseMap I) f)) :
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (w : W ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) w.hom.hom ∧
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) w.hom.hom ∧
      MapIsProper (w ≫ f) ∧
      ∃ l : Z ⟶ W, IsPullback l i w (henselianPairClosedFibreInclusion I f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
