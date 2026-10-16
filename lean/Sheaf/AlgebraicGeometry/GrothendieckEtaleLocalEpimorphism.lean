/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # Local lifting families for general Grothendieck coefficients

Source: the local epimorphism argument for sheaves, Stacks Project, Tags 00WL and 01H0.
The categorical formulation below is an agent-written coefficient generalization.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Maps admitting local lifts through a sheaf epimorphism jointly detect zero maps.
Source: Stacks Project, Sites, Tag 00WL, the image subsheaf argument, and
Hypercoverings, Tag 01H0, the local primitive step. This is the categorical
finite-cover version for Grothendieck abelian coefficients.
(blueprint: lem-weil-pbc-grothendieck-etale-local-epimorphism).

Proof: restrict to the qcqs etale basis. It has finite covering families and is
stable under the finite fiber products used in their matching diagrams.
Restriction to this basis is an equivalence of sheaf categories, so p remains
epic there. Let Q be the pointwise image of p, viewed as a subpresheaf of G.
For a finite cover
C = (Wᵢ → W), define L_C as the inverse image in G(W) of the subobject
∏ Q(Wᵢ) of ∏ G(Wᵢ). Refining a cover enlarges L_C, and common refinements make
these subobjects a directed family. Use the poset of distinct subobjects L_C,
which is small by well-poweredness, as the filtered index; no filteredness of
the raw category of covering maps is required. Set L(W) equal to their union.
Restriction maps carry L_C into the analogous subobject for the pulled-back
cover, so L is a subpresheaf of G. To check its sheaf condition on a fixed finite basis cover
(Wᵢ → W), write its matching object as the kernel of the difference
of the two restriction maps from ∏ L(Wᵢ) to the finite product of G on the
overlaps. This uses monicity of L → G. AB5 expresses this kernel as the filtered colimit
of the analogous
kernels with L(Wᵢ) replaced by L_{Cᵢ}(Wᵢ), for finite tuples of covers Cᵢ.
For each such tuple, glue in G and compose the finite covers Cᵢ with Wᵢ → W.
The glued map then factors through L_C(W) for this composite cover C, by the
defining pullback of L_C. These maps induce the inverse of the matching map
for L by the colimit universal property. Uniqueness follows from monicity.
This is an equality of subobjects; no compactness or projectivity of an
arbitrary source B is used to factor a map through one stage of a union.
The resulting subsheaf L of G contains the image of p. Since p is epic,
L → G is both monic and epic; thus L(W) = G(W).

Pull this filtered union back along x : B → G(W). AB5, or exactness of
filtered colimits applied to the defining pullback kernels, shows that the
subobjects B_C = B ×_{G(W)} L_C have union B. Over B_C form
P_C = B_C ×_{∏ Q(Wᵢ)} ∏ F(Wᵢ). Finite products of the image epimorphisms
F(Wᵢ) → Q(Wᵢ) are epic, and epis are stable under pullback in an abelian
category, so P_C → B_C is epic. The composite π_C : P_C → B admits the
specified local lifts on C. The same lifts extend to every arrow of its
generated covering sieve by restriction; choose one factorization for each
such arrow, with no compatibility requirement. The hypothesis gives
π_C ≫ g = 0. Cancel P_C → B_C to obtain B_C.arrow ≫ g = 0 for every C.
Since the filtered union of B_C is B, g = 0. This proof uses filtered unions,
not pullback stability of an arbitrary jointly epic family. When W is empty,
G(W) is terminal, and the zero lifts on the empty covering sieve test the
identity map of B. Zero coefficients or a zero source are included. -/
theorem eq_zero_of_locally_liftable_maps
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0 := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
