/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.BundleEndomorphismDerivedAdjunction
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.ShiftSaturatedIsoLocus
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Fully faithful derived tensor from a compact self-orthogonal bundle

Source: Stacks Project, dga.tex, Tag 09LZ, lemma-fully-faithful-in-compact-case,
degree-zero endomorphism specialization; perfect.tex, Tag 09M3
(blueprint: lem-sfb-compact-bundle-self-ext-full-faithfulness).

The functor `F` is specified by the left-derived universal property of the recorded
ordinary tensor. The adjunction is with the recorded right derived global Hom,
including its right endomorphism action. Its actual unit occurs in the conclusion.
Compactness is tested in D_QCoh, using the recorded coproduct construction.
-/

@[expose] public section

set_option autoImplicit false

universe u a w wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.BundleEndomorphism

/-- A compact finite locally free bundle without self-extensions in nonzero degrees gives a
fully faithful derived tensor functor, and the unit of its tensor-Hom adjunction is invertible.
The map `aX` encodes the A-scheme structure as in the recorded adjunction dependency.
The existential in `hcompact` only packages E[0] as an object of the full subcategory D_QCoh;
its compactness uses that category's canonical u-small coproducts. The parameters `F`, `eps`
and the left-derived property identify the specified total derived tensor, rather than an
arbitrary functor. The adjunction parameter retains the specified right derived Hom.
No generation hypothesis on E is imposed.
Source: Stacks Project, dga.tex, Tag 09LZ, lemma-fully-faithful-in-compact-case,
degree-zero specialization, with the quasi-coherent image supplied by perfect.tex, Tag 09M3
(blueprint: lem-sfb-compact-bundle-self-ext-full-faithfulness).

Proof:
1. Use lem-sfb-bundle-endomorphism-derived-adjunction to identify F(B) with E and
H^q(G(K)) with Hom(E,K[q]), respecting precomposition. Coproducts in the two categories are
provided by lem-pc-derived-module-direct-sums and lem-pc-derived-qcoh-direct-sums.
2. The regular right B-module is projective: lift a map along a surjection by lifting its value
at 1 and extending B-linearly. By lem-pc-ring-derived-map-representative, maps from B[0] to
K[q] in the derived category are cycles in K^q modulo boundaries, hence H^q(K), for unbounded K.
3. The formula and lem-pc-derived-module-homology-coproduct show B is compact. Vanishing of all
these groups makes K zero by lem-weil-pbc-unbounded-derived-iso-cohomology, so B weakly generates
in the sense of def-pc-generators; no target generation is required.
4. F preserves coproducts by adjunction. The cohomology map of the coproduct comparison for G
is precisely the compactness map for E, with shifts commuting with coproducts. It is bijective,
including its B-action. Apply lem-weil-pbc-unbounded-derived-iso-cohomology to show that G also
preserves coproducts.
5. The unit on B is induced by b mapping to j composed with b for a K-injective resolution
j:E to I. Its degree-zero cohomology is the canonical ordinary-to-derived endomorphism map,
a bijection by lem-weil-pbc-derived-single-fully-faithful. Every other degree is zero by the
self-Ext hypothesis. For B[n] the same calculation is shifted, so all these units are invertible.
6. By lem-sc-shift-saturated-iso-locus, the locus where every shifted unit is invertible is
closed under isomorphisms, triangles and coproducts. Use lem-pc-compact-generators-build-objects
for the singleton B: induction gives invertibility on its successive stages, and the telescope
triangle gives it on every object. Naturality of the inverses makes the unit a natural iso.
7. Adjunction and postcomposition with the inverse unit identify Hom(F(M),F(N)) with Hom(M,N).
Naturality of the unit shows that this identification inverts F.map, proving full faithfulness.
-/
theorem compact_bundle_self_ext_fullyFaithful
    (X : Scheme.{u}) (A : Type a) [CommRing A] (aX : A →+* Scalars X)
    [CompactSpace X] [QuasiSeparatedSpace X] (E : Modules X) [E.IsFiniteLocallyFree]
    [HasDerivedCategory.{w} (Modules X)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)]
    (hcompact : ∃ hE : schemeDerivedQCohProperty X (single X E),
      @IsCompactObject _ _ _ (derivedQCohDirectSums X) ⟨single X E, hE⟩)
    (hself : ∀ q : ℤ, q ≠ 0 → Subsingleton (single X E ⟶ (single X E)⟦q⟧))
    (F : DerivedCategory (ModuleCat.{u} (End E)ᵐᵒᵖ) ⥤ schemeDerivedQCohCategory X)
    (eps : DerivedCategory.Qh ⋙ (F ⋙ (schemeDerivedQCohProperty X).ι) ⟶
      (tensor X E).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [(F ⋙ (schemeDerivedQCohProperty X).ι).IsLeftDerivedFunctor eps
      (HomotopyCategory.quasiIso _ (.up ℤ))]
    (adj : F ⊣ qcHom X E) :
    F.Full ∧ F.Faithful ∧ IsIso adj.unit := by
  sorry

end AlgebraicGeometry.BundleEndomorphism
