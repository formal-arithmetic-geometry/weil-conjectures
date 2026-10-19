/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Topology.InverseImageStalk
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.Paper.StrictHenselizationFunctoriality

/-! # Strict-local fibres of pseudo-open immersions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XVII, Definition 5.2.1 and
proof of Proposition 5.2.2(a),(c), printed page 287
(blueprint: lem-per-pseudo-open-strict-local-fibre).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A pseudo-open immersion induces an isomorphism on pointed strict localizations,
and its strict-localization square is Cartesian. The second isomorphism is the
canonical comparison to the chosen fibre product. The sheaf map in the hypothesis
is exactly the inverse-image adjoint of the structure-sheaf map `f.c`.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XVII, Definition 5.2.1 and
proof of Proposition 5.2.2(a),(c), printed page 287
(blueprint: lem-per-pseudo-open-strict-local-fibre).

Proof:
1. The inverse-image stalk isomorphism of
`lem-weil-pbc-topological-inverse-image-stalk`, followed by the assumed sheaf
isomorphism, identifies the local rings at y and f(y). The adjunction-unit formula
on germs identifies this composite with the stalk map of f. Since the geometric
point downstairs is ybar followed by f, both residue embeddings in Ω agree under
this identification; their relative separable closures are the same subfield K.
2. Choose affine charts at these points. The stalk-localization theorem
`lem-weil-pbc-affine-open-stalk-localization` identifies their localized chart rings
with the local rings. Apply `lem-exc-affine-strict-local-ring-comparison` to identify
the geometric strict-local rings with algebraic strict henselizations relative to K.
Reindex the pointed-etale algebra diagrams along the local-ring isomorphism and its
inverse. Both operations preserve the underlying algebra and pointing. The colimit
universal property gives inverse maps of strict-local rings, preserving evaluation.
3. Taking Spec gives an isomorphism e over f. To verify the structural square, work
in the chosen affine charts: the affine adjunction
`lem-a1-locally-ringed-space-affine-adjunction` reduces equality to the equality of
ring maps supplied by the stalk-map formula in step 1 and the colimit maps in step 2.
Evaluation compatibility identifies the residue map with the identity of K.
Uniqueness in `lem-weil-pbc-strict-henselization-functoriality` identifies e with
`strictHenselizationMap f ybar`.
4. The hypotheses make f a monomorphism: equal composites into X have equal
underlying maps by injectivity, and their inverse-image sheaf maps agree by
cancelling the pulled-back structure-sheaf isomorphism. For a compatible pair
(a : T → Y, b : T → X_(xbar)), the unique lift is e⁻¹b. Its composite with j_Y is a
by cancellation of f, and its composite with e is b. This is precisely the
fibre-product universal property `def-pc-fibre-product`, so the canonical comparison
`pullback.lift` is an isomorphism. -/
theorem isIso_pseudoOpen_strictLocalFibre
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X)
    (htop : Topology.IsEmbedding f)
    (hsheaf : IsIso
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
        X.sheaf Y.sheaf).symm ⟨f.c⟩))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ybar : Spec (.of Ω) ⟶ Y) :
    IsIso (strictHenselizationMap f ybar) ∧
      IsIso (pullback.lift (f := f) (g := strictHenselizationStructuralMap (ybar ≫ f))
        (strictHenselizationStructuralMap ybar) (strictHenselizationMap f ybar)
        (strictHenselizationMap_over f ybar).symm) := by
  sorry

end AlgebraicGeometry.Scheme
