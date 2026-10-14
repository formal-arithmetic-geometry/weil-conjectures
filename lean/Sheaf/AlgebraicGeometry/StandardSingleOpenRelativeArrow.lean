/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Sheaf.AlgebraicGeometry.RelativeMVMaps
import Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceIso

/-! # Identifying a relative open arrow for a single coefficient -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restricting a single coefficient to an open contained in its domain gives the
literal tensor-pullback standard comparison, as an isomorphism of arrows.
Source: Stacks Project, Tags 08HY, 0D5S, 01JR and 0A1D.
(blueprint: lem-pc-standard-single-open-relative-arrow).

Proof: The open scheme of W inverse image Z is canonically isomorphic to Z,
with its inclusion into W identified with homOfLE hZ. On the cartesian base
changes use the projection-preserving pullback isomorphism for this scheme
isomorphism and for associating the two pullbacks. Exact open restriction
identifies derived pullback of N[0] with the single complex of the literal tensor
pullback of N; the comparison is the derived-to-ordinary pullback counit. Use
these coefficient comparisons, direct-image composition, and pullback along g
to construct the source and target vertex isomorphisms. Expand relativeMVLocalArrow
and standardSingleBaseChangeMap into their base-change mates and single-complex
counits. The composition law for picardTermwiseSingleMap, the compatibility of
source-isomorphism base-change conjugacy, and the composite-adjunction counit formula
identify the two composites. This is the commuting square defining an arrow
isomorphism; each vertex map is invertible by exact open restriction and scheme
isomorphism transport. More explicitly, put J = W inverse image Z, i:J -> W,
X' = W times_B A with projections q:X' -> W and f':X' -> A, and
J' = X' times_W J with projections r:J' -> X' and k:J' -> J. Let
P = Z times_B A. The source isomorphism e:J -> Z is isoOfLE hZ. The two
projections define e':J' -> P; the inverse is obtained by first lifting into X'
and then into J'. The projection equations and pullback extensionality prove
both inverse identities and k;e = e';(P -> Z).

Write L and R for the pinned derived functors. Let c(h,t) compare successive
pullback along t then h with pullback along h;t.
Put M = tensorPullbackObj (Y.homOfLE hZ) N. Exactness of open restriction,
followed by tensor-pullback composition, gives
alpha:L_e(M[0]) -> L_i(N[0]) as an isomorphism. On J' the same construction
and the equality r;q = k;i give an isomorphism
beta:L_e'((P -> Z tensor-pullback M)[0]) -> L_r((q tensor-pullback N)[0]).
To check the coefficient compatibility required by exists_derivedBaseChange_source_iso,
expand the local coefficient as c(k,i), transport across k;i = r;q, inverse
c(r,q), and L_r(picardTermwiseSingleMap q N). Apply the single-map composition
identity once on each path. The tensor-composition factors are precisely those
used in alpha and beta, so cancellation and naturality give that compatibility.
Apply source-isomorphism conjugacy with these alpha and beta, and invert its
arrow isomorphism to orient it from the local arrow to the standard arrow.
The vertex isomorphisms use the invertible derived adjunction units for e and e';
their inverse identities follow from the adjunction triangle identities.
No assertion about invertibility of a base-change map is used.
Empty Z or W and zero N give the same comparison between zero objects;
Z = W gives the identity-open comparison. -/
theorem standardSingle_open_relative_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B)
    (W Z : Y.Opens) (hZ : Z ≤ W) (N : W.toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let f := W.ι ≫ p
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
    Nonempty
      (relativeMVLocalArrow f (pullback.snd f g) g (pullback.fst f g)
          (IsPullback.of_hasPullback f g) K K'
          (Scheme.picardTermwiseSingleMap (pullback.fst f g) N) (W.ι ⁻¹ᵁ Z) ≅
        Arrow.mk (standardSingleBaseChangeMap (Z.ι ≫ p)
          (Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N) g)) := by sorry

end AlgebraicGeometry
