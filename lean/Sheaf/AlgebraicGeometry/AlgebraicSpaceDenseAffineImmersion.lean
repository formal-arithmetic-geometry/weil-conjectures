/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart

/-!
# A dense open scheme immersing into affine space

Source: Stacks Project, spaces-limits.tex, Tag 088N, specialized to an affine
Noetherian target; spaces-morphisms.tex, Tags 06G4, 04ZK and 04ZL
(blueprint: lem-sfb-space-dense-affine-immersion).

The open subspace is exhibited by its representing scheme and its scheme-test open
immersion. Density uses the existing point image in the atlas topology. The two
commuting triangles retain the specified morphism to the affine base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type algebraic space over an affine Noetherian scheme has a
quasi-compact dense open scheme admitting an immersion into finite-dimensional affine
space over that same base. Neither the space nor the ring is assumed reduced; no
irreducibility, nonemptiness or flatness hypothesis is imposed.

Source: Stacks Project, spaces-limits.tex, Tag 088N
(lemma-embedding-into-affine-over-qs), specialized to the affine Noetherian base;
spaces-morphisms.tex, Tags 06G4, 04ZK and 04ZL
(blueprint: lem-sfb-space-dense-affine-immersion).

Proof:
1. The affine source B makes B to S separated by
   lem-weil-pbc-affine-source-morphism-separated. Its diagonal is a closed immersion
   on every scheme test by lem-weil-pbc-closed-immersion-base-change. Combine this
   with separatedness of f using lem-sfb-space-quasiseparated-test-calculus.
   Apply lem-sfb-quasiseparated-space-dense-scheme-open to get a dense open scheme V.
2. By pqf-def-locnoeth and lem-weil-pbc-affine-scheme-qcqs the base is Noetherian.
   Finite type makes X quasi-compact. Its etale charts are locally of finite type
   over B, hence locally Noetherian by pqf-lem-locnoeth-lft. Apply
   lem-sfb-noetherian-space-topology; its open subspace V is also Noetherian.
3. By lem-sc-noetherian-finite-irreducible-components and
   lem-sc-irreducible-components-cover, V has finitely many irreducible components.
   In each component remove all the other components. The resulting open is nonempty
   by irreducibility and maximality of components. Choose an affine open inside it
   using lem-weil-pbc-affine-opens-basis. These affine opens are disjoint and dense
   in their respective components, so their union U is open dense in X.
4. By lem-weil-pbc-finite-affine-coproduct-spectrum this finite disjoint union is
   the spectrum of the product of its coordinate rings. Thus U is affine and
   quasi-compact by lem-weil-pbc-affine-scheme-qcqs. The inclusions into V and X
   compose to an open immersion on every scheme test. For empty X use empty U:
   the empty product is the zero ring.
5. By lem-weil-pbc-open-immersion-etale the map U to X is an etale scheme chart.
   The chart test in def-sfb-space-morphism-properties makes U to B locally of
   finite type. It is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence.
   The affine-base construction in lem-chow-affine-immersion presents its coordinate
   ring as a quotient of a polynomial ring in finitely many variables. This gives
   a closed immersion into affine space over B, hence an immersion as requested.
   Restricting f defines g, and the two displayed triangles commute by construction.
   All restrictions retain their structure sheaves, including nilpotents. -/
theorem exists_dense_affineSpace_immersion {S : Scheme.{u}}
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (b : Spec (.of A) ⟶ S) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace (Over.mk b))
    (hsep : MapIsSeparated f) (hft : MapIsFiniteType f) :
    ∃ (U : Over S) (j : yoneda.obj U ⟶ X.obj.obj)
      (g : U ⟶ Over.mk b) (n : ℕ)
      (a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of A))),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j ∧
      CompactSpace U.left ∧ Dense (pointImage j) ∧
      j ≫ f.hom.hom = yoneda.map g ∧ IsImmersion a ∧
      a ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of A)) ↘ Spec (.of A)) = g.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
