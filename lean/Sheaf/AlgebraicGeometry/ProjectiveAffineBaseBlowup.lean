/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.ReesAlgebra
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.Affine.Functoriality
import WeilConjectures.Blowup.Affine.Localization
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra

/-! # H-projectivity of blowups over an affine Noetherian base

Source: Stacks Project, Divisors, Tag 02NS; Morphisms, Tags 087S and 01WE
(blueprint: lem-sfb-projective-affine-base-blowup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For an H-projective scheme over an affine Noetherian base, blowing up any
finite-type quasi-coherent ideal is H-projective both over the scheme and over its base.
The ideal may be zero or the unit ideal; the scheme may be empty or nonintegral.

Source: Stacks Project, Divisors, Tag 02NS; Morphisms, Tags 087S and 01WE
(blueprint: lem-sfb-projective-affine-base-blowup).

Proof plan:
1. Choose the factorization $X\xrightarrow{i}\mathbf P^N_S\xrightarrow{q}S$ in [def-kun-
   projective]. Apply [lem-weil-pbc-projective-ample-invertible] with the given ring $A$, this
   $N$, and this closed immersion $i$. Its statement supplies an invertible sheaf $\mathcal
   L=i^*\mathcal O_{\mathbf P^N_A}(1)$ which is ample on $X$ in the absolute sense. Thus the base
   $X$ of the blowup admits exactly the ample invertible sheaf required later; no passage from
   relative to absolute ampleness is left implicit.
2. Form the quasi-coherent graded Rees algebra $\mathcal R=\bigoplus_{n\geq0}\mathcal I^n$ of
   [def-nagata-sheaf-rees-algebra]. For an affine open $V=\operatorname{Spec}R\subseteq X$ put
   $I_V=\Gamma(V,\mathcal I)$. By [def-sbc-ideal-sheaf-powers], $\mathcal
   I^n|_V=\widetilde{I_V^n}$. Clauses (2) and (4) of [lem-weil-pbc-affine-tilde-gamma-adjunction]
   identify the sheaf direct sum on $V$ with $\widetilde{\bigoplus_n I_V^n}$ and its sections with
   $\bigoplus_n I_V^n$. The products agree on homogeneous summands, so $\Gamma(V,\mathcal
   R)=\mathcal R_R(I_V)$ as graded $R$-algebras, with degree-zero identity, by [def-nagata-rees-
   algebra]. This also identifies restriction maps: restricting a homogeneous section in degree
   $n$ restricts its coefficient in $\mathcal I^n$.
3. Apply clause (a) of [lem-weil-pbc-quasi-coherent-symmetric-algebra] to the degree-one inclusion
   $\mathcal I\to\mathcal R$. It gives an algebra morphism $\varphi:\operatorname{Sym}(\mathcal
   I)\to\mathcal R$. Clause (b) identifies it on each affine $V$ with
   $\operatorname{Sym}_R(I_V)\to\bigoplus_n I_V^n$, $x_1\cdots x_n\mapsto x_1\cdots x_n$ in degree
   $n$. In the symmetric grading of [lem-weil-pbc-symmetric-algebra-graded], which is the grading
   of the canonical affine-basis graded algebra $A_X(\mathcal I)$ of [def-trf-canonical-symmetric-
   graded-algebra] (the relative-Proj input for $\operatorname{Sym}(\mathcal I)$, identified there
   with the affine sections of clause (b)), this map preserves degree. It is onto in every degree:
   an element of the ideal power $I_V^n$ is a finite sum of products of $n$ elements of $I_V$ with
   coefficients in $R$, each the image of the same symmetric monomial; in degree zero the map is
   the identity of $R$. Hence $\varphi$ is a surjective graded sheaf-algebra morphism. This is a
   direct calculation, not an extra lemma about the blowup.
4. By [def-nagata-relative-proj] and [lemma-nagata-relative-proj-exists],
   $P=\operatorname{Proj}_X(\mathcal R)$ is glued from $\operatorname{Proj}(\Gamma(V,\mathcal R))$
   over affine opens $V$. Step 2, clause (2) of [prop-nagata-relative-proj-functoriality] (applied
   to the graded isomorphism $\bigoplus_n I_V^n\cong\mathcal R_R(I_V)$, $x\mapsto xt^n$ in degree
   $n$, identity in degree zero) and [def-nagata-affine-blowup] identify these, including their
   structure maps, with $\operatorname{Bl}_{I_V}(V)$, the local schemes of [def-nagata-global-
   blowup-local-model]. Check the transitions explicitly: [def-nagata-rees-localization-map] sends
   a degree-$n$ coefficient $x$ to $x/1$. The restriction morphism in [def-nagata-affine-blowup-
   restriction-map] is Proj of this map with the degree-zero identifications, and is an
   isomorphism by [prop-nagata-affine-blowup-restrict]. On a common basic affine refinement the
   blowup transition is $r_{j,s}\circ r_{i,s}^{-1}$ by [def-nagata-global-blowup-overlap-basic-
   map]. The relative-Proj construction restricts the same coefficients, so gives exactly this
   transition. The gluing datum of [def-nagata-global-blowup-glue-data], whose glued scheme is $B$
   by [def-nagata-global-blowup], is therefore the same datum as for $P$. The unique affine-chart-
   compatible isomorphism in [lemma-nagata-relative-proj-exists] yields $B\cong P$ over $X$. All
   intersections are treated by affine refinements, not assumed affine.
5. Apply clause (3) of [prop-nagata-relative-proj-functoriality] to the surjective degree-
   preserving morphism $\varphi$ of Step 3. Here $\operatorname{Sym}(\mathcal I)$ carries the
   graded structure of [def-trf-canonical-symmetric-graded-algebra], which is the algebra whose
   relative Proj is $\mathbf P_X(\mathcal I)$ in [def-trf-projective-bundle-morphism]. In the
   opposite direction it gives a closed immersion $\operatorname{Proj}_X(\mathcal
   R)\hookrightarrow\operatorname{Proj}_X(\operatorname{Sym}(\mathcal I))=\mathbf P_X(\mathcal I)$
   over $X$. The symmetric algebra is quasi-coherent by its construction in Step 3 and the Rees
   algebra is quasi-coherent by Step 2; the source is generated in degree one, so this is also
   exactly the situation of Stacks Tag 07ZK. Use the isomorphism of Step 4 to obtain
   $B\hookrightarrow\mathbf P_X(\mathcal I)$ over $X$. Since $\mathcal I$ is quasi-coherent of
   finite type by hypothesis, this factorization is projectivity in the projective-bundle sense of
   [def-trf-projective-bundle-morphism], with $\mathcal E=\mathcal I$.
6. Apply [lem-trf-projective-bundle-to-h-projective] to $b:B\to X$. Step 5 supplies its
   projective-bundle hypothesis, and Step 1 supplies an ample invertible sheaf on its base $X$.
   Therefore $b$ is H-projective in the finite-projective-space convention of the item. In
   particular this step uses no integrality or nonzero-ideal hypothesis.
7. The given $f:X\to S$ is H-projective, and Step 6 proves the same for $b$. Apply [lem-trf-h-
   projective-composition] with $g=b$ and $h=f$ to obtain that $fb:B\to S$ is H-projective as
   well. All steps apply to every finite-type quasi-coherent ideal, including $0$ and $\mathcal
   O_X$, and to an empty $X$. The argument has imposed no additional hypothesis on $X$ or $A$.
-/
theorem isHProjective_blowupMap_and_comp_of_affine_base (A : Type u) [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsHProjective f] (I : X.IdealSheafData)
    (hI : I.toModules.IsQuasiCoherentFiniteType) :
    IsHProjective I.blowupMap ∧ IsHProjective (I.blowupMap ≫ f) := by
  sorry

end AlgebraicGeometry
