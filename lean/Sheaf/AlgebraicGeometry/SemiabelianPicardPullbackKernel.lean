/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.SplitTorusCharacterPushout
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.AbelianVariety.HomogeneousLineAlgebraicTriviality

/-! # The kernel of Picard pullback along a split-torus extension

Source: Milne, Abelian Varieties, I Proposition 9.3, printed pp.41--42.
This is the character-pushout consequence recorded in the DAG, rather than the
verbatim extension-classification statement of that proposition.
(blueprint: lem-sfb-semiabelian-picard-pullback-kernel)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An invertible module on an abelian quotient whose tensor pullback is trivial
is algebraically equivalent to the structure sheaf. The kernel square and fppf local
surjectivity express the exact sequence with its specified split torus. The relation
uses smooth connected separated finite-type parameter schemes and actual tensor pullbacks.

Source: Milne, Abelian Varieties, I Proposition 9.3, printed pp.41--42,
character-pushout consequence; I Proposition 8.4(b), printed pp.35--36.
(blueprint: lem-sfb-semiabelian-picard-pullback-kernel)

Proof plan, following the five steps of the DAG:
1. Put T = G_m^r. The kernel square expresses any two lifts of a section of A
   uniquely as g and g*i(t). Fppf local lifts therefore trivialize G as a T-torsor.
   By lem-sfb-multiplicative-type-largest-subtorus T is smooth; its Laurent
   presentation is affine and finitely presented, also in rank zero.
   Apply lem-sfb-smooth-affine-group-torsor-representability to see q is affine,
   smooth and surjective, with G times T identified with G times_A G.
   By lem-pc-smooth-flat, def-pc-fppf-site and lem-trf-fppf-covering-is-fpqc,
   q is an fpqc covering. By lem-sc-abelian-variety-characterization A is
   geometrically integral, hence geometrically connected. Commutativity descends
   from G by local lifting. Apply lem-sfb-semiabelian-geometric-power-integrality
   at n = 1 to obtain integrality of G.
2. Choose a frame s of q^*N. Its ratio under translation gives a regular unit
   u(g,t) with s(g*i(t)) = u(g,t)*s(g) and u(g,1) = 1. The Laurent ring of T
   is a domain, including T = Spec F in rank zero. Apply
   lem-sfb-rosenlicht-product-unit-factorization to the integral schemes G and T,
   based at their identities: u(g,t) = u(1,t). Comparing two successive
   translations makes chi(t) = u(1,t) a group-scheme character, as an identity
   of regular functions and thus also on nonreduced test schemes.
3. Apply lem-sfb-split-torus-character-pushout. Its quotient relation
   (g,z) ~ (g*i(t),chi(t)^(-1)*z) gives an extension E_chi by G_m, an invertible
   module M_chi with frame torsor E_chi, and a frame sigma_chi of q^*M_chi
   satisfying sigma_chi(g*i(t)) = chi(t)*sigma_chi(g).
4. Send s to sigma_chi. On G times_A G the matching character factors show
   this isomorphism respects the canonical descent identifications. Full
   faithfulness in lem-pc-fpqc-descent descends it and its inverse, giving
   N isomorphic to M_chi.
5. For a in A(F), the one-dimensional fibre of M_chi has a frame e. Translation
   by e in the commutative extension E_chi is G_m-equivariant and lies over
   translation by a. On local frames it therefore gives M_chi isomorphic to
   t_a^*M_chi. Apply lem-sfb-abelian-homogeneous-line-algebraic-triviality and
   transfer along N isomorphic to M_chi. In rank zero the character is trivial
   and M_chi itself is trivial. -/
theorem semiabelian_picard_pullback_kernel
    {F : Type u} [Field F] [IsAlgClosed F]
    (A G : Grp (Over (Spec (.of F)))) [IsAbelianVariety A.X]
    [IsCommMonObj G.X] [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (r : ℕ) (i : MultiplicativeType.splitTorus F r ⟶ G) (q : G ⟶ A)
    (hkernel : IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus F r).X)
      q.hom.hom η[A.X])
    (hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of F)))
      (yoneda.map q.hom.hom))
    (N : A.X.left.Modules) [N.IsInvertible]
    (htrivial : Nonempty ((Scheme.Modules.tensorPullback q.hom.hom.left).obj N ≅
      SheafOfModules.unit G.X.left.ringCatSheaf)) :
    Scheme.Modules.AreAlgebraicallyEquivalent A.X N
      (SheafOfModules.unit A.X.left.ringCatSheaf) := by
  sorry

end AlgebraicGeometry
