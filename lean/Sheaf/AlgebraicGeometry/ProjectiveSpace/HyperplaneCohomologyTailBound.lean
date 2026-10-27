/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import Sheaf.AlgebraicGeometry.FixedHyperplaneRestrictionCohomology
import Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences

/-!
# Cohomology tails from a regular hyperplane restriction

Source: Stacks Project, Varieties, Tag 08AG, proof of `lemma-bound-quotients-free`,
the paragraphs beginning "Let i >= 2", "We still have to control H1", and "Suppose d > m prime"
(blueprint: lem-sfb-hyperplane-cohomology-tail-bound).

The given hyperplane is regular for the module. No infinitude assumption on the field
is needed. Cohomology means right-derived module global sections. Its vector-space
structure is restriction of scalars along the structure map from the base field.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

/-- A coherent module whose restriction to a regular hyperplane is `m`-regular has
vanishing cohomology in degrees at least two for twists at least `m`, and vanishing
first cohomology for twists at least `m + dim_k H^1(E(m))`.
The isomorphism `e` is over `k`; `htwist` identifies the pulled-back ambient twists
with the standard twists on the lower-dimensional projective space. Thus the regularity
hypothesis on `H`, expressed using the ambient twists, is exactly the stated regularity
of `G = i^* E`. The degree pair `d, 1 + d` ranges over all pairs `D - 1, D`.

Source: Stacks Project, Varieties, Tag 08AG, `lemma-bound-quotients-free`, middle
cohomology paragraphs, extracted for an arbitrary coherent module with regular
hyperplane restriction (blueprint: lem-sfb-hyperplane-cohomology-tail-bound).

Proof:
1. Twists of E are coherent by the local trivializations of O(d). A field is Noetherian,
   so lem-pc-projective-space-coherent-finiteness makes every twisted cohomology space
   finite-dimensional, in particular h = dim_k H^1(E(m)). Apply
   lem-sfb-fixed-hyperplane-restriction-cohomology to the given s; write a_d^q for
   multiplication H^q(E(d-1)) to H^q(E(d)) and r_d for restriction on sections.
   Choose the twist comparisons compatibly with products: a degree-one frame comparison
   a = c b gives a^d = c^d b^d for every integer d, also for negative d by dual frames.
   Transition functions make these comparisons glue and c^d c^e = c^(d+e) gives
   compatibility with the standard twist multiplication on projective (n-1)-space.
2. By lem-sfb-m-regular-coherent-sheaf-consequences for G on H, all its positive
   cohomology vanishes in twists at least m and section multiplication by linear
   forms is onto there. This includes n=1, where H is projective zero-space.
   By lem-pc-projective-space-serre-vanishing choose D at least zero such that every
   positive cohomology of E(t) vanishes for t at least D.
3. For q at least two and d at least m the exact sequence has zero H^(q-1)(G(d)),
   so a_d^q is injective. For t at least m compose the injections with indices
   t+1 through T=max(t,D). Their target H^q(E(T)) is zero, so H^q(E(t)) is zero.
   If T=t, Serre vanishing applies directly; no nonempty composite is required.
4. The zero H^1(G(d)) makes a_d^1 onto for d at least m. The preceding boundary
   delta_d satisfies ker(a_d^1)=im(delta_d) and ker(delta_d)=im(r_d). Consequently
   a_d^1 is injective exactly when delta_d is zero, exactly when r_d is onto.
5. Suppose d at least m+1 and a_d^1 is injective. Then r_d is onto. Express any
   section of G(d+1) as a finite sum of products g_l ell_l using step 2. Lift g_l
   through r_d and ell_l through the surjective restriction of linear forms in the
   fixed-hyperplane lemma. Compatibility with products makes r_(d+1) onto, hence
   a_(d+1)^1 injective. Induction gives all subsequent injections. Compose indices
   d through max(d,D) to embed H^1(E(d-1)) in the zero H^1(E(max(d,D))).
6. Put b_t=dim_k H^1(E(t)). For t at least m the maps to the next degree are onto.
   If the source is nonzero they cannot be injective by step 5, so a nonzero kernel
   vector extended to a basis gives b_(t+1) at most b_t-1. A zero source has zero
   image. Induct on r at least zero to get b_(m+r) at most max(h-r,0): the base is
   b_m=h; a zero value stays zero, and a positive value forces h-r positive and
   decreases by at least one. Thus b_(m+h)=0 and all later groups vanish, including
   h=0. This proves the second tail bound. -/
theorem hyperplane_cohomology_tail_bound (k : Type u) [Field k]
    (n : ℕ) (hn : 1 ≤ n)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules)
    (hE : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace E)
    (s : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) (hs : s ≠ 0)
    {H : Scheme.{u}} (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    [IsClosedImmersion i]
    (hH : i.ker = Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection _ s))
    (e : H ≅ ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)))
    (he : e.hom ≫ (ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)) ↘ Spec (.of k)) =
      i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))
    (htwist : ∀ d : ℤ,
      (Scheme.Modules.tensorPullback i).obj
          (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≅
        (Scheme.Modules.tensorPullback e.hom).obj
          (twist (ULift.{u} (Fin ((n - 1) + 1))) (Spec (.of k)) d))
    (hG : RingedSpace.IsCoherent H.toRingedSpace ((Scheme.Modules.tensorPullback i).obj E))
    (hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n E d s))
    (m : ℤ)
    (hregular : ∀ q : ℕ, 1 ≤ q → q ≤ n - 1 →
      Subsingleton ((RingedSpace.moduleCohomology H.toRingedSpace q).obj
        ((Scheme.Modules.tensorPullback i).obj E ⊗ₘ
          (Scheme.Modules.tensorPullback i).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (m - (q : ℤ)))))) :
    (∀ (q : ℕ) (t : ℤ), 2 ≤ q → m ≤ t →
      Subsingleton ((RingedSpace.moduleCohomology
        (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace q).obj
          (E ⊗ₘ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) t))) ∧
    (∀ t : ℤ,
      m + (Module.finrank k
        ((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k
          (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
            ((RingedSpace.moduleCohomology
              (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace 1).obj
                (E ⊗ₘ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m))) : ℤ) ≤ t →
      Subsingleton ((RingedSpace.moduleCohomology
        (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace 1).obj
          (E ⊗ₘ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) t))) := by
  sorry

end
end AlgebraicGeometry.ProjectiveSpace
