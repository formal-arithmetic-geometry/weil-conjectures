/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Module.Projective
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeProperties
import WeilConjectures.Algebra.Homology.AcyclicLift
import WeilConjectures.AlgebraicGeometry.ComplexLiftStrictMap
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeCokernel
import WeilConjectures.AlgebraicGeometry.ProjectiveClassReducedSplitting
import WeilConjectures.RingTheory.FiniteProjectiveFreeModIdeal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Lifting a marked finite-free model modulo a Jacobson ideal

Source: Stacks Project, More on Algebra, Tags 0BCB and 0BCA; Algebra, Tag 00DV
(blueprint: lem-sfb-jacobson-marked-free-complex-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory

namespace DerivedCategory

/-- Lift a prescribed derived finite-free model, retaining both its marking and its cutoff.
`L`, `ε`, and the left-derived universal property present derived extension of scalars,
exactly as in `lem-pur-derived-change-of-rings`. On a bounded-above free complex `P`,
`ε.app P` is the canonical K-flat comparison `c_P`. The two chosen localization Hom
universes are independent. No nilpotence of the ideal is assumed.

Source: Stacks Project, More on Algebra, Tag 0BCB (finite-free case), Tag 0BCA (choose
its delta to represent the inverse of the specified alpha), and Algebra, Tag 00DV
(blueprint: lem-sfb-jacobson-marked-free-complex-lift).

Proof:
1. Use the class of finite projective modules (def-weil-pbc-projective-module). It is
   closed under sums and summands: lift the two component maps for sums, and extend a
   map by zero and restrict its lift for summands; concatenate or project finite
   generating sets. Reduction detects surjections by lem-sc-finite-module-surjective-mod-ideal.
2. By def-pc-ring-pseudo-coherent-complex choose a bounded-above finite-free complex H
   and h : Q(H) ≅ K. By lem-weil-pbc-free-module-projective and
   lem-weil-pbc-projective-module-flat its terms are projective and flat. Apply
   lem-pc-module-bounded-flat-kflat and lem-pur-derived-change-of-rings to obtain c_H.
   By lem-pc-ring-derived-map-representative represent c_H L(h⁻¹) alpha⁻¹ by a chain
   map delta : F → H/IH. Its derived class is invertible, so delta is a quasi-isomorphism.
3. By lem-sc-complex-lift-cone-properties the actual cone of delta is bounded above,
   acyclic, and termwise the reduction of finite-free modules. By
   lem-sc-complex-lift-acyclic-projective lift it to an acyclic bounded-above finite
   projective complex A, with an identification e of its reduction with that cone.
4. By lem-sc-complex-lift-strict-map lift the cone inclusion to f : H → A. Put
   B = coker(f). By lem-sc-complex-lift-cone-cokernel its reduction is F[1], identified
   by the second coordinate of e, and the reduced sequence is degreewise split.
   Apply lem-sc-projective-class-reduced-splitting degreewise: the original sequence
   is short exact with finite projective cokernel terms, and hence degreewise split.
5. Set P = B[-1] and theta to the shifted second-coordinate identification. By
   lem-sc-finite-projective-free-mod-ideal the finite projective terms of P are free.
   For i > b their reductions vanish; apply lem-sc-finite-module-surjective-mod-ideal
   to 0 → Pⁱ to obtain Pⁱ = 0. All four bounded-above projective complexes H,A,B,P
   are K-flat by lem-weil-pbc-projective-module-flat and lem-pc-module-bounded-flat-kflat.
6. By lem-weil-pbc-complex-ses-triangle the sequence H → A → B has canonical boundary
   s : Q(B) → Q(H)[1]. Since A is acyclic, its derived image is zero. Apply
   lem-weil-pbc-hom-into-triangle-exact and its rotations: Hom(W,s) is bijective for
   every W. Taking W = Q(H)[1] and Q(B) shows s is invertible. Put t = s[-1] and beta = ht.
7. In the reduced sequence H/IH → Cone(delta) → F[1], use the first-coordinate
   retraction and second-coordinate section. Their boundary pi d u is delta[1].
   By lem-weil-pbc-degreewise-split-derived-triangle this computes the canonical
   boundary, fixing the sign for the cone convention with third map minus projection.
   By lem-sfb-ringed-kflat-pullback-ses-triangle on the point site, reduction preserves
   this boundary and its shift. Shift back to get c_H L(t) = Q(delta) Q(theta) c_P.
8. The choice of delta gives Q(delta) alpha L(h) = c_H. Substitute the preceding
   identity and beta = ht and cancel Q(delta). This gives alpha L(beta) = Q(theta) c_P,
   the displayed marking equation, together with the cutoff and finite freeness. -/
theorem exists_marked_finiteFree_lift_of_jacobson
    {R : Type u} [CommRing R] (I : Ideal R)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : Q ⋙ L ⟶
      (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ) ⋙ Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars.{u, u, max u v}
        (Ideal.Quotient.mk I)).mapHomologicalComplex (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ε.app P ≫ Q.map θ.hom = L.map β.hom ≫ α.hom := by
  sorry

end DerivedCategory
