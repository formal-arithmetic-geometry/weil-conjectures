/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.DmPointStabilizer
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Comparison of curve stabilizers and dual-number automorphisms -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The stabilizer of a geometric curve object is its automorphism scheme. Its
identity dual-number points are the identity-reducing automorphisms of the cartesian
presheaf fibre product used by the curve-stack interface. All comparisons are over
the specified field, on every test scheme, and retain the group identity.
Source: Stacks Project, moduli-curves.tex, Tags 0DSQ and 0E6G, first proof paragraph;
categories.tex, fibred Yoneda lemma; stacks-morphisms.tex, Tag 0DSN
(blueprint: lem-sfb-proper-curve-stabilizer-comparison).

Proof: restrict the algebraic-space family X along Spec Omega -> Spec k, using the
equivalence between the slice sites and sheaves over the represented base. Its
properness and dimension bound follow from `isCurve`, tested on the identity
geometric point; the closed immersion diagonal, quasi-compactness, local finite
type and universal closedness are the other recorded `isCurve` properties. Apply
`exists_proper_curve_automorphism_scheme` to this space to get the separated
finite-type group scheme G and its natural representing group isomorphisms.
Use cartesian pullbacks of X to form its fibred Yoneda functor x. Evaluation at
the identity scheme gives an equivalence with X, so a factorization of x through
a full open U is equivalent to membership of X in U. In the reverse direction,
all pullback objects lie in U by `pullback`, giving that factorization.
Regard the represented scheme G over Omega as an algebraic space over k, with
map p to Spec Omega. The representing group isomorphisms and fibred Yoneda
identify its sections over every test scheme with the vertical natural
automorphisms of x. Their restriction naturality is exactly
`IsModuliAutomorphismSpace`. On etale charts p is the composite of an etale
scheme map with G -> Spec Omega, so unramifiedness of G implies the chartwise
condition. Conversely test on the identity chart of G.
Finally the slice-presheaf equivalence identifies automorphisms after restriction
to D = Spec(DualNumber Omega) with automorphisms over D of the cartesian presheaf
pullback of X. Naturality for the zero section identifies reduction to the identity
with `infinitesimalReduction` followed by the automorphism being
`infinitesimalReduction`. Naturality for D -> Spec Omega identifies the constant
identity point with the identity automorphism. Bijectivity of the representing
maps then gives the last equivalence. This uses arbitrary nonreduced test schemes
and does not assume smoothness or reducedness of G. -/
theorem ProperCurveModuli.exists_stabilizer_comparison {k : Type u} [Field k]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))
    (X : ProperCurveFamily (Over.mk a)) :
    ∃ (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk a)))
        (ProperCurveModuli.category (Spec (.of k))))
      (G : Grp (Over (Spec (.of Ω)))) (Z : AlgebraicSpace (Spec (.of k)))
      (p : Z.obj.obj ⟶ yoneda.obj (Over.mk a)),
      LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
      IsModuliAutomorphismSpace (Over.mk a) x Z p ∧
      (∀ U : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
        U.property ⟨Over.mk a, X⟩ ↔
          ∃ y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk a))) U.category,
            Nonempty (ModuliTwoIso
              (y.comp (fullModuliInclusion (ProperCurveModuli.category (Spec (.of k)))
                U.property)) x)) ∧
      (SpaceMapIsUnramified Z (Over.mk a) p ↔ IsUnramified G.X.hom) ∧
      ((∀ v : Spec (.of (DualNumber Ω)) ⟶ G.X.left,
        v ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ v =
          η[G.X].left →
        v = Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ η[G.X].left) ↔
        ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a X.projection) := by
  sorry

end AlgebraicGeometry
