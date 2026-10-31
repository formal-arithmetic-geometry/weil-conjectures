/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.RelativeTorus
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.AlgebraicGeometry.FpqcClosedImmersionDescent
import WeilConjectures.AlgebraicGeometry.NoetherianDvrProperness
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism

/-!
# A monic relative torus homomorphism is a closed immersion

Source: Conrad, *Reductive group schemes*, Theorem 5.3.5 and direct proof,
printed pages 165--168; the affine multiplicative-type case is Appendix B,
Lemma B.1.3, pages 281--282. The non-affine target reduction uses
Prasad--Yu, Proposition 3.1 (blueprint: lem-sfb-relative-torus-monomorphism-closed).

## Main statement

A homomorphism from a relative torus to a separated finitely presented group
scheme is a closed immersion when it is pointwise injective.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pointwise monic homomorphism from a relative torus is a closed immersion.

Source: Conrad, *Reductive group schemes*, Theorem 5.3.5 and direct proof,
printed pages 165--168; Appendix B, Lemma B.1.3, pages 281--282; Prasad--Yu,
Proposition 3.1 (blueprint: lem-sfb-relative-torus-monomorphism-closed).

Proof, following the accepted ten-step split:
1. Injectivity on all S-scheme points makes u a monomorphism of schemes: if
   two maps to P have equal composites with u, they have the same composite
   to S, so the pointwise hypothesis applies. The same holds after base change.
2. Choose an fppf splitting cover and refine by affine opens of constant rank.
   Its pullback to G is fppf, hence fpqc (lem-trf-fppf-covering-base-change,
   lem-trf-fppf-covering-is-fpqc). By lem-pc-fpqc-descend-closed-immersion it
   suffices to work over Spec A with P the rank-r split torus, allowing r = 0.
3. Use lemma-nagata-noetherian-inverse-system-affine and thm-pd-spreading-out
   to descend G, its group operations and u to a finite-type integer subalgebra
   of A. Descend all group and homomorphism identities to a common later stage.
4. Enlarge the stage using lem-weil-pbc-descend-separated and
   lem-weil-pbc-descend-monomorphism. Local finite type of u follows on affine
   charts from finite generators of P over the base. By
   lem-weil-pbc-finite-type-over-noetherian the models are Noetherian; u is
   therefore quasi-compact and of finite type. Denote this stage by S₀.
5. By lem-pc-proper-monomorphism-closed it suffices to prove u₀ proper.
   Apply lem-sfb-noetherian-dvr-properness to an arbitrary DVR square.
   Pull both groups back to Spec R, with fraction field K, obtaining u_R.
6. By lem-sfb-algebraic-group-monomorphism-closed-immersion the generic map
   u_K is closed. Lem-sfb-dvr-flat-generic-subgroup-closure gives its separated,
   flat, finitely presented schematic closure C in G_R. The split torus P_R is
   smooth by lem-sfb-relative-torus-character-reconstruction, hence flat by
   lem-pc-smooth-flat. The closure's flat-source property factors u_R through
   C; its closed inclusion is monic, so the factor is a monic homomorphism.
7. By lem-sfb-dvr-generic-affine-group-affine, C is affine: it is separated,
   flat and of finite type over R, with affine generic fibre the split torus.
8. The split torus has coordinate Hopf algebra R[ℤ^r], hence is of
   multiplicative type. Lem-sfb-affine-multiplicative-type-monomorphism-closed
   makes its monic homomorphism to C closed. Composition gives u_R closed
   (lem-weil-pbc-closed-immersion-comp).
9. The section of G_R from the DVR square lies in an affine open containing
   its closed point. There u_R is Spec(B/I) into Spec B, by
   def-weil-closed-immersion. The map B to R kills I in K, hence in R because
   R injects into K. It factors through B/I and gives a lift, uniquely by
   monicity. Lem-sfb-noetherian-dvr-properness gives properness of u₀;
   lem-pc-proper-monomorphism-closed makes it a closed immersion.
10. Base change recovers u on the split affine piece, and closed immersions
    survive base change (lem-weil-pbc-closed-immersion-base-change).
    Lem-pc-fpqc-descend-closed-immersion returns to the original base. -/
theorem relative_torus_monomorphism_closed
    {S : Scheme.{u}} (P G : Over S) [GrpObj P] [GrpObj G]
    [IsCommMonObj P] [Smooth P.hom] [IsAffineHom P.hom]
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom]
    [QuasiSeparated P.hom] [IsSeparated G.hom]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    [QuasiSeparated G.hom] (hP : IsRelativeTorus P)
    (u : P ⟶ G) [IsMonHom u]
    (hu : ∀ (T : Over S), Function.Injective (fun x : T ⟶ P => x ≫ u)) :
    IsClosedImmersion u.left := by
  sorry

end AlgebraicGeometry
