/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.AlgebraicGeometry.ExcellentNormalizedBlowupTower
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.Blowup.Principalization
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import Sheaf.AlgebraicGeometry.NormalSurfaceExceptionalCurves
import Sheaf.AlgebraicGeometry.NormalizedSurfaceGraphExceptionalInjection

/-!
# Domination by normalized point blowups of an excellent surface

Source: Stacks Project, Resolution of Surfaces, Tag 0BBT,
`resolve-lemma-dominate-by-normalized-blowing-up`, and Tag 0BFT for properness
(blueprint: lem-per-excellent-surface-normalized-domination).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper birational morphism to a normal excellent integral Noetherian surface is
 dominated by a finite tower of normalized blowups at reduced closed points. Normality is
 stated on stalks, and birationality uses the actual generic-stalk map. The bottom level is
 identified with the given base, not with an additional normalization. Length zero is allowed.

Source: Stacks Project, Resolution of Surfaces, Tags 0BBT and 0BFT
(blueprint: lem-per-excellent-surface-normalized-domination).

Proof plan, following the ten steps of the DAG:
1. Normalize Y, using lem-per-normal-surface-exceptional-curves. The normalization is finite
   and proper, and its composite to S remains birational. Since S is normal, its initial
   normalization in Tag 0BBT is S itself (def-sc-normalization).
2. Strongly induct on the number r of contracted curves of a proper birational map Z to X
   between normal excellent Noetherian surfaces. The exceptional-curves lemma makes r finite
   and says that r = 0 is an isomorphism, giving the tower of length zero.
3. Choose a contracted curve C over the closed point x. Its generic local ring R is a DVR
   with common fraction field K = Frac(O_X,x); its residue field has transcendence degree one
   over k(x). Lift a transcendental residue to u in R and write u = a/b in K.
4. The residue of u is nonzero, so v(a) = v(b). A unit b in O_X,x would put that residue in
   k(x), which is impossible. Thus a and b lie in its maximal ideal and N = min(v(a),v(b)) > 0
   (def-sc-discrete-valuation-ring).
5. Blow up the reduced point x and normalize. The excellent normalized-tower geometry theorem
   gives a normal integral excellent Noetherian surface with a projective birational map;
   lem-trf-projective-bundle-proper gives properness. Apply
   lem-per-normalized-surface-graph-exceptional-injection to the normalized dominating
   component of the graph. It supplies an injection of contracted curves into those of Z/X.
   Stop if the number drops; otherwise C has a unique continuing curve C_1.
6. The graph-injection lemma identifies its generic DVR with R, and the new contraction point
   x_1 is closed with k(x_1)/k(x) finite. Therefore the same residue of u remains
   transcendental over k(x_1). The local maps O_X,x to O_X1,x1 to R commute.
7. The point ideal is finite type on Noetherian affines. Principalization gives a local
   non-zero-divisor d generating its extension to the ordinary blowup. By
   lem-per-integral-blowup-projective-geometry the blowup is integral; its local rings and
   the normalized local rings embed in K, so d remains nonzero. Its extension at x_1 is
   d O_X1,x1, with d in the maximal ideal. Divide a and b by d to get nonzero a_1,b_1 in
   O_X1,x1 with u = a_1/b_1 (thm-nagata-blowup-principalizes-center).
8. Locality to R gives v(d) > 0, so N_1 = N - v(d) < N. The same transcendental-residue
   argument as in step 4 gives N_1 > 0 and puts a_1,b_1 in the new maximal ideal.
9. Repeat while the number of contracted curves stays r. The injection, unique continuing
   curve, common DVR, finite residue extensions and local fraction representations persist.
   A strictly decreasing positive integer cannot persist for N steps. Thus after finitely
   many normalized point blowups the number of contracted curves drops. Graph maps occur
   only on auxiliary sources, not as extra steps of the base tower.
10. Apply the outer induction hypothesis at that smaller number, concatenate the towers,
   and compose the endpoint map through the auxiliary source and the normalization to Y.
   The normalized-tower geometry at each step gives integral normal levels, proper arrows
   and their function-field isomorphisms. No regularity of the endpoint is asserted. -/
theorem exists_normalized_point_blowup_domination
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]
    (hNormal : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x))
    (hExcellent : ∀ U : S.affineOpens, IsExcellent Γ(S, U))
    (hDim : topologicalKrullDim S = 2)
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ S) [IsProper f]
    (hη : f (genericPoint Y) = genericPoint S)
    (hBir : IsIso (f.functionFieldMap hη)) :
    ∃ (n : ℕ) (X : Fin (n + 1) → Scheme.{u})
      (hIntegral : ∀ i : Fin (n + 1), IsIntegral (X i))
      (hzero : X 0 = S)
      (p : ∀ i : Fin (n + 1), X i ⟶ S)
      (arrow : ∀ j : Fin n, X j.succ ⟶ X j.castSucc),
      p 0 = eqToHom hzero ∧
      (∀ i : Fin (n + 1), ∀ x : X i,
        IsDomain ((X i).presheaf.stalk x) ∧
          IsIntegrallyClosed ((X i).presheaf.stalk x)) ∧
      (∀ j : Fin n, arrow j ≫ p j.castSucc = p j.succ) ∧
      (∀ j : Fin n, IsProper (arrow j)) ∧
      (∀ j : Fin n, ∃ hgen :
        arrow j (@genericPoint (X j.succ) _ inferInstance
          (@irreducibleSpace_of_isIntegral _ (hIntegral j.succ))) =
          @genericPoint (X j.castSucc) _ inferInstance
            (@irreducibleSpace_of_isIntegral _ (hIntegral j.castSucc)),
        IsIso (@Scheme.Hom.functionFieldMap _ _ (hIntegral j.succ)
          (hIntegral j.castSucc) (arrow j) hgen)) ∧
      (∀ j : Fin n, ∃ (x : X j.castSucc)
        (hx : IsClosed ({x} : Set (X j.castSucc))) (I : (X j.castSucc).IdealSheafData),
        I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ ∧
        ∃ (_ : IsIntegral I.blowup) (e : X j.succ ≅ I.blowup.normalization),
          e.hom ≫ I.blowup.fromNormalization ≫ I.blowupMap = arrow j) ∧
      ∃ l : X (Fin.last n) ⟶ Y, l ≫ f = p (Fin.last n) := by
  sorry

end AlgebraicGeometry
