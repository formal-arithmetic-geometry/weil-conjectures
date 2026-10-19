/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ExcellentNormalSurfaceLocalData
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.LocalOrdinaryPointBlowupsGlobalize

/-!
# Resolution of rational surface singularities by ordinary point blowups

Source: Stacks Project, Resolution of Surfaces, Tags 0BBV, 0BG0, 0BGE and 0BGM;
Dualizing Complexes, lemma-ubiquity-dualizing
(blueprint: lem-per-rational-surface-point-blowup-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A rational normal local surface essentially of finite type over a complete Noetherian
local ring has a finite ordinary point-blowup resolution. The initial structure map is an
isomorphism, and each later structure map is its predecessor composed with the displayed
ordinary blowup arrow. The ideal is the vanishing ideal of the closed singleton, so the
center has its reduced structure. Singularity is failure of regularity of its local ring.

The localization presentation allows different universes for the complete base and the
surface ring. The cohomology hypothesis uses the additive structure sheaf on the ordinary
Zariski topology and evaluates `Sheaf.H'` at the top open. No chosen cohomology comparison,
normalization, or extra excellence hypothesis is part of the statement.

Source: Stacks Project, Resolution of Surfaces, Tags 0BBV, 0BG0, 0BGE and the rational
singularity subcase of 0BGM; Dualizing Complexes, lemma-ubiquity-dualizing
(blueprint: lem-per-rational-surface-point-blowup-resolution).

Proof plan:
1. The complete-local excellence theorem makes C excellent. Write B=S^{-1}D for a finite type
   C-algebra D. Excellence is preserved by finite type extension and localization, so B is
   excellent and therefore Nagata. Its given normality, dimension and vanishing hypothesis now say
   precisely that B defines a rational singularity: the normal modifications in that definition
   are exactly the integral normal proper models inducing the given isomorphism of function
   fields. The cohomology is the same Zariski cohomology, by the topological-cohomology convention
   in the statement.
   Uses: lem-per-complete-local-excellence, lem-exc-finite-type-localization-excellent, lem-exc-
   quasi-excellent-nagata, def-per-rational-surface-singularity, def-sc-topological-abelian-
   cohomology.
2. Apply the rational-to-Gorenstein blowup theorem with R=B and complete base C. Its Nagata and
   rationality hypotheses were checked in Step 1. Obtain a finite ordinary tower X_n\to\cdots\to
   X_0=\operatorname{Spec}B at singular closed points over the closed point of the base. Its
   intermediate schemes are integral and normal, its endpoint X=X_n has Gorenstein local rings,
   and its composite is proper and identifies function fields. Each individual arrow is proper as
   well: the reduced ideal of a closed point on a Noetherian scheme is a finite-type quasi-
   coherent ideal, so the blowup-proper theorem applies, inductively. At the start
   \operatorname{Spec}B is Noetherian, and after each proper (hence finite type) arrow the finite-
   type-over-Noetherian theorem keeps it Noetherian.
   Uses: lem-per-rational-surface-gorenstein-blowups, lemma-nagata-blowup-proper, lem-weil-pbc-
   finite-type-over-noetherian, def-weil-proper-morphism.
3. The endpoint X is finite type over the excellent ring B. Finite-type/localization stability of
   excellence therefore makes X excellent on every affine chart. Step 2 gives Noetherianity,
   integrality and normality. Apply the closed-dominant dimension theorem to the proper birational
   map X\to\operatorname{Spec}B: its function-field extension has transcendence degree zero, so
   \dim X=\dim B=2. The excellent-normal-surface local-data theorem now applies. Its singular set
   is a finite set of closed points \{x_1,\ldots,x_t\}, and R_i=\mathcal O_{X,x_i} is an excellent
   Noetherian normal local domain of dimension two with normal maximal-ideal-adic completion. Each
   R_i is Nagata by quasi-excellent-implies-Nagata.
   Uses: lem-exc-finite-type-localization-excellent, lem-trf-closed-dominant-dimension, lem-per-
   excellent-normal-surface-local-data, lem-exc-quasi-excellent-nagata.
4. For each i, the proper map X\to\operatorname{Spec}B sends the closed singleton \{x_i\} to a
   closed singleton. Since B is local, that image is its unique closed point. Thus B\to R_i is a
   local homomorphism. The function-field identification of Step 2 embeds both rings in the same
   field and makes this map injective. Choose an affine neighbourhood \operatorname{Spec}E of x_i
   in the finite-type B-scheme X. Then E is a finite type B-algebra and the affine-stalk theorem
   identifies R_i=E_{\mathfrak q_i}, proving essential finite type. The fraction field of this
   stalk is the function field of the integral scheme X, hence is \operatorname{Frac}B. Apply
   rationality propagation to B\subseteq R_i: Step 1 supplies rationality and the normal Nagata
   dimension-two base; Step 3 supplies the normal dimension-two target. Consequently every R_i is
   rational.
   Uses: def-weil-proper-morphism, def-sc-function-field, lem-weil-pbc-affine-open-stalk-
   localization, lem-per-rational-singularity-birational-propagation.
5. Every R_i is Gorenstein by Step 2. Steps 3 and 4 also give normality, the Nagata property,
   dimension two, rationality and normal completion. These are exactly the hypotheses of the
   rational-double-point resolution theorem. Apply it to obtain a finite ordinary tower
   T_{i,m_i}\to\cdots\to T_{i,0}=\operatorname{Spec}R_i at singular reduced closed points over its
   closed point, with integral normal intermediate schemes and regular endpoint. There is no
   choice to make when t=0.
   Uses: lem-per-rational-double-point-blowup-resolution.
6. Apply ordinary-point-blowup globalization to the normal integral Noetherian scheme X, its
   distinct singular closed points x_i, and the towers of Step 5. This gives W=Z_N\to\cdots\to
   Z_0=X, a finite tower of proper ordinary blowups with integral normal Noetherian intermediate
   schemes. Its centers are singular reduced closed points. Over X\setminus\{x_i\} every
   intermediate scheme is unchanged; over x_i the endpoint local rings are identified with those
   of T_{i,m_i}. For t=0 it gives the identity tower.
   Uses: lem-per-local-ordinary-point-blowups-globalize.
7. Every point of W over X\setminus\{x_i\} has the unchanged regular local ring, since the x_i are
   exactly the singular points of X. Every point over some x_i has the local ring of its
   corresponding point on the regular scheme T_{i,m_i}. Thus all local rings of W are regular.
   Step 6 gives Noetherianity, so the local-ring characterization of a regular scheme makes W
   regular.
   Uses: def-weil-regular-scheme.
8. Concatenate the first ordinary tower and the tower of Step 6. All its schemes are integral and
   normal and all its arrows are proper. The second tower is supported over the x_i, which map to
   the closed point of \operatorname{Spec}B by Step 4; the first already had that support.
   Consequently every center is a singular reduced closed point lying over the closed point of
   \operatorname{Spec}B. The endpoint is regular by Step 7. Both finite lengths may be zero, so
   the conclusion includes the zero-length case.
-/
theorem exists_regular_ordinary_point_blowup_tower
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (B : Type v) [CommRing B] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
    (hDim : ringKrullDim B = 2)
    (hEss : ∃ (D : CommRingCat.{max u v}) (φ : C →+* D) (S : Submonoid D),
      φ.FiniteType ∧ Nonempty (LocalizedModule S D ≃+* B))
    (hRat : ∀ (Z : Scheme.{v}) [IsIntegral Z],
      (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)) →
      ∀ (f : Z ⟶ Spec (CommRingCat.of B)) [IsProper f]
        (hη : f (genericPoint Z) = genericPoint (Spec (CommRingCat.of B))),
        IsIso (f.functionFieldMap hη) → Subsingleton (Sheaf.H' Z.structureSheafAb 1 ⊤)) :
    ∃ (n : ℕ) (V : Fin (n + 1) → Scheme.{v})
      (p : ∀ i : Fin (n + 1), V i ⟶ Spec (CommRingCat.of B)),
      IsIso (p 0) ∧
      (∀ i : Fin (n + 1), IsIntegral (V i) ∧
        ∀ x : V i, IsDomain ((V i).presheaf.stalk x) ∧
          IsIntegrallyClosed ((V i).presheaf.stalk x)) ∧
      IsRegularScheme (V (Fin.last n)) ∧
      ∀ j : Fin n, ∃ (x : V j.castSucc) (hx : IsClosed ({x} : Set (V j.castSucc)))
        (I : (V j.castSucc).IdealSheafData),
        I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ ∧
        ¬ IsRegularLocalRing ((V j.castSucc).presheaf.stalk x) ∧
        p j.castSucc x = IsLocalRing.closedPoint B ∧
        ∃ e : V j.succ ≅ I.blowup,
          IsProper (e.hom ≫ I.blowupMap) ∧
          e.hom ≫ I.blowupMap ≫ p j.castSucc = p j.succ := by
  sorry

end AlgebraicGeometry
