/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.FilteredColimitFiniteData
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Finite-stage detection of alteration objects and generic degrees

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé III, Proposition 6.2,
first paragraph, printed pp. 43--44, and Proposition 3.1, printed pp. 37--38;
Stacks Project, Tags 01ZM, 01ZO and 06AC
(blueprint: lem-per-ind-etale-alteration-object-degree-descent).

The objects and arrows are ordinary scheme pullbacks, using the recorded `Alt` category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- Alteration objects and the prime-to-ell generic degrees of a finite diagram descend
simultaneously to a stage, and persist at all later stages.

Source: ILO III 6.2, first paragraph, pp. 43--44, with the finite generic-rank argument
of III 3.1, pp. 37--38; the object and degree conditions are ILO II 1.2.2 and 1.1.8
(blueprint: lem-per-ind-etale-alteration-object-degree-descent).

Proof:
1. Write the affine bases as spectra of rings R_a, with limit ring R. The transition
   maps and R_a -> R are flat. The ordinary etale and ind-etale total-fraction
   comparisons identify Q_b with Q_a tensor R_b and Q with Q_a tensor R. Hence Q is
   the colimit of the Q_a. Each total ring is a finite product of generic residue fields.
2. Choose finite affine covers of the initial objects. On a chart C_0 the finitely
   generated nilradical N_0 extends to exactly the nilradical at each etale stage:
   modulo N_0 the base change is etale over a reduced ring, hence reduced. Its fixed
   generators vanish in the reduced limit, so elementwise colimit descent kills all
   of them at one stage, giving reduced models at all later stages.
3. On each initial chart take the kernel of C_0 -> C_0 tensor Q_0. Flat tensor exactness
   identifies all later kernels with its extensions. The limit kernel vanishes because
   maximal dominance and reducedness make the denominators nonzerodivisors. Kill its
   finitely many generators at a stage. Injectivity into the generic localization then
   implies that every source minimal prime contracts to a base minimal prime.
4. The generic-fibre finiteness criterion makes each limit object finite over Q.
   Finiteness descent (01ZO) over Spec Q_a gives finite generic fibres at a stage.
   This persists under base change, and with steps 2--3 gives objects of alt/S_a.
5. For a specified good arrow, its generic source and target algebras D and E are
   reduced finite algebras over Q, hence finite products of fields. Choose primitive
   target idempotents e_i and a source field factor h_i D of degree d_i prime to ell
   over each hit target field e_i E. Unhit target idempotents map to zero.
6. Descend these finitely many idempotents and their orthogonality, sum, and map
   equations by finite-data descent. The selected maps of clopen pieces are finite
   locally free of degrees d_i at the limit; fixed-degree descent (06AC) gives the
   same ranks at a stage and all later stages. Their initial maps are locally finitely
   presented because they are maps of finite algebras over a Noetherian ring.
7. At a later target generic point in the image, the chosen piece has a reduced
   fibre of dimension d_i: taking this fibre selects factors of the reduced generic
   source algebra. Its field-factor degrees sum to d_i, so some degree is prime to
   ell. All generic residue extensions are finite by the tower of finite field
   extensions over the base generic field. This proves maximal prime-to-ell finiteness.
8. Directedness combines the finitely many stages for charts, objects, arrows and
   factors. If the limit is empty, 01Z2 gives an empty stage and all later models
   are empty. Zero algebras and empty factor lists also cover empty individual models.
   Quasi-excellence and invertibility are retained from the parent setting.
-/
theorem exists_alteration_object_degree_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ a : Iᵒᵖ, IsAffine (D.obj a)]
    [∀ a : Iᵒᵖ, IsNoetherian (D.obj a)]
    [∀ a : Iᵒᵖ, IsReduced (D.obj a)]
    [∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g)]
    [∀ {a b : Iᵒᵖ} (g : a ⟶ b), Etale (D.map g)]
    (c : Cone D) (_hc : IsLimit c) [IsReduced c.pt] [IsNoetherian c.pt]
    (_hqe : ∀ a : I, IsQuasiExcellent Γ(D.obj (op a), ⊤))
    (a₀ : I) (ell : ℕ) [Fact ell.Prime]
    (_hell : IsUnit (ell : Γ(D.obj (op a₀), ⊤)))
    (n m : ℕ) (V : Fin n → Over (D.obj (op a₀)))
    [∀ b : Fin n, LocallyOfFinitePresentation (V b).hom]
    [∀ b : Fin n, QuasiCompact (V b).hom]
    [∀ b : Fin n, QuasiSeparated (V b).hom]
    (s t : Fin m → Fin n) (f : ∀ j : Fin m, V (s j) ⟶ V (t j))
    (_hV : ∀ b : Fin n, ∃ T : Alt c.pt,
      T.obj = (Over.pullback (c.π.app (op a₀))).obj (V b)) :
    ∃ (a₁ : I) (_ha₁ : a₀ ≤ a₁), ∀ (a : I) (ha : a₁ ≤ a),
      (∀ b : Fin n, ∃ T : Alt (D.obj (op a)),
        T.obj = (Over.pullback (D.map (homOfLE (_ha₁.trans ha)).op)).obj (V b)) ∧
      (∀ j : Fin m,
        IsMaximallyPrimeToEllFinite ell
          (((Over.pullback (c.π.app (op a₀))).map (f j)).left) →
        IsMaximallyPrimeToEllFinite ell
          (((Over.pullback (D.map (homOfLE (_ha₁.trans ha)).op)).map (f j)).left)) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
