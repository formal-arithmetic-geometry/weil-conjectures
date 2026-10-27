module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ClosedImmersionUnboundedProjectionFormula
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Nonpositive finite free tensor after closed pushforward

Source: Stacks Project, More on Morphisms, Tag 09US,
`lemma-pull-relative-pseudo-coherent`, tensor-filtration paragraph, extracted as an
absolute closed-pushforward lemma, with the tail vanishing in degrees at least the cutoff
(blueprint: lem-sfb-closed-pushforward-nonpositive-free-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u wP wW

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Tensoring by a nonpositive complex of finite free modules preserves degree-`m`
pseudo-coherence of the derived closed pushforward. The object `Q` is arbitrary, and
neither `Q` nor `F` is required to be bounded below or quasi-coherent.

Source: Stacks Project, More on Morphisms, Tag 09US,
`lemma-pull-relative-pseudo-coherent`, tensor-filtration paragraph, extracted as an
absolute closed-pushforward lemma with the corrected tail inequality
(blueprint: lem-sfb-closed-pushforward-nonpositive-free-tensor).

Proof:
1. Put A = Rj_*Q. Restrict to an approximation open U for A and its inverse image V.
   Closed pushforward is exact (lem-sfb-closed-immersion-unbounded-projection-formula).
   It commutes with open restriction (lem-pc-module-pushforward-open-restriction).
   Exact restriction preserves K-flatness and total tensor (lem-pc-kflat-open-restriction,
   lem-pc-open-restriction-total-tensor, lem-pur-site-restriction-module-adjunction-exact),
   so it suffices to work on U, using exact-functor derived factorization.
2. A strictly perfect approximation B to A on U gives an upper cohomology bound a >= m.
   Exactness of closed pushforward and exact-functor cohomology identify j_*H^i(Q) with
   H^i(A). Closed pushforward detects zero sheaves, since every open of V is the inverse
   image of an open of U (also lem-weil-pbc-closed-pushforward-stalks). Hence H^i(Q)=0
   for i>a locally. This uses def-sfb-m-pseudo-coherent-complex and def-pc-perfect-complex.
3. Good truncation at a gives a representative E of Q with E^p=0 for p>a
   (def-kun-truncations). Finite free terms are flat; the bounded-above-flat K-flat
   lemma makes F K-flat (def-pc-flat-sheaf-modules, lem-pc-bounded-above-flat-kflat).
   Thus the local target is C=j_*Tot(E tensor F). In degree n its possible columns
   satisfy n-a <= q <= 0, so only finitely many contribute.
4. Finite sums A^r[-q] are m-pseudo-coherent for q<=0, by taking finite sums and shifts
   of the strictly perfect approximations. Indeed H^i(A[-q])=H^(i-q)(A), and i-q>=i.
   Rank zero is witnessed by the zero complex.
5. For c<=0 let F_c be the stupid truncation retaining degrees >=c, and set
   C_c=j_*Tot(E tensor F_c), with C_1=0. The degreewise split sequence of column
   truncations gives a distinguished triangle C_(c+1) -> C_c -> A^(r_c)[-c]
   (lem-weil-pbc-degreewise-split-derived-triangle). A basis and the sign (-1)^(cn)
   identify the quotient differential with the shifted one; only finite sums occur.
6. Finite descending induction from C_1=0 proves C_c m-pseudo-coherent, by clause (2)
   of lem-sfb-ringed-site-m-pseudocoherent-triangle. Its Zariski-site approximation
   property is exactly the scheme open-cover property.
7. Choose c=min(0,m-a). The discarded quotient D=C/C_c only has terms in degrees
   <=a+c-1<=m-1. Thus the zero strictly perfect complex approximates D in degree m.
   This is vanishing in degrees >=m; no lower bound is used.
8. The split sequence C_c -> C -> D gives a distinguished triangle. The same triangle
   lemma proves C m-pseudo-coherent from its two end vertices. The local comparisons
   and the open-cover definition give the conclusion on W. -/
theorem isMPseudoCoherent_closedPushforward_tensor_nonpositive_free
    (P W : Scheme.{u}) [IsAffine P] [IsAffine W]
    [HasDerivedCategory.{wP} (SheafOfModules.{u} (moduleRings P.toRingedSpace))]
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))]
    [∀ U : W.Opens,
      HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (j : P ⟶ W) [IsClosedImmersion j] (m : ℤ) (Q : schemeDerivedCategory P)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings P.toRingedSpace)) ℤ)
    (hF_zero : ∀ q : ℤ, 0 < q → IsZero (F.X q))
    (hF_free : ∀ q : ℤ, q ≤ 0 → ∃ r : ℕ,
      Nonempty (F.X q ≅ SheafOfModules.free
        (R := moduleRings P.toRingedSpace) (ULift.{u} (Fin r))))
    (hQ : Scheme.IsMPseudoCoherent W m ((schemeDerivedDirectImage j).obj Q)) :
    Scheme.IsMPseudoCoherent W m
      ((schemeDerivedDirectImage j).obj (Q ⊗ DerivedCategory.Q.obj F)) := by
  sorry

end AlgebraicGeometry
