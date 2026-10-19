/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.GRing
import Sheaf.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Mathlib.Topology.Irreducible
import Sheaf.RingTheory.CompleteLocalConnectednessBound

/-!
# Connected punctured principal slices of excellent normal local domains

Source: Stacks Project, Algebraization, Tag 0ECR (lemma-punctured-still-connected),
with More on Algebra, Tags 0C23 and 07NV, and Algebra, Tag 00MC
(blueprint: lem-per-normal-punctured-hypersurface-connected).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- A punctured principal hypersurface in an excellent normal local domain of finite dimension
at least three is nonempty and connected. Source: Stacks Project, Algebraization, Tag 0ECR,
via normality of completion (More on Algebra, Tag 0C23), dimension preservation (Tag 07NV),
and faithful flatness of completion (Algebra, Tag 00MC).
(blueprint: lem-per-normal-punctured-hypersurface-connected)

Proof:
1. Set B to be the maximal-ideal completion of A. It is Noetherian and local, its maximal
   ideal n is the extension of m, and its residue field is that of A. It is n-adically
   complete and dim B = dim A = N >= 3. Use lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal,
   and lem-weil-pbc-completion-dimension. Noetherianity makes m finitely generated.
2. Excellence implies the G-ring condition. By lem-weil-pbc-g-ring-completion-regular,
   A -> B is flat with geometrically regular fibres. The trivial residue-field extension
   makes each fibre regular, hence normal by lem-weil-pbc-regular-ring-normal.
   Apply lem-weil-pbc-flat-normal-fibres-noetherian-normal to deduce normality of B.
   Localization at the maximal ideal of a local ring changes nothing, so B is a domain.
3. The generic point (0) belongs to every nonempty open in Spec B. Thus each nonempty open
   is connected and Spec B is its sole irreducible component. In the notation of Tag 0ECR,
   d = N and c = N: removing a proper closed subset leaves a nonempty connected open,
   whereas removing all of Spec B leaves the empty space, which is not connected.
   Use def-weil-affine-spectrum, def-weil-pbc-krull-dimension-ring,
   def-weil-connected-scheme and def-weil-irreducible-components.
4. The image g of f belongs to n. The proper ideal (g) has one generator, and
   1 < min(c, d - 1) since N >= 3. The final assertion of
   lem-per-complete-local-connectedness-bound gives that V(g) minus {n} is nonempty
   and connected. No normality of B/(g) is used.
5. By lem-weil-pbc-local-completion-faithfully-flat, Spec B -> Spec A is surjective.
   A prime over m contains mB = n and hence equals n; conversely n contracts to m,
   by the residue-field identification in lem-weil-pbc-local-completion-local-ring.
   A prime contains g precisely when its contraction contains f. Therefore the inverse
   image of V(f) minus {m} is V(g) minus {n}, and the restricted map is surjective.
6. Contraction of primes is continuous, since the inverse image of D(a) is D(image(a)).
   The restricted map is continuous. Its image is nonempty; a nontrivial clopen partition
   of that image would pull back to a nontrivial clopen partition of V(g) minus {n}.
   This proves the asserted nonemptiness and connectedness. -/
theorem normal_punctured_hypersurface_connected
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hA : IsExcellent A)
    (hdim_finite : ringKrullDim A < ⊤) (hdim : (3 : WithBot ℕ∞) ≤ ringKrullDim A)
    (f : A) (hf : f ≠ 0) (hfm : f ∈ IsLocalRing.maximalIdeal A) :
    IsConnected (PrimeSpectrum.zeroLocus {f} \ {IsLocalRing.closedPoint A}) := by
  sorry

end RingTheory
