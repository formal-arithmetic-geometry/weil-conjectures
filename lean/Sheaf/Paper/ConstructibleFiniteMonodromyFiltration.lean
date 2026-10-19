/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constructible sheaves filtered by finite-monodromy stratum sheaves

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
7.2.3--7.2.6, 7.3.1--7.3.6, 7.4.2 and the first reduction in 7.4.6, pp. 301--307
(blueprint: lem-per-constructible-finite-monodromy-filtration).

We use the existing fixed-coefficient module-sheaf category, the ordinary inverse and
closed direct images, and the open extension by zero. Finiteness of a module sheaf means
finite generation of its module stalks, not finiteness of the underlying sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A constructible module sheaf over a Noetherian F_ell-algebra has a finite filtration
whose graded pieces are locally closed extensions of finite-monodromy local systems.
The factorization of each immersion is closed followed by open. All filtration terms
and quotients are constructible. If E is zero the filtration has length zero.

Source: ILO, Expose XVII, 7.2.3--7.2.6, 7.3.1--7.3.6, Proposition 7.4.2 and the first
reduction in Proposition 7.4.6, pp. 301--307
(blueprint: lem-per-constructible-finite-monodromy-filtration).

Proof plan:
1. Pass to the reduction using prop-weil-pbc-universal-homeomorphism-topos. Constants
and module operations transport through this equivalence; pullback preserves local
trivializations by lemma-constructible-pullback-constant and
lemma-constructible-pullback-locally-constant. Reduced closed remainders exist by
lem-weil-pbc-reduced-induced-closed-subscheme and remain Noetherian.
2. Induct on closed remainders using lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.
Choose a generic point of an irreducible component, remove the other finitely many
components (lem-weil-pbc-noetherian-finitely-many-components), and choose a reduced affine
open in its given stratum. The factorization through that stratum follows from
lem-weil-pbc-reduced-source-factors-through-closed-subscheme.
3. Choose an affine etale trivializing chart meeting the generic point. Its morphism is
quasi-compact and quasi-separated by lem-weil-pbc-affine-morphism-permanence. Etaleness,
lem-weil-pbc-unramified-quasi-finite-at-points, and
lem-weil-pbc-lqf-qc-source-bounded-fibres give a finite generic fibre. Apply
lem-weil-pbc-generic-finite-morphism-open-neighborhood to make the chart finite etale
on a nonempty open containing that point.
4. Its source is Noetherian by pqf-lem-locnoeth-lft and quasi-compactness. Choose an open
and closed connected component by lem-sfb-noetherian-connected-components-open.
Use lem-fet-galois-category, lem-galois-object-exists and lem-galois-axioms to dominate
it by a connected finite etale Galois cover. Pullback composition trivializes E on this
cover. Induction on the proper closed complement gives a finite ordered partition.
5. Apply lem-weil-pbc-open-closed-short-exact to the first open stratum in a remainder:
its kernel is j_!L and its quotient is the closed direct image from the complement.
Induct on the number of strata to filter that quotient.
6. Closed direct image is exact by lemma-openclosed-stalk-lowerstar,
prop-weil-pbc-geometric-stalks-exact, and lemma-weil-pbc-geometric-stalk-conservative;
stalks outside the closed subset vanish. Pull back its filtration under the quotient
map and prepend the kernel, giving actual subsheaves of E.
7. For closed i:Z -> T and open j':V' -> Z, use the open complement of Z minus V'
in T to factor V' -> T as closed then open. Adjunction and the direct-image formula
compare the two extensions. On geometric stalks they agree on V' and both vanish
outside; conservativity gives j''_!i''_* M isomorphic to i_*j'_! M.
8. Apply this comparison and lem-weil-pbc-inverse-image-composition to every inductive
quotient and then to the reduction. On each ordered stratum every filtration term
restricts to E or to zero, so terms and quotients are constructible. The zero sheaf,
including the empty scheme, has the empty filtration. -/
theorem exists_constructible_finiteMonodromy_filtration
    (ell : ℕ) [Fact ell.Prime]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod ell) A]
    (X : Scheme.{u}) [IsNoetherian X]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hE : ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} A) (R.immersion a)).obj E)) :
    ∃ (n : ℕ) (F : Fin (n + 1) → Subobject E),
      IsZero (F 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ∧
      IsIso (F (Fin.last n)).arrow ∧ (IsZero E → n = 0) ∧
      ∃ hF : ∀ a : Fin n, F a.castSucc ≤ F a.succ,
        (∀ a : Fin (n + 1), IsConstructibleSheaf (F a :
          Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) ∧
        ∀ a : Fin n,
          IsConstructibleSheaf (cokernel (Subobject.ofLE (F a.castSucc) (F a.succ) (hF a))) ∧
          ∃ (S V : Scheme.{u}) (i : S ⟶ V) (j : V ⟶ X)
            (_ : IsClosedImmersion i) (_ : IsOpenImmersion j)
            (_ : ConnectedSpace S) (_ : IsNoetherian S)
            (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
            IsFiniteLocallyConstantSheaf L ∧
            Nonempty (cokernel (Subobject.ofLE (F a.castSucc) (F a.succ) (hF a)) ≅
              (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
                ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj L)) ∧
            ∃ P : S.FiniteEtale,
              ConnectedSpace P.obj.left ∧ CategoryTheory.PreGaloisCategory.IsGalois P ∧
              ((Etale.upperStar (ModuleCat.{u + 1} A) P.obj.hom).obj L).IsConstant
                P.obj.left.smallEtaleTopology := by
  sorry

end AlgebraicGeometry.Scheme
