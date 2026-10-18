/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.GroupTheory.WeilGroup
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor

/-!
# Finite constant cohomology and geometric monodromy

Source: Weil conjectures blueprint, sec-purity-real-sheaves/sk-p-real-rankone,
`lem-wf-finite-constant-h1-pi1.md`, equation (3.1) and its two naturality clauses
(blueprint: lem-wf-finite-constant-h1-pi1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FiniteEtale
open scoped FintypeCatDiscrete

namespace WeilConjectures

/-- Finite constant `H¹` is the group of continuous characters, with pointed pullback
naturality and Weil descent by inverse conjugation. Source: blueprint,
sec-purity-real-sheaves/sk-p-real-rankone, equation (3.1)
(blueprint: lem-wf-finite-constant-h1-pi1).

The map is the existing canonical torsor-monodromy bijection, upgraded to an additive
isomorphism by viewing the multiplicative character group as an additive group. Naturality
is stated on the canonical classes of all finite étale torsors: these exhaust `H¹`.
For the Weil formula the canonical map to the arithmetic fundamental group identifies the
geometric subgroup; the unique `h` in the conclusion is precisely `w⁻¹ g w` in that subgroup.

Proof: (1) Geometric connectedness makes the geometric fibre connected. By
`thm-galois-torsor-h1`, represent a class by an M-torsor. By `thm-galois-lc-etale` its underlying
sheaf is a finite étale cover. Its nonempty fibre is a simply transitive M-set, by
`def-weil-pbc-finite-torsors`. By `thm-galois-fundamental` it is a finite continuous G-set.
(2) Choose p in this fibre and define f(g) by g p = p + f(g). Commutation of translations
with G proves the homomorphism law; commutativity of M proves independence of p and of the
representative. The open stabilizer proves continuity (`def-galois-fibre-functor`).
(3) Conversely a character gives the action g a = f(g) + a on M. The fundamental equivalence
transports the translations to a finite étale cover. The torsor corresponding to f under
`cor-galois-abelian-h1` identifies this cover with a locally nonempty torsor; full faithfulness
transports its torsor structure. The two constructions are inverse.
(4) By `lem-sc-torsor-h1`, addition of classes is contracted product. The fibre of the product
is the antidiagonal quotient of the two fibres; its monodromy is f + f'. The trivial torsor
has character zero. This upgrades the existing bijection to the asserted group isomorphism.
(5) Base-change compatibility in `thm-galois-fundamental` identifies the fibre of a pointed
pullback with the original fibre acted on through the induced fundamental-group map.
The torsor-class naturality in `thm-galois-torsor-h1` proves the pointed pullback square.
(6) For a Weil element w, `lem-wf-finite-etale-weil-transport` gives a natural bijection
from the fibre of the pullback along Phi^(deg w) to the original fibre, intertwining g
with w⁻¹ g w. Naturality for translations makes this bijection M-equivariant, so the
character of the pullback is f(w⁻¹ g w). Torsor-class naturality proves the cohomology formula.
(7) By `lem-wf-weil-group-exact-sequence`, changing w by a geometric element changes this
conjugation by an inner automorphism. Characters to abelian M kill inner conjugation.
This includes degree zero and every positive and negative integer degree. -/
theorem finiteConstantH1Pi1 (D : FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [GeometricallyConnected U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [ConnectedSpace U₀.left] [ConnectedSpace (D.geometricFiber U₀).left]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (G₀ : Type u) [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [CompactSpace G₀]
    [∀ P, MulAction G₀ ((fiber (s ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj P)]
    [IsFundamentalGroup (fiber (s ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) G₀]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] :
    ∃ e : Sheaf.H
        ((constantSheaf (D.geometricFiber U₀).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)) 1 ≃+ Additive (G →ₜ* Multiplicative M),
      (∀ c, (e c).toMul = EtaleTorsor.sheafHEquivContinuousMonoidHom M s G c) ∧
      (∀ (a : Aut (D.geometricFiber U₀).left) (ha : s ≫ a.hom = s)
          (P : EtaleTorsor M (D.geometricFiber U₀).left) (g : G),
        (e (EtaleTorsor.classH1 M _ ⟦P.pullback a.hom⟧)).toMul g =
          (e (EtaleTorsor.classH1 M _ ⟦P⟧)).toMul
            (fundamentalGroupMap (pullbackFiberIso a.hom s ≪≫
              eqToIso (congrArg (fun t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left => fiber t)
                ha)) G G g)) ∧
      (∀ (w : weilGroup U₀.hom (s ≫ pullback.fst U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) G₀)
          (P : EtaleTorsor M (D.geometricFiber U₀).left) (g : G),
        ∃! h : G,
          fundamentalGroupMap (pullbackFiberIso (pullback.fst U₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s) G G₀ h =
            w.val.1⁻¹ * fundamentalGroupMap (pullbackFiberIso (pullback.fst U₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) s) G G₀ g * w.val.1 ∧
          (e (EtaleTorsor.classH1 M _ ⟦P.pullback
            ((D.geometricFrobenius U₀) ^ (weilGroupDeg U₀.hom
              (s ≫ pullback.fst U₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) G₀ w).toAdd).hom⟧)).toMul g =
            (e (EtaleTorsor.classH1 M _ ⟦P⟧)).toMul h) :=
  sorry

end WeilConjectures
