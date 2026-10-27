/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Effective fppf descent of quasi-coherent modules on algebraic spaces

Source: Stacks Project, Tag 04W8, specialized to fppf coverings using Tag 0DFQ
(blueprint: lem-sfb-space-fppf-qcoh-descent).

The statement uses the equivalent effectivity and unique-descent-of-maps formulation.
Overlap objects are the actual sheaf fibre products. The triple equation is tested
on every algebraic space mapping to the three overlaps with the specified projections;
this includes the triple fibre product itself. All pullback comparisons use the
existing tensor-normalized composition isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pull an overlap transition to a test of a triple overlap, retaining the given legs.
Source: Stacks, Tag 04W8, descent datum and canonical composition identifications
(blueprint: lem-sfb-space-fppf-qcoh-descent). -/
def qcohDescentTransitionOn {S : Scheme.{u}} {A B R T : AlgebraicSpace S}
    (M : A.Modules) (N : B.Modules) (p : R ⟶ A) (q : R ⟶ B)
    (φ : (moduleTensorPullback p).obj M ≅ (moduleTensorPullback q).obj N)
    (r : T ⟶ R) (a : T ⟶ A) (b : T ⟶ B) (ha : r ≫ p = a) (hb : r ≫ q = b) :
    (moduleTensorPullback a).obj M ≅ (moduleTensorPullback b).obj N :=
  (eqToIso (congrArg (fun f ↦ (moduleTensorPullback f).obj M) ha)).symm ≪≫
    ((moduleTensorComposition r p).app M).symm ≪≫
    (moduleTensorPullback r).mapIso φ ≪≫ (moduleTensorComposition r q).app N ≪≫
    eqToIso (congrArg (fun f ↦ (moduleTensorPullback f).obj N) hb)

/-- The canonical overlap transition for the pullbacks of a global module.
The second projection is the actual second projection of the underlying sheaf pullback.
Source: Stacks, Tag 04W8, canonical functor, and Tag 03D7, tensor composition
(blueprint: lem-sfb-space-fppf-qcoh-descent). -/
def qcohCanonicalDescentTransition {S : Scheme.{u}} {A B X : AlgebraicSpace S}
    (f : A ⟶ X) (g : B ⟶ X) (M : X.Modules) :
    (moduleTensorPullback (enlargedFibreProductFst f g)).obj
        ((moduleTensorPullback f).obj M) ≅
      (moduleTensorPullback
        (ObjectProperty.homMk (pullback.snd f.hom g.hom) : enlargedFibreProduct f g ⟶ B)).obj
        ((moduleTensorPullback g).obj M) :=
  (moduleTensorComposition (enlargedFibreProductFst f g) f).app M ≪≫
    eqToIso (congrArg (fun h ↦ (moduleTensorPullback h).obj M)
      (ObjectProperty.hom_ext _ (pullback.condition (f := f.hom) (g := g.hom)))) ≪≫
    ((moduleTensorComposition
      (ObjectProperty.homMk (pullback.snd f.hom g.hom) : enlargedFibreProduct f g ⟶ B)
      g).app M).symm

/-- Every quasi-coherent cocycle datum for a small fppf covering is effective, and
compatible maps between pullbacks of global quasi-coherent modules descend uniquely.
The specified isomorphisms identify the given, unrefined overlap transitions exactly.
No quasi-compactness, separatedness, Noetherian or finite-generation assumption occurs.
Source: Stacks, Tag 04W8 (proposition-fpqc-descent-quasi-coherent), fppf case via Tag 0DFQ
(blueprint: lem-sfb-space-fppf-qcoh-descent).

Proof:
1. Tensor pullback preserves quasi-coherence by
   lem-sfb-space-module-pullback-quasicoherent. The normalized composition maps of
   def-sfb-space-module-tensor-composition send c tensor (d tensor m) to
   c times r-sharp(d) tensor m. Both associations of three tensors give the same
   product; the unit is multiplication. These formulas give all coherence equations.
   The scheme Zariski/etale equivalence compares tensor pullbacks for every scheme map.
2. Choose surjective etale scheme atlases A_i of the covering members. Their composites
   cover X by lem-sfb-space-fppf-covering-calculus. For every scheme test T to X,
   B_i(T) = T times_X A_i is a scheme by the representable diagonal, even when T to X
   is not etale. The maps B_i(T) to T form a scheme fppf, hence fpqc, cover.
3. Pull the given modules and transitions to B_i(T). Their cocycle is the pullback of
   the given triple equation. Scheme fpqc descent, lem-pc-fpqc-descent, gives H_T and
   specified identifications theta_Ti with these modules, preserving the transitions.
4. For a scheme map f from T' to T over X, descend the compatible covered isomorphisms
   theta_T'i inverse followed by the pullback of theta_Ti. Full faithfulness gives
   c_f : f-star H_T isomorphic to H_T'. The inverse descends too. On the cover,
   cancellation of theta_T'i proves the identity and composition laws for c_f;
   faithfulness gives those laws globally, including non-etale scheme tests.
5. Pull maps of data to B_i(T), descend uniquely, and use faithfulness for their
   compatibility with c_f, identities and composition. Restricting (H_T,c_f) to etale
   charts, lem-sfb-space-qcoh-cartesian-chart-family assembles a quasi-coherent B(xi)
   and its maps, with compatible chart isomorphisms rho_U to H_U.
6. Compare on an arbitrary scheme test T by an etale atlas U to X. On W = T times_X U,
   with maps a to U and b to T, use c_b inverse composed with c_a and a-star rho_U.
   On W times_T W the chart compatibility on U times_X U and the composition law for
   c make both maps equal. Scheme descent gives lambda_T : t-star B(xi) isomorphic
   to H_T, natural in T and xi. On etale charts it agrees with rho_T by uniqueness.
7. For an etale chart V of X_i, pull to B_j(V). The inverse of phi_ij composed with
   theta_Vj identifies H_V with v-star M_i, since the compatibility equation is
   phi_ik inverse composed with phi_jk equals phi_ij inverse. Descend to eta_V.
   Faithfulness gives compatibility in V; eta_V composed with lambda_V therefore
   assembles to alpha_i : q_i-star B(xi) isomorphic to M_i, naturally in xi.
8. Test compatibility of alpha_i and alpha_j on charts V of X_i times_X X_j and their
   covers B_k(V). Both maps agree by phi_ik = phi_ij followed by phi_jk. Scheme descent
   faithfulness and chart faithfulness give the required overlap equation globally.
9. For a global M, scheme descent applied to its pullbacks gives beta_T : t-star M
   isomorphic to H_T(K(M)), preserving theta_Ti. Uniqueness makes these compatible
   and they assemble to beta : M isomorphic to B(K(M)). On covered charts the formulas
   cancel, giving alpha_K(M) composed with K(beta_M) equal to the identity. Thus a
   compatible local map descends by conjugating B of that map by beta; any other map
   agrees by scheme and chart faithfulness. Alpha gives effectivity of every datum.
10. For empty X, all members are empty. The empty covering forces the module category
    on each such space to have just the zero module and its unique map. Both assertions
    hold also for the empty index set. For nonempty X the covering index cannot be
    empty; empty members contribute only zero-module data. No finiteness is used. -/
theorem space_fppf_qcoh_descent {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S}
    (q : ∀ i : I, Xᵢ i ⟶ X) (hq : IsFppfCover q) :
    (∀ (Mᵢ : ∀ i : I, (Xᵢ i).QCoh)
      (φ : ∀ i j : I,
        (moduleTensorPullback (enlargedFibreProductFst (q i) (q j))).obj (Mᵢ i).obj ≅
          (moduleTensorPullback
            (ObjectProperty.homMk (pullback.snd (q i).hom (q j).hom) :
              enlargedFibreProduct (q i) (q j) ⟶ Xᵢ j)).obj (Mᵢ j).obj),
      (∀ (i j k : I) (T : AlgebraicSpace S)
        (a : T ⟶ Xᵢ i) (b : T ⟶ Xᵢ j) (c : T ⟶ Xᵢ k)
        (rᵢⱼ : T ⟶ enlargedFibreProduct (q i) (q j))
        (rⱼₖ : T ⟶ enlargedFibreProduct (q j) (q k))
        (rᵢₖ : T ⟶ enlargedFibreProduct (q i) (q k))
        (hᵢⱼ₁ : rᵢⱼ ≫ enlargedFibreProductFst (q i) (q j) = a)
        (hᵢⱼ₂ : rᵢⱼ ≫ ObjectProperty.homMk (pullback.snd (q i).hom (q j).hom) = b)
        (hⱼₖ₁ : rⱼₖ ≫ enlargedFibreProductFst (q j) (q k) = b)
        (hⱼₖ₂ : rⱼₖ ≫ ObjectProperty.homMk (pullback.snd (q j).hom (q k).hom) = c)
        (hᵢₖ₁ : rᵢₖ ≫ enlargedFibreProductFst (q i) (q k) = a)
        (hᵢₖ₂ : rᵢₖ ≫ ObjectProperty.homMk (pullback.snd (q i).hom (q k).hom) = c),
        qcohDescentTransitionOn (Mᵢ i).obj (Mᵢ k).obj _ _ (φ i k)
            rᵢₖ a c hᵢₖ₁ hᵢₖ₂ =
          qcohDescentTransitionOn (Mᵢ i).obj (Mᵢ j).obj _ _ (φ i j)
              rᵢⱼ a b hᵢⱼ₁ hᵢⱼ₂ ≪≫
            qcohDescentTransitionOn (Mᵢ j).obj (Mᵢ k).obj _ _ (φ j k)
              rⱼₖ b c hⱼₖ₁ hⱼₖ₂) →
      ∃ (M : X.QCoh) (α : ∀ i : I, (moduleTensorPullback (q i)).obj M.obj ≅ (Mᵢ i).obj),
        ∀ i j : I,
          qcohCanonicalDescentTransition (q i) (q j) M.obj ≪≫
              (moduleTensorPullback
                (ObjectProperty.homMk (pullback.snd (q i).hom (q j).hom) :
                  enlargedFibreProduct (q i) (q j) ⟶ Xᵢ j)).mapIso (α j) =
            (moduleTensorPullback (enlargedFibreProductFst (q i) (q j))).mapIso (α i) ≪≫
              φ i j) ∧
    (∀ (M N : X.QCoh)
      (a : ∀ i : I,
        (moduleTensorPullback (q i)).obj M.obj ⟶ (moduleTensorPullback (q i)).obj N.obj),
      (∀ i j : I,
        (moduleTensorPullback (enlargedFibreProductFst (q i) (q j))).map (a i) ≫
            (qcohCanonicalDescentTransition (q i) (q j) N.obj).hom =
          (qcohCanonicalDescentTransition (q i) (q j) M.obj).hom ≫
            (moduleTensorPullback
              (ObjectProperty.homMk (pullback.snd (q i).hom (q j).hom) :
                enlargedFibreProduct (q i) (q j) ⟶ Xᵢ j)).map (a j)) →
      ∃! f : M.obj ⟶ N.obj, ∀ i : I, (moduleTensorPullback (q i)).map f = a i) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
