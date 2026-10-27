module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Connected.Clopen

/-!
# Affine normal quotients and their exact sequences

Source: Milne, Algebraic Groups (2017), Theorem 5.28, Propositions 5.24--5.29,
Theorem 5.55, Proposition 5.59 and Section 5(j)
(blueprint: lem-sfb-affine-normal-quotient-geometry).

The quotient presentation retains its actual quotient map. Its coequalizer is the
pointwise coset presheaf, and its universal arrow specifies the fppf sheafification.
Subgroups are compared by their images on all test schemes, so presentations differing
by an isomorphism describe the same subgroup. The last clause realizes both quotients
of a normal inclusion on the same representing group, with the prescribed maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The presentation of the fppf quotient of a group scheme by a specified kernel.
The kernel square is scheme-theoretic. The displayed torsor isomorphism has first
projection g and second projection gn. The coequalizer is therefore the presheaf
of right cosets, and precomposition with its displayed unit is the sheafification
universal property. Local surjectivity uses the actual fppf topology.

Source: Milne, Algebraic Groups (2017), Propositions 5.24--5.27 and Section 5(j)
(blueprint: lem-sfb-affine-normal-quotient-geometry). -/
def IsFppfGroupQuotient {B : Scheme.{u}} {N G Q : Grp (Over B)}
    (i : N ⟶ G) (q : G ⟶ Q) : Prop :=
  IsPullback i.hom.hom (toUnit N.X) q.hom.hom η[Q.X] ∧
  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over B) (yoneda.map q.hom.hom) ∧
  Presheaf.IsSheaf (Scheme.fppfTopology.over B) (yoneda.obj Q.X) ∧
  (∃ e : G.X ⊗ N.X ≅ pullback q.hom.hom q.hom.hom,
    e.hom ≫ pullback.fst _ _ = fst G.X N.X ∧
    e.hom ≫ pullback.snd _ _ =
      lift (fst G.X N.X) (snd G.X N.X ≫ i.hom.hom) ≫ μ[G.X]) ∧
  ∃ ηq : coequalizer (yoneda.map (fst G.X N.X))
      (yoneda.map (lift (fst G.X N.X) (snd G.X N.X ≫ i.hom.hom) ≫ μ[G.X])) ⟶
      yoneda.obj Q.X,
    coequalizer.π _ _ ≫ ηq = yoneda.map q.hom.hom ∧
    ∀ Z : Sheaf (Scheme.fppfTopology.over B) (Type u),
      Function.Bijective (fun f : yoneda.obj Q.X ⟶ Z.obj ↦ ηq ≫ f)

/-- Quotient geometry for a normal closed subgroup of an affine finite type group.

Source: Milne, Algebraic Groups (2017), Theorem 5.28, Propositions 5.24--5.29,
Theorem 5.55 (p.113), Proposition 1.62 (p.24), Proposition 5.59 (p.114),
and Section 5(j) (pp.116--119)
(blueprint: lem-sfb-affine-normal-quotient-geometry).

Proof plan, following the eleven steps of the DAG node:
1. Realize N as the kernel of a finite dimensional representation. Factor this
   representation through its affine faithfully flat image Q (the representation-kernel
   and flat-image lemmas). Its kernel remains N on every algebra of points.
2. Finite type over k makes both coordinate rings Noetherian. The coordinate algebra of G
   is finite type over that of Q and hence finitely presented. The resulting map is an
   fppf cover, including after arbitrary base change.
3. The map from cosets to Q is injective and locally surjective. Representable fpqc
   descent and the local-bijection criterion identify Q with its fppf sheafification.
   The torsor inverse sends (g,h) to (g,g⁻¹h).
4. The torsor and its sheaf universal property persist under every field extension.
   They identify the quotient maps after base change.
5. Smoothness descends along the flat finitely presented surjection G → Q. Geometric
   connectedness descends by surjectivity after passing to an algebraic closure.
6. For a closed S in Q form P = G ×[Q] S. It is closed, affine, finite type, and its
   projection to S is an fppf cover. The fibre of the identity is still N, hence P/N = S.
7. For a closed subgroup H containing N, factor H → Q by the flat-image lemma through a
   faithfully flat map onto a closed subgroup I of Q; it is finitely presented as in
   step 2. If g maps into I, lift locally to h in H; then g⁻¹h lies in N ⊆ H. Membership
   descends by representable fpqc descent along the monomorphism H → G, so q⁻¹(I) = H.
   The same local lifts show that q⁻¹(S) maps onto S, so the two constructions are inverse.
8. Membership descends along subgroup monomorphisms. Local lifts and common fppf
   refinements therefore preserve and reflect inclusions and normal inclusions.
9. For S₁ normal in S₀, the composite P₀ → S₀ → S₀/S₁ has kernel P₁ and is locally
   surjective. Its coset sheaf is both quotients, with the stated identical target map.
10. If N and S are smooth, the base changed smooth affine N-torsor P → S is smooth by
    torsor representability; compose with the smooth structural map of S.
11. If N and S are also connected, the identity section makes N geometrically connected.
    Every geometric fibre of P → S is a translate of N after an fppf lift. Connected
    fibres and the quotient topology for a flat quasi-compact surjection imply that P
    is connected. Uses the rational-point criterion, the algebraically closed residue
    field criterion, faithful-flat base change, and connected-preimage quotient topology.
-/
theorem affine_normal_quotient_geometry
    {k : Type u} [Field k] (N G : Grp (Over (Spec (.of k))))
    (i : N ⟶ G)
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom] :
    ∃ (Q : Grp (Over (Spec (.of k)))) (q : G ⟶ Q),
      IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
      IsFppfGroupQuotient i q ∧
      q.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        IsFppfGroupQuotient
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.map i)
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.map q)) ∧
      (Smooth G.X.hom → Smooth Q.X.hom) ∧
      (GeometricallyConnected G.X.hom → GeometricallyConnected Q.X.hom) ∧
      (∀ (S : Grp (Over (Spec (.of k)))) (j : S ⟶ Q),
        IsClosedSubgroupScheme j.hom.hom →
        ∃ (P : Grp (Over (Spec (.of k)))) (p : P ⟶ G) (h : P ⟶ S) (a : N ⟶ P),
          IsAffine P.X.left ∧ LocallyOfFiniteType P.X.hom ∧ QuasiCompact P.X.hom ∧
          IsClosedSubgroupScheme p.hom.hom ∧
          IsPullback p.hom.hom h.hom.hom q.hom.hom j.hom.hom ∧
          a ≫ p = i ∧ IsFppfGroupQuotient a h ∧
          (IsNormalSubgroupScheme j.hom.hom → IsNormalSubgroupScheme p.hom.hom) ∧
          (Smooth N.X.hom → ConnectedSpace N.X.left →
            Smooth S.X.hom → ConnectedSpace S.X.left →
            Smooth P.X.hom ∧ ConnectedSpace P.X.left)) ∧
      (∀ (H : Grp (Over (Spec (.of k)))) (b : H ⟶ G),
        IsClosedSubgroupScheme b.hom.hom →
        (∃ a : N ⟶ H, a ≫ b = i) →
        ∃ (S : Grp (Over (Spec (.of k)))) (j : S ⟶ Q) (h : H ⟶ S),
          IsClosedSubgroupScheme j.hom.hom ∧
          IsPullback b.hom.hom h.hom.hom q.hom.hom j.hom.hom) ∧
      (∀ (S₀ S₁ : Grp (Over (Spec (.of k)))) (j₀ : S₀ ⟶ Q) (j₁ : S₁ ⟶ Q),
        IsClosedSubgroupScheme j₀.hom.hom → IsClosedSubgroupScheme j₁.hom.hom →
        ((∀ (T : Over (Spec (.of k))) (s : T ⟶ S₀.X),
          ∃ t : T ⟶ S₁.X, t ≫ j₁.hom.hom = s ≫ j₀.hom.hom) ↔
        (∀ (T : Over (Spec (.of k))) (g : T ⟶ G.X),
          (∃ s : T ⟶ S₀.X, s ≫ j₀.hom.hom = g ≫ q.hom.hom) →
          ∃ t : T ⟶ S₁.X, t ≫ j₁.hom.hom = g ≫ q.hom.hom))) ∧
      (∀ (S₀ S₁ P₀ P₁ : Grp (Over (Spec (.of k))))
        (j₀ : S₀ ⟶ Q) (j₁ : S₁ ⟶ Q) (s : S₁ ⟶ S₀)
        (p₀ : P₀ ⟶ G) (p₁ : P₁ ⟶ G) (h₀ : P₀ ⟶ S₀) (h₁ : P₁ ⟶ S₁)
        (t : P₁ ⟶ P₀),
        IsClosedSubgroupScheme j₀.hom.hom → IsClosedSubgroupScheme j₁.hom.hom →
        IsPullback p₀.hom.hom h₀.hom.hom q.hom.hom j₀.hom.hom →
        IsPullback p₁.hom.hom h₁.hom.hom q.hom.hom j₁.hom.hom →
        s ≫ j₀ = j₁ → t ≫ p₀ = p₁ → t ≫ h₀ = h₁ ≫ s →
        (IsNormalSubgroupScheme s.hom.hom ↔ IsNormalSubgroupScheme t.hom.hom) ∧
        (IsNormalSubgroupScheme s.hom.hom →
          ∃ (R : Grp (Over (Spec (.of k)))) (r : S₀ ⟶ R),
            IsAffine R.X.left ∧ LocallyOfFiniteType R.X.hom ∧ QuasiCompact R.X.hom ∧
            IsFppfGroupQuotient s r ∧ IsFppfGroupQuotient t (h₀ ≫ r))) := by
  sorry

end AlgebraicGeometry
