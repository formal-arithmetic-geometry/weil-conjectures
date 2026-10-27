module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FppfLocalOpenSubfunctorDescent

/-! # Parabolic quotient torsors and rational lifting over any field

Source: Milne, Algebraic Groups (2017), Theorem 25.9(b), printed p.546;
Theorem 5.28 and Sections 5(g), 8(a) for the quotient and torsor construction.
(blueprint: lem-sfb-field-parabolic-quotient-rational-lift)

The coequalizer below is the presheaf of right cosets. Its map to the representable
presheaf of Q, normalized on G, has the sheafification universal property. The big
fppf site over k restricts on affine tests to the stated site of k-algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth geometrically connected closed subgroup with proper represented fppf
coset sheaf is parabolic. Its canonical projection is a right torsor, has kernel P
on every test algebra, and is surjective on k-points. The action is an internal
left G-action, normalized by the multiplication of G. No assumption of infinitude,
perfectness, splitness, or algebraic closedness is imposed on k.

The arrow ηq and its equation on generators specify the canonical quotient map;
its bijection on maps to every fppf sheaf is the sheafification universal property.
Representable presheaves are fppf sheaves, so no additional sheaf hypothesis on Q
is needed. Properness includes finite type (universally closed implies quasi-compact).

Source: Milne, Theorem 25.9(b), printed p.546; Theorem 5.28, pp.104--105,
and Sections 5(g), 8(a).
(blueprint: lem-sfb-field-parabolic-quotient-rational-lift)

Proof, following all seven steps of the DAG:
1. Regard schemes as algebraic spaces (def-trf-scheme-algebraic-space). Their
   fpqc sheaf property (lem-a1-algebraic-space-fpqc-sheaf), together with
   lem-trf-fppf-covering-is-fpqc, gives fppf descent. Left multiplication respects
   right cosets, so descends to an action with unit, associativity and the displayed
   normalization. Apply lem-sfb-algebraic-group-homogeneous-quotient to G and P:
   affine G is separated, and the quotient is flat, surjective and finitely presented.
   Its coset-fibre formula gives inverse maps (g,p) ↦ (g,gp) and
   (g,h) ↦ (g,g⁻¹h). Pullback covers remain covers by
   lem-trf-fppf-covering-base-change. Thus every quotient section lifts locally;
   taking its local cosets and gluing identifies this quotient with the given Q,
   by the normalized sheafification universal property.
2. Evaluate the torsor isomorphism on (1,g) for any test algebra A. The equality
   q(g)=q(1) is equivalent to g being the image of a unique P(A)-point. Conversely
   right-coset invariance sends every P(A)-point to q(1), including for nonreduced A.
3. A greatest-rank split torus S in P exists: tangent injection bounds its rank
   (lem-sfb-affine-group-dual-number-calculus). By
   lem-sfb-split-torus-hom-matrices, an equal-rank closed inclusion of split tori
   is an isomorphism: its surjective Laurent-coordinate map forces a surjective
   square integer exponent matrix. Hence S is maximal. Apply
   lem-sfb-parabolic-prescribed-split-cocharacter to get λ with P=P_λ.
4. Apply lem-sfb-relative-dynamic-subgroups to conjugation by λ. Smoothness gives
   local finite presentation (def-sbc-smooth-morphisms), and affineness gives
   quasi-compactness and quasi-separatedness. With N=U_{-λ}, multiplication
   N × P → G is an open immersion and N contains the identity over k.
5. The restriction N → Q is a monomorphism by the torsor formula and injectivity
   of that open multiplication. Its pullback along G → Q is precisely N × P → G.
   Apply lem-trf-fppf-local-open-subfunctor-descent: N identifies with an open
   U in Q containing q(1), and the inverse followed by N → G is a section s.
6. If k is infinite and x is a k-point of Q, the open inverse image of U under
   g ↦ g⁻¹·x is nonempty, since x has an fppf-local lift. By
   lem-sfb-infinite-field-reductive-rational-density choose a k-point a in it.
   Then y=a⁻¹·x lies in U(k), and a s(y) maps to x, also over imperfect k.
7. If k is finite, pull back q over x using lem-trf-fppf-covering-base-change.
   Its fibre is an fppf P-torsor by the base-changed kernel-pair isomorphism.
   The group P is smooth, geometrically connected, affine and finite type.
   Apply lem-sfb-finite-field-connected-group-torsor-point (Lang) and project its
   k-point to a lift in G(k). The finite and infinite cases exhaust all fields. -/
theorem field_parabolic_quotient_rational_lift
    {k : Type u} [Field k] (G P : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (i : P ⟶ G) [IsClosedSubgroupScheme i.hom.hom] [Smooth P.X.hom]
    (hP : ConnectedSpace
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P).X.left)
    (Q : Over (Spec (.of k))) [IsProper Q.hom] (q : G.X ⟶ Q)
    (ηq : coequalizer (yoneda.map (fst G.X P.X))
      (yoneda.map (fst G.X P.X * (snd G.X P.X ≫ i.hom.hom))) ⟶ yoneda.obj Q)
    (hηq : coequalizer.π _ _ ≫ ηq = yoneda.map q)
    (hquot : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) :
    (∃ a : ModObj G.X Q, μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul) ∧
      Flat q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left ∧
      QuasiCompact q.left ∧ QuasiSeparated q.left ∧
      (∃ e : G.X ⊗ P.X ≅ pullback q q,
        e.hom ≫ pullback.fst q q = fst G.X P.X ∧
        e.hom ≫ pullback.snd q q = fst G.X P.X * (snd G.X P.X ≫ i.hom.hom)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (g : StandardGroupSchemes.affine k A ⟶ G.X),
        g ≫ q = (1 : StandardGroupSchemes.affine k A ⟶ G.X) ≫ q ↔
          g ∈ Set.range (fun p : StandardGroupSchemes.affine k A ⟶ P.X ↦
            p ≫ i.hom.hom)) ∧
      Function.Surjective (fun g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X ↦ g ≫ q) := by
  sorry

end AlgebraicGeometry
