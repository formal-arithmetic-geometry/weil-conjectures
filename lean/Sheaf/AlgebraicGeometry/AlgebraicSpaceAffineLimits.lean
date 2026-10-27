module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Affine inverse limits of algebraic spaces and eventual schematicity

Source: Stacks Project, Spaces Limits, Tags 07SF, 07SQ and 07SR, with Situation 084R
(blueprint: lem-sfb-space-affine-limits-schematic-stages).

The cone is limiting in fppf sheaves, not just in algebraic spaces. Base change is
indexed by `Over (op i)`, whose objects are exactly stages `j ≥ i`. The two equations
on its limiting cone specify the canonical comparison with the sheaf fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine inverse systems have algebraic-space limits with affine projections, commute
with arbitrary base change at a stage, and, for qcqs stages, detect schemes and affine
schemes eventually. Quasi-compactness is the existence of a quasi-compact scheme atlas;
quasi-separatedness is the existing absolute-diagonal predicate.
Source: Stacks Project, Spaces Limits, Tags 07SF, 07SQ, 07SR and Situation 084R
(blueprint: lem-sfb-space-affine-limits-schematic-stages).

Proof, following the ten steps of the node:
1. Fix an index and pass to its cofinal directed tail. Choose an étale scheme atlas U₀
   of Z₀ and its scheme relation R₀. Their pullbacks Uᵢ and Rᵢ are schemes because the
   transitions are affine. Use [lem-weil-pbc-limit-affine-transition] to form scheme
   limits U and R with affine projections. Pullback identities identify the two maps
   R → U as base changes of the étale maps R₀ → U₀. The relation axioms hold on test
   schemes coordinatewise; uniqueness of the relation witnesses gives compatibility.
2. By [lem-trf-etale-relation-quotient], U/R is an algebraic space. It is the fppf-sheaf
   limit: a compatible family of sections lifts to U over the single étale cover
   obtained from U₀, and two quotient sections with identical images lift locally to
   U with a compatible family of witnesses in Rᵢ, hence a witness in R.
3. Repeating at any index identifies the pullback of its atlas with U. Affine target
   locality [lem-sfb-space-affine-locality] gives affine projections. On test schemes,
   a map into Z ×_{Zᵢ} W is a map into W and a compatible tail family into Zⱼ with
   common image in Zᵢ. This gives the canonical base-change isomorphism, respecting
   both projections. Directedness extends a tail family uniquely to the full system.
4. Assume qcqs stages. Affine permanence gives Z qcqs. If Z is affine, choose U₀
   affine by [lem-trf-space-qc-finite-affine-atlas-refinement]. All Uᵢ and U are affine.
   Put Aᵢ = Γ(Zᵢ, O) and Cᵢ = Γ(Uᵢ, O). The two section-continuity lemmas
   [lem-sfb-space-limit-sections] and [lem-weil-pbc-limit-global-sections-colimit]
   identify their colimits with A = Γ(Z, O) and B = Γ(U, O).
5. Descend the étale A-algebra B to an étale A₀-algebra B₀ using
   [lem-weil-pbc-etale-algebra-filtered-colimit-descent], with its specified base-change
   isomorphism. It is finitely presented by the affine lfp criterion. The scheme
   theorem [lem-weil-pbc-descend-surjective] makes Spec Bᵢ → Spec Aᵢ surjective
   eventually, where Bᵢ = Aᵢ ⊗ B₀.
6. Lift finitely many generators of B₀ into some Cᵢ; eventual equality makes its
   finitely many relations vanish after increasing i. This gives Bᵢ → Cᵢ. The canonical
   map Zᵢ → Spec Aᵢ is constructed on its atlas by the scheme affine-target bijection
   [lem-weil-pbc-morphism-into-affine-scheme] and descended by sheaf uniqueness.
7. Set T₀ = Z₀ ×_{Spec A₀} Spec B₀. The resulting map U₀ → T₀ is étale, hence lfp,
   by [lem-trf-space-chartwise-etale-permanence]. Both spaces are qcqs. Its limit is
   the specified isomorphism from step 6, so
   [lem-sfb-space-limit-representable-isomorphism] makes Uᵢ → Tᵢ an isomorphism
   eventually.
8. Thus Zᵢ → Spec Aᵢ becomes affine after the surjective étale cover Spec Bᵢ.
   Affine target locality shows that Zᵢ is an affine scheme.
9. If Z is a scheme, choose a finite affine open cover. Descend it, including its
   covering condition, by [lem-sfb-space-limit-open-cover-descent]. Step 3 identifies
   each open with its tail limit. Steps 4–8 and directedness make all these finitely
   many opens affine at a common stage. Then [lem-pc-schemes-criterion] makes that
   stage a scheme. An empty cover descends to an empty stage, represented by Spec 0.
10. Any later stage is affine over the chosen stage. Affine representability makes it
    a scheme if that stage is a scheme, and affine if that stage is affine. This proves
    persistence at every later stage. -/
theorem exists_affine_limit_eventually_schematic
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (haff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), MapIsAffine (D.map a)) :
    ∃ c : Cone D,
      Nonempty (IsLimit ((ObjectProperty.ι IsAlgebraicSpace).mapCone c)) ∧
      (∀ i : Iᵒᵖ, MapIsAffine (c.π.app i)) ∧
      (((∀ i : Iᵒᵖ, ∃ (U : Over S) (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
          CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a) ∧
        (∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))) →
        ((c.pt.obj.obj.IsRepresentable →
          ∃ i : I, ∀ j : I, i ≤ j → (D.obj (op j)).obj.obj.IsRepresentable) ∧
        ((∃ U : Over S, IsAffine U.left ∧ Nonempty (yoneda.obj U ≅ c.pt.obj.obj)) →
          ∃ i : I, ∀ j : I, i ≤ j → ∃ U : Over S,
            IsAffine U.left ∧ Nonempty (yoneda.obj U ≅ (D.obj (op j)).obj.obj)))) ∧
      (∀ (i : I) (W : AlgebraicSpace S) (f : W ⟶ D.obj (op i)),
        ∃ b : Cone (Over.post (X := op i) (D ⋙ ObjectProperty.ι IsAlgebraicSpace) ⋙
            Over.pullback f.hom ⋙ Over.forget W.obj),
          Nonempty (IsLimit b) ∧
          ∃ e : b.pt ≅ Limits.pullback (c.π.app (op i)).hom f.hom,
            ∀ j : Over (op i),
              b.π.app j ≫ Limits.pullback.fst (D.map j.hom).hom f.hom =
                e.hom ≫ Limits.pullback.fst (c.π.app (op i)).hom f.hom ≫
                  (c.π.app j.left).hom ∧
              b.π.app j ≫ Limits.pullback.snd (D.map j.hom).hom f.hom =
                e.hom ≫ Limits.pullback.snd (c.π.app (op i)).hom f.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
