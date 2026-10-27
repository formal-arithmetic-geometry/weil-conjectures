/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.LinearAlgebra.RootDatumLatticeEmbedding
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer

/-! # An isomorphism criterion using a torus and signed simple root groups

Source: Milne, Algebraic Groups (2017), 23.24 and the paragraph completing 23.18,
printed p.492; Proposition 23.5, pp.485--486.
(blueprint: lem-sfb-torus-simple-root-isomorphism-criterion)

The root datum is the actual character/cocharacter datum of the target, pinned by
its composition pairing and nonzero adjoint character weights. Boolean true denotes
positive sign and false negative sign. Lifted root groups and their restriction
isomorphisms are given over the ambient groups, including on nonreduced test algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A surjective reductive homomorphism is an isomorphism if its maximal-torus
restriction is an isomorphism and every signed simple root group has an isomorphic
lift with the pulled-back root character. No kernel reducedness is assumed.

Source: Milne, 23.24 and the final paragraph completing 23.18, p.492, generalized
from the graph projection to a surjective reductive homomorphism; Proposition 23.5.
(blueprint: lem-sfb-torus-simple-root-isomorphism-criterion)

Proof plan:
1. Apply lem-sfb-affine-homomorphism-flat-image. The closed image is surjective
   onto G. By sbc-lem-smooth-geometrically-reduced, G is reduced. The image ideal
   lies in every prime, hence in the zero nilradical (def-weil-closed-immersion,
   def-pc-reduced-scheme). Thus f is faithfully flat on coordinate algebras.
2. The scheme-theoretic kernel K is normal and K intersect S is ker(a), the trivial
   group scheme. Apply lem-sfb-reductive-normal-subgroup-torus-finiteness: K is finite.
3. Apply lem-sfb-isogeny-root-power-laws. The root bijection b has positive
   characteristic-exponent powers e with a*(b(delta)) = e(delta) delta and the
   corresponding coroot formula; K is central iff all these powers are one.
4. For each signed simple root, the closed lifted Ga injects its tangent line into
   Lie(H). Its character is a*(signed alpha), by the displayed conjugation law.
   The one-dimensional weight and uniqueness assertions of
   lem-sfb-reductive-rank-one-reflections and
   lem-sfb-reductive-root-subgroup-parametrizations identify the lift with that root
   group. Target reducedness makes its exponent one, and identifies its coroot.
5. Apply lem-sfb-root-datum-lattice-embedding to remove the central directions and
   lem-sfb-root-base-rational-integral-spans to obtain the rational root-pairing base.
6. Apply lem-sfb-root-base-reflection-induction to Q(beta): a*(beta) is a source
   root. Negation preserves Q; step 4 gives the simple case. Naturality of the
   character/cocharacter pairing and the coroot formula identify source reflection
   with pullback of target simple reflection. Thus Q holds for every root.
   The root-power formula now has delta and e(delta) delta both source roots, so
   source reducedness forces e(delta) = 1 for every delta.
7. By lem-sfb-isogeny-root-power-laws K is central. The scheme-theoretic equality
   from lem-sfb-reductive-torus-self-centralizer puts K inside S, including its
   infinitesimal part. Therefore K = K intersect S = 1.
8. Apply lem-sfb-faithfully-flat-group-quotient-universal to the identity of H to
   obtain j with jf = id. Its uniqueness gives fj = id. These are group-scheme
   inverse equations. With an empty base, reflection induction and all exponent
   assertions are vacuous; centrality and this inverse argument still apply.
-/
theorem torus_simpleRoot_isomorphism_criterion
    {F : Type u} [Field F] [IsAlgClosed F]
    (H G S T : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iS : S ⟶ H) (iT : T ⟶ G)
    (hS : ReductiveTorusCentralizer.IsMaximalTorus iS)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplitS : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r))
    (hsplitT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (f : H ⟶ G) (hf : Surjective f.hom.hom.left)
    (a : S ≅ T) (ha : iS ≫ f = a.hom ≫ iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X)
    (hconj : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (base : P.Base) (hred : P.IsReduced)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (U : Φ → Grp (Over (Spec (.of F)))) (iU : ∀ β, U β ⟶ G)
    (hU : ∀ β,
      IsClosedSubgroupScheme (iU β).hom.hom ∧ Smooth (U β).X.hom ∧
      ConnectedSpace (U β).X.left ∧
      @TorusCharacterTangent.IsStable F _ T G aG _ (iU β) ∧
      (GrpObj.differential (iU β).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG β.val.toMul ∧
      Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U β))
    (hlift : ∀ (α : base.support) (ε : Bool),
      ∃ (β : Φ), β.val = (if ε then α.val.val else -α.val.val) ∧
        ∃ (V : Grp (Over (Spec (.of F)))) (iV : V ⟶ H)
          (v : Grp.mk (StandardGroupSchemes.additive F) ≅ V) (e : V ≅ U β),
          IsClosedSubgroupScheme iV.hom.hom ∧ Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧
          iV ≫ f = e.hom ≫ iU β ∧
          ∀ (A : Type u) [CommRing A] [Algebra F A]
            (s : StandardGroupSchemes.affine F A ⟶ S.X) (x : A),
            (s ≫ iS.hom.hom) *
                (TorusCharacterTangent.additiveParameterPoint F x ≫ v.hom.hom.hom ≫ iV.hom.hom) *
                (s ≫ iS.hom.hom)⁻¹ =
              TorusCharacterTangent.additiveParameterPoint F
                  (TorusCharacterTangent.multiplicativePointCoordinate F
                    (s ≫ a.hom.hom.hom ≫ β.val.toMul.hom.hom) * x) ≫
                v.hom.hom.hom ≫ iV.hom.hom) :
    IsIso f := by
  sorry

end AlgebraicGeometry
