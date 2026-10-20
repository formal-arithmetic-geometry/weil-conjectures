/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CompactificationRefinementLocalizing
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.SixFunctorsBasics.BrownHypotheses
import Sheaf.Paper.CompactificationLocalizing
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import Mathlib.CategoryTheory.Yoneda
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.Paper.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Brown exceptional adjoints and compactification independence

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-existence,
det-sf-existence-brown.proof.md, parts (1)--(3); Stacks Tags 0A8F, 0A8G, 0A8D
(blueprint: det-sf-existence-brown).

All functors act on the recorded localizing closures in the ordinary derived categories
of internal modules. Comparisons are normalized by the existing open-adjunction refinement
map and the K-injective-normalized direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Push the canonical open refinement map along the coarse proper map, then undo the
canonical derived direct-image compositor. This is the specified map from the coarse
compact-support composite to the fine one, before any invertibility assertion.
Source: blueprint det-sf-existence-brown.proof.md (3), using the refinement construction
in det-sf-comp-coherence-cocycle, proof step 4
(blueprint: det-sf-existence-brown). -/
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ r K) ≫
    (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    eqToHom (congrArg
      (fun q ↦ (lowerStar Λ q).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K))
      r.hom.hom.hom_g)

/-- Brown representability on the localizing constructible closure gives exact exceptional
adjoints, with their adjunction-induced coherent shifts. The adjoints are unique among
counit-compatible natural isomorphisms. Their comparisons for different compactifications
are normalized by the canonical compact-support comparisons and satisfy identity and
cocycle laws. The source triangulation and sums are the standing Brown hypotheses; the
set of compact generators is explicitly required to lie in Dctf. The target triangulation
and the restriction-membership witnesses are conclusions, not extra assumptions.

Source: blueprint main-20261015, det-sf-existence-brown, statement and proof parts (1)--(3);
Stacks Tags 0A8F, 0A8G and 0A8D (blueprint: det-sf-existence-brown).

Proof:
1. The geometric setting makes Y qcqs (lem-weil-pbc-qcqs-over-affine). For every
compactification, det-sf-comp-coherence-single gives preservation of the localizing
closures, exactness and preservation of small sums. sk-lem-brown-hypotheses supplies
the target Brown structures. The assumed compact generators supply the source condition.
2. Apply lem-pc-brown-representability-right-adjoint to each restricted functor. For each N,
Hom(F(-),N) is cohomological and carries sums to products, hence is representable by Brown.
Yoneda assembles these representing objects into G, with natural Hom bijections F ⊣ G.
3. Transpose the shifted counit, obtaining G(N)[n] ≅ G(N[n]). Full faithfulness of Yoneda
(lem-galois-yoneda-fully-faithful) gives naturality. The transpose of the identity shift
is the counit; transposing successive shifts gives the sum shift by coherence for F.
The triangle identities give compatibility of both unit and counit with these shifts.
This is exactly Adjunction.rightAdjointCommShift, including zero and addition coherence.
4. Apply lem-sf-triangulated-right-adjoint with these compatible shifts: G is exact.
5. det-sp-unique-right-adjoint transposes the counits of two adjunctions to inverse natural
transformations. The adjunction bijection is injective, so the counit equation uniquely
determines the isomorphism, and also implies compatibility with every Hom bijection.
6. det-sf-comp-coherence-cocycle constructs the canonical F comparisons through any common
dense refinement, normalized by brownCompactificationRefinementMap. Restricting the ambient
comparisons along the fully faithful inclusions gives phi. Transfer one adjunction along
phi and apply step 5 to obtain gamma. Transposing its counit equation gives uniqueness.
For three compactifications, substitute the two counit equations and use naturality of
phi and its cocycle. The result is the counit equation for the third comparison; uniqueness
gives the gamma cocycle. The same calculation for identity phi gives identity gamma.
-/
theorem exists_brownExceptionalAdjoints
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    [(localizingClosureProEtale Λ X).IsTriangulated]
    [LocallySmall.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (_hgen : ∃ (I : Type (u + 1))
      (E : I → (localizingClosureProEtale Λ X).FullSubcategory),
      (∀ i, constantModelBoundedConstructible Λ X (E i).obj ∧
        DerivedCategory.finiteTorAmplitude _ (E i).obj) ∧
      (∀ i, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E) :
    ∃ (h : ∀ (c : Compactification.BoundaryCompactification f) K,
        localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
      (fun [triY : (localizingClosureProEtale Λ Y).IsTriangulated] ↦
        ∃ (G : Compactification.BoundaryCompactification f →
            ((localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory))
          (adj : ∀ c : Compactification.BoundaryCompactification f,
            localizingLowerShriek Λ c.obj.obj (h c) ⊣ G c),
          (∀ c, (fun [comm : (G c).CommShift ℤ] ↦
            (G c).IsTriangulated ∧ (adj c).CommShift ℤ)
              (comm := (adj c).rightAdjointCommShift ℤ)) ∧
          (∀ (c : Compactification.BoundaryCompactification f)
            (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory)
              (adjJ : localizingLowerShriek Λ c.obj.obj (h c) ⊣ J),
            ∃! e : G c ≅ J, ∀ N,
              (localizingLowerShriek Λ c.obj.obj (h c)).map (e.hom.app N) ≫
                adjJ.counit.app N = (adj c).counit.app N) ∧
          ∃ phi : ∀ c d : Compactification.BoundaryCompactification f,
              localizingLowerShriek Λ c.obj.obj (h c) ≅
                localizingLowerShriek Λ d.obj.obj (h d),
            (∀ (c : Compactification.BoundaryCompactification f)
              (d : Compactification.DenseBoundaryCompactification f)
              (r : d.obj ⟶ c) (K : (localizingClosureProEtale Λ X).FullSubcategory),
              ((phi c d.obj).hom.app K).hom = brownCompactificationRefinementMap Λ r K.obj) ∧
            (∀ c, phi c c = Iso.refl _) ∧
            (∀ c d e, phi c d ≪≫ phi d e = phi c e) ∧
            ∃ gamma : ∀ c d : Compactification.BoundaryCompactification f, G c ≅ G d,
              (∀ (c d : Compactification.BoundaryCompactification f)
                (N : (localizingClosureProEtale Λ Y).FullSubcategory),
                (localizingLowerShriek Λ d.obj.obj (h d)).map ((gamma c d).hom.app N) ≫
                  (adj d).counit.app N =
                    (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N) ∧
              (∀ (c d : Compactification.BoundaryCompactification f) (e : G c ≅ G d),
                (∀ N : (localizingClosureProEtale Λ Y).FullSubcategory,
                  (localizingLowerShriek Λ d.obj.obj (h d)).map (e.hom.app N) ≫
                  (adj d).counit.app N =
                    (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N) →
                e = gamma c d) ∧
              (∀ c, gamma c c = Iso.refl _) ∧
              (∀ c d e, gamma c d ≪≫ gamma d e = gamma c e))
        (triY := hY) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
