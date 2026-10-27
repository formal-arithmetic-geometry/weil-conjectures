/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackPointTopology

/-! # Finite inertia and a flat locally quasi-finite affine presentation

Source: Stacks Project, `stacks-morphisms.tex`, Tag 0DU4 (lemma-etale-local-quasi-DM-at-x),
with Tag 0CL0, Tag 06MF and `spaces-morphisms.tex`, Tag 03XX
(blueprint: lem-sfb-finite-inertia-flat-quasifinite-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The arrow represented by a point of the self relation, retaining the comparison
isomorphism of its actual 2-fibre-product object and both endpoint identifications.
Source: Stacks Project, `algebraic.tex`, Tag 04T4, the self-relation construction
(blueprint: lem-sfb-finite-inertia-flat-quasifinite-presentation). -/
def moduliSelfRelationArrow {S : Scheme.{u}} {U R : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (s t : R ⟶ U)
    (E : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct p p))
    (α : ModuliTwoIso (E.comp (moduliTwoFiberFst p p))
      (discreteModuliMap (yoneda.map s)))
    (β : ModuliTwoIso (E.comp (moduliTwoFiberSnd p p))
      (discreteModuliMap (yoneda.map t)))
    {T : Over S} (r : T ⟶ R) :
    p.obj (CostructuredArrow.mk (yoneda.map (r ≫ s))) ⟶
      p.obj (CostructuredArrow.mk (yoneda.map (r ≫ t))) :=
  p.map (α.val.inv.app (CostructuredArrow.mk (yoneda.map r))) ≫
    (E.obj (CostructuredArrow.mk (yoneda.map r))).obj.hom ≫
      p.map (β.val.hom.app (CostructuredArrow.mk (yoneda.map r)))

/-- Finite inertia yields a pointed affine flat locally finitely presented scheme chart
whose self relation is a separated locally quasi-finite scheme groupoid.
Source: Stacks Project, `stacks-morphisms.tex`, Tag 0DU4, first proof paragraph,
using Tags 0CL0, 06MF and `spaces-morphisms.tex`, Tag 03XX
(blueprint: lem-sfb-finite-inertia-flat-quasifinite-presentation).

Proof, following the six steps of the node:
1. On each scheme test finite inertia is quasi-finite by pqf-lem-finite-qf, hence
locally quasi-finite by pqf-lem-qf-locqf-qc, also after an etale chart by
lem-a1-scheme-lqf-etale-source-locality. It is proper and separated by
lem-weil-pbc-finite-proper and def-weil-proper-morphism. Apply
lem-sfb-inertia-locally-quasifinite-diagonal and
lem-sfb-separated-source-finite-inertia-target to the structural map: the diagonal
is locally quasi-finite and separated; the stack itself need not be separated.
2. Use lem-sfb-quasidm-flat-locally-quasifinite-atlas and a field-extension lift of
x to its atlas. Restrict to an affine open through the lifted point. The restriction
is representable by lem-sfb-stack-diagonal-space-source-representability, flat and
locally finitely presented by lem-sfb-stack-chartwise-smooth-etale-calculus and
lem-weil-pbc-open-immersion-etale, and locally quasi-finite on scheme tests by
lem-a1-space-open-chart-tests. No global surjectivity is required.
3. The self relation is an algebraic space by lem-sfb-representable-pullback-over-space.
Its projections inherit flatness and local finite presentation by the chartwise
base-change calculus. The scheme-test definition also gives local quasi-finiteness.
4. By lem-sfb-groupoid-diagonal-two-pullback-identities, its map to U times U is a
base change of the stack diagonal. Affineness of U and
lem-weil-pbc-affine-source-morphism-separated, together with
lem-sfb-stack-separation-compactness-permanence, make both projections separated.
5. Apply lem-a1-separated-locally-qf-space-representable to a projection to U.
Transport both projections and their properties to the representing scheme using
lem-sfb-space-local-properties-chart-test. No quasi-compactness is needed.
6. On every test, a self-relation point is a triple (a,b,alpha). Identity, inverse
and composition are (a,a,1), (b,a,alpha inverse), and composition of the displayed
isomorphisms. Yoneda and the fibre-groupoid laws give def-a1-groupoid-scheme.
The final compatibility equation records this composition under the equivalence;
identity and inverse are consequently the unique canonical ones as well.
-/
theorem finite_inertia_flat_quasifinite_presentation
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection F)) :
    ∀ x : ModuliPoints F,
      ∃ (U : Over (Spec (CommRingCat.of k)))
        (p : BasedFunctor (discreteModuli (yoneda.obj U)) F)
        (u : U.left),
        IsAffine U.left ∧
        moduliPointMap p (Quot.mk _
          ⟨CostructuredArrow.mk (yoneda.map
            (Over.homMk (U.left.fromSpecResidueField u) rfl :
              Over.mk (U.left.fromSpecResidueField u ≫ U.hom) ⟶ U)),
            ⟨U.left.residueField u, inferInstance, ⟨Iso.refl _⟩⟩⟩) = x ∧
        IsRepresentableByAlgebraicSpaces p ∧
        ModuliSpaceTest
          (fun (X Y : Scheme.{u}) (f : X ⟶ Y) ↦
            Flat f ∧ LocallyOfFinitePresentation f) p ∧
        ∃ (R : Over (Spec (CommRingCat.of k)))
          (s t : R ⟶ U)
          (E : BasedFunctor
            (discreteModuli (yoneda.obj R))
            (moduliTwoFiberProduct p p))
          (α : ModuliTwoIso (E.comp (moduliTwoFiberFst p p))
            (discreteModuliMap (yoneda.map s)))
          (β : ModuliTwoIso (E.comp (moduliTwoFiberSnd p p))
            (discreteModuliMap (yoneda.map t)))
          (e : U.left ⟶ R.left)
          (i : R.left ⟶ R.left)
          (c : pullback s.left t.left ⟶ R.left),
          E.toFunctor.IsEquivalence ∧
          IsGroupoidScheme s.left t.left e i c ∧
          IsSeparated s.left ∧ IsSeparated t.left ∧
          Flat s.left ∧ Flat t.left ∧
          LocallyOfFinitePresentation s.left ∧
          LocallyOfFinitePresentation t.left ∧
          Scheme.Hom.IsLocallyQuasiFinite s.left ∧
          Scheme.Hom.IsLocallyQuasiFinite t.left ∧
          ∀ (T : Over (Spec (CommRingCat.of k))) (a b d : T ⟶ R)
            (q : T.left ⟶ pullback s.left t.left)
            (h : a ≫ t = b ≫ s),
            q ≫ pullback.fst s.left t.left = b.left →
            q ≫ pullback.snd s.left t.left = a.left → q ≫ c = d.left →
            ∀ (hs : a ≫ s = d ≫ s) (ht : b ≫ t = d ≫ t),
              moduliSelfRelationArrow p s t E α β a ≫
                eqToHom (congrArg (fun f ↦ p.obj (CostructuredArrow.mk (yoneda.map f))) h) ≫
                moduliSelfRelationArrow p s t E α β b =
              eqToHom (congrArg (fun f ↦ p.obj (CostructuredArrow.mk (yoneda.map f))) hs) ≫
                moduliSelfRelationArrow p s t E α β d ≫
                eqToHom
                  (congrArg (fun f ↦ p.obj (CostructuredArrow.mk (yoneda.map f))) ht.symm) := by
  sorry

end CategoryTheory
