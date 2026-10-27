module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.StackRelativeSpectrum
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Relative spectra preserve adequate moduli spaces

Source: Alper, arXiv:1005.2398v3, Lemma 5.2.11, printed p.28, used in
Lemma 8.3.1, printed p.39 (blueprint: lem-sfb-adequate-relative-spectrum).

The direct image is identified, as an algebra, with the recorded étale-test
section sheaf. The source is the actual functor of algebra points. The target
uses the existing normalized relative-Spec anti-equivalence for spaces. The map
is fixed by evaluation on every compatible pair of scheme charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- A quasi-coherent model of the actual direct-image algebra. The equivalences
preserve restrictions and the canonical structure maps. They also give the
canonical size transport from compatible section families to small chart rings.
Source: Alper Lemma 5.2.11; Stacks Tag 06W6
(blueprint: lem-sfb-adequate-relative-spectrum). -/
structure ModuliDirectImageAlgebraModel {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicSpace S) (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (B : ModuliAlgebraSheaf F hF) where
  /-- The quasi-coherent algebra on the target's small étale site. -/
  algebra : Y.QCAlg
  /-- Identification with sections over the actual base changes. -/
  sections (W : Y.EtaleSite) : algebra.obj.right.obj.obj (op W) ≃+*
    (moduliDirectImage hF Y φ B.right).obj.obj (op W)
  /-- The identifications are natural on the target étale site. -/
  naturality {W U : Y.EtaleSite} (f : W ⟶ U)
      (s : algebra.obj.right.obj.obj (op U)) :
    sections W (algebra.obj.right.obj.map f.op s) =
      (moduliDirectImage hF Y φ B.right).obj.map f.op (sections U s)
  /-- Structure functions act by their pullbacks on every object of a base change. -/
  structure_map (W : Y.EtaleSite) (r : Scheme.Γ.obj (op (Y.etaleForget.obj W)))
      (i : ModuliPushforwardIndex Y φ W) :
    (sections W (algebra.obj.hom.hom.app (op W) r)).1 (op i) =
      B.hom.hom.app (op i.left)
        (ULift.up ((Scheme.Γ.map (moduliChartSchemeMap Y φ W i).op) r))

/-- The target relative spectrum uses the existing section-normalized anti-equivalence.
Its theorem determines this object up to the normalized canonical isomorphism;
no mere existence theorem for unrelated algebraic spaces is used.
Source: Stacks Tags 081V--081W; Alper Lemma 5.2.11
(blueprint: lem-sfb-adequate-relative-spectrum). -/
def moduliImageRelativeSpecData {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    RelativeSpecData Y :=
  (Classical.choose (space_relative_spec_correspondence S)) Y

/-- The affine algebraic space which is the relative spectrum of the direct image.
Source: Alper Lemma 5.2.11 (blueprint: lem-sfb-adequate-relative-spectrum). -/
def moduliImageRelativeSpectrum {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    {Y : AlgebraicSpace S} {φ : BasedFunctor F (discreteModuli Y.obj.obj)}
    {B : ModuliAlgebraSheaf F hF} (M : ModuliDirectImageAlgebraModel hF Y φ B) :=
  (moduliImageRelativeSpecData Y).relativeSpec M.algebra

/-- The evaluation condition on the canonical relative-Spec arrow. In the equation,
`i` is a chart of the direct-image section family, `q` is a chart of the target
relative spectrum, and `j` is a lift of the source test object to `q`. The base
triangle ensures these refer to the same map to `W`. The left side evaluates
that section using the algebra point; the right side pulls back the tautological
function on the target relative spectrum.
Source: Alper Lemma 5.2.11; Stacks Tag 01LX
(blueprint: lem-sfb-adequate-relative-spectrum). -/
def IsModuliRelativeSpecEvaluation {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    {Y : AlgebraicSpace S} (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (B : ModuliAlgebraSheaf F hF) (M : ModuliDirectImageAlgebraModel hF Y φ B)
    (h : BasedFunctor (moduliRelativeSpectrum B)
      (discreteModuli (moduliImageRelativeSpectrum M).obj.left.obj.obj)) : Prop :=
  (moduliRelativeSpectrumProjection B).comp φ =
      h.comp (discreteModuliMap (moduliImageRelativeSpectrum M).obj.hom.hom.hom) ∧
  ∀ (x : (moduliRelativeSpectrum B).obj) (W : Y.EtaleSite)
    (i : φ.obj x.unop.1.unop ⟶ W.obj)
    (q : ModuleChart (moduliImageRelativeSpectrum M).obj.hom W)
    (j : h.obj x ⟶ q.left.obj),
    eqToHom (φ.w_obj x.unop.1.unop).symm ≫ i.left =
      eqToHom (h.w_obj x).symm ≫ j.left ≫ q.hom.left →
    ∀ c : M.algebra.obj.right.obj.obj (op W),
      (x.unop.2.1.app (op (Over.mk (𝟙 x.unop.1.unop))))
        ((M.sections W c).1 (op (CostructuredArrow.mk i))) =
      ULift.up ((Scheme.Γ.map
        ((eqToHom (h.w_obj x).symm ≫ j.left).left).op)
        (((moduliImageRelativeSpecData Y).directImage
          (moduliImageRelativeSpectrum M)).projection W q
          (((moduliImageRelativeSpecData Y).counitAlgebra M.algebra).hom.right.hom.app
            (op W) c)))

/-- The direct image is quasi-coherent, both relative spectra are algebraic, and
its evaluation arrow is an adequate moduli space, for every quasi-coherent algebra.
The chart algebras are small in the scheme universe; the ambient section-family
universe remains unrestricted. This is the size convention for taking spectra.
The existential model of the image is fixed by its natural ring identifications;
the source and target relative spectra and the evaluation equation fix the arrow.
Source: Alper, arXiv:1005.2398v3, Lemma 5.2.11, printed p.28
(blueprint: lem-sfb-adequate-relative-spectrum).

Proof:
1. By lem-sfb-stack-qcqs-algebra-direct-image, qcqs of the adequate map makes its
   direct-image algebra quasi-coherent. Its étale-test formula gives `M`.
   The functor of points of lem-sfb-stack-relative-spec-construction identifies
   the source with `moduliRelativeSpectrum B`, proves it algebraic, and identifies
   its affine-chart realizations. The space case is the existing relative Spec.
   Evaluation of the direct-image sections gives the displayed arrow and formula.
2. Cover Y by affine étale schemes W. By
   lem-sfb-stack-quasi-coherent-scheme-restriction the restrictions are tensor
   restrictions. The étale-test formula identifies the image algebra on W with
   the image of the base-changed map. Composition of charts is étale by
   lem-trf-space-chartwise-etale-permanence. By
   lem-sfb-adequate-moduli-etale-locality this base-changed map is adequate.
   Tautological evaluation identifies the ring of functions of its relative
   spectrum with the sections of B, and hence with the affine target ring.
3. The source over W is qcqs: the original adequate map is qcqs and its relative
   spectrum is affine, so apply lem-sfb-stack-qcqs-composition-affine.
   The evaluation arrow is the canonical affinization by its section formula;
   lem-sfb-stack-affinization-qcqs therefore proves it qcqs.
4. For any surjection of quasi-coherent algebras on the source relative spectrum,
   use lem-sfb-stack-affine-algebra-direct-image along its affine projection.
   This preserves the surjection and identifies global section rings. Adequacy
   on W lifts a positive power of each section. Transfer it through those ring
   identifications, which preserve multiplication and powers. This treats all
   algebras on the relative spectrum, not only ones descending from F.
5. The qcqs property, the structural ring isomorphism and these power lifts give
   adequacy over each affine chart by lem-sfb-adequate-moduli-etale-locality.
   Their base changes cover the target by
   lem-trf-space-chartwise-etale-permanence. First descend qcqs using
   lem-sfb-stack-etale-local-qcqs-homeomorphism, then adequacy by étale locality.
   None of these steps imposes finiteness, flatness or reducedness on B. -/
theorem adequate_relative_spectrum {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F) (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ)
    (B : ModuliAlgebraSheaf F hF.1.1) (hB : IsQuasicoherentModuliAlgebra B)
    (hsmall : ∀ x : F.obj, Small.{u} (B.right.obj.obj (op x))) :
    ∃ (M : ModuliDirectImageAlgebraModel hF.1.1 Y φ B)
      (hV : IsAlgebraicModuliStack (moduliRelativeSpectrum B))
      (h : BasedFunctor (moduliRelativeSpectrum B)
        (discreteModuli (moduliImageRelativeSpectrum M).obj.left.obj.obj)),
      IsModuliRelativeSpecEvaluation φ B M h ∧
        IsAdequateModuliSpace (moduliRelativeSpectrum B) hV
          (moduliImageRelativeSpectrum M).obj.left h := by
  sorry

end CategoryTheory
