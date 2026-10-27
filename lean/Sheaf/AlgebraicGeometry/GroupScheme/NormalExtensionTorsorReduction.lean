module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.CategoryTheory.Sites.Sheafification

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Reduction of represented right torsors through a normal extension

Source: Milne, Algebraic Groups (2017), Example 2.68, Proposition 2.69, p.60,
Proposition 16.55, p.344, and Appendix A.80--A.81, pp.584--585.
(blueprint: lem-sfb-normal-extension-torsor-reduction).

The auxiliary records spell out the conclusions of this one reduction theorem.
All schemes, actions, quotient arrows and comparisons remain part of the data.
The orbit presheaf is the presheaf coequalizer of projection and restricted action.
Its universal arrow to the represented quotient is its fppf sheafification, in the
universal-property sense of def-weil-pbc-sheafification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.NormalTorsorReduction

/-- The quotient scheme, both torsors, and the specified sheafified orbit map.
The identification records that the total space of the N-torsor is the original P;
its action is precisely the restricted original action. The two action equations
also specify the induced Q-action. The final fields give the full sheafification
universal property, rather than a quotient only on rational points.

Source: Milne, Example 2.68, Proposition 2.69 and Appendix A.81
(blueprint: lem-sfb-normal-extension-torsor-reduction). -/
structure Data {B : Scheme.{u}} {N G Q : Grp (Over B)}
    (i : N ⟶ G) (q : G ⟶ Q) {S : Over B} (P : RepresentedRightTorsor G S) where
  quotient : RepresentedRightTorsor Q S
  kernelTorsor : RepresentedRightTorsor N quotient.space
  identification : kernelTorsor.space ≅ P.space
  over_base : kernelTorsor.projection ≫ quotient.projection =
    identification.hom ≫ P.projection
  restricted_action : kernelTorsor.action ≫ identification.hom =
    (identification.hom ⊗ₘ i.hom.hom) ≫ P.action
  quotient_action : P.action ≫ identification.inv ≫ kernelTorsor.projection =
    ((identification.inv ≫ kernelTorsor.projection) ⊗ₘ q.hom.hom) ≫ quotient.action
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over B) (yoneda.obj quotient.space)
  orbitMap :
    coequalizer (yoneda.map (fst P.space N.X))
      (yoneda.map ((𝟙 P.space ⊗ₘ i.hom.hom) ≫ P.action)) ⟶ yoneda.obj quotient.space
  orbitMap_quotient : coequalizer.π _ _ ≫ orbitMap =
    yoneda.map (identification.inv ≫ kernelTorsor.projection)
  universal : ∀ Z : Sheaf (Scheme.fppfTopology.over B) (Type u),
    Function.Bijective (fun f : yoneda.obj quotient.space ⟶ Z.obj ↦ orbitMap ≫ f)

/-- The actual quotient morphism P → P/N, through the recorded identification.
Source: Milne, Proposition 16.55 and Appendix A.81
(blueprint: lem-sfb-normal-extension-torsor-reduction). -/
def Data.map {B : Scheme.{u}} {N G Q : Grp (Over B)}
    {i : N ⟶ G} {q : G ⟶ Q} {S : Over B} {P : RepresentedRightTorsor G S}
    (d : Data i q P) : P.space ⟶ d.quotient.space :=
  d.identification.inv ≫ d.kernelTorsor.projection

/-- The fibre P_a with its restricted N-action and its actual projection to P.
A cartesian square identifies it with P ×[P/N] S. The last field is exactly the
section-composition assertion, conditional on a being a section of P/N → S.

Source: Milne, Proposition 16.55, normal-extension induction
(blueprint: lem-sfb-normal-extension-torsor-reduction). -/
structure SectionFiber {B : Scheme.{u}} {N G Q : Grp (Over B)}
    {i : N ⟶ G} {q : G ⟶ Q} {S : Over B} {P : RepresentedRightTorsor G S}
    (d : Data i q P) (a : S ⟶ d.quotient.space) where
  torsor : RepresentedRightTorsor N S
  inclusion : torsor.space ⟶ P.space
  cartesian : IsPullback inclusion torsor.projection d.map a
  action : torsor.action ≫ inclusion = (inclusion ⊗ₘ i.hom.hom) ≫ P.action
  section_lift : a ≫ d.quotient.projection = 𝟙 S →
    ∀ b : S ⟶ torsor.space, b ≫ torsor.projection = 𝟙 S →
      (b ≫ inclusion) ≫ P.projection = 𝟙 S

/-- A base-change comparison for the quotient, its N-torsor, and all reductions
along sections. Both torsor squares are cartesian; the displayed action equation
specifies the pulled-back quotient action. The unique fibre comparison has the
actual two pullback projections and preserves the restricted action. Its last
clause identifies the composites of compatible sections with P after pullback.
Uniqueness with these projections also specifies identity and iterated pullbacks.

Source: Milne, Appendix A.81 and Proposition 16.55, arbitrary-base completion
(blueprint: lem-sfb-normal-extension-torsor-reduction). -/
structure BaseChange {B : Scheme.{u}} {N G Q : Grp (Over B)}
    {i : N ⟶ G} {q : G ⟶ Q} {S : Over B} {P : RepresentedRightTorsor G S}
    (d : Data i q P) {S' : Over B} (f : S' ⟶ S)
    (P' : RepresentedRightTorsor G S') (j : P'.space ⟶ P.space)
    (d' : Data i q P') where
  quotientMap : d'.quotient.space ⟶ d.quotient.space
  quotient_cartesian :
    IsPullback quotientMap d'.quotient.projection d.quotient.projection f
  quotient_action : d'.quotient.action ≫ quotientMap =
    (quotientMap ⊗ₘ 𝟙 Q.X) ≫ d.quotient.action
  kernel_cartesian : IsPullback j d'.map d.map quotientMap
  section_fibers : ∀ (a : S ⟶ d.quotient.space) (a' : S' ⟶ d'.quotient.space),
    a ≫ d.quotient.projection = 𝟙 S → a' ≫ d'.quotient.projection = 𝟙 S' →
    a' ≫ quotientMap = f ≫ a →
    ∀ (F : SectionFiber d a) (F' : SectionFiber d' a'),
      ∃! t : F'.torsor.space ⟶ F.torsor.space,
        IsPullback t F'.torsor.projection F.torsor.projection f ∧
        t ≫ F.inclusion = F'.inclusion ≫ j ∧
        F'.torsor.action ≫ t = (t ⊗ₘ 𝟙 N.X) ≫ F.torsor.action ∧
        ∀ (b : S ⟶ F.torsor.space) (b' : S' ⟶ F'.torsor.space),
          b ≫ F.torsor.projection = 𝟙 S → b' ≫ F'.torsor.projection = 𝟙 S' →
          b' ≫ t = f ≫ b →
          (b' ≫ F'.inclusion) ≫ j = f ≫ (b ≫ F.inclusion)

end AlgebraicGeometry.NormalTorsorReduction

namespace AlgebraicGeometry

/-- A represented right G-torsor has the represented normal quotient and reductions
along every section, compatibly with arbitrary base change of the base scheme.

Source: Milne, Example 2.68 and Proposition 2.69, p.60; Proposition 16.55, p.344;
Appendix A.80--A.81, pp.584--585
(blueprint: lem-sfb-normal-extension-torsor-reduction).

Proof plan (the nine steps of the DAG node):
1. Take the fppf cover U=P → S. Its diagonal section trivializes P_U by the
   torsor square. Fppf covers are fpqc (lem-trf-fppf-covering-is-fpqc), and flatness,
   surjectivity and finite presentation survive pullback by the three permanence
   lemmas. Represented functors satisfy descent (lem-weil-pbc-fpqc-representable-descent).
2. Q is flat over k (lem-pc-flat-field), and finite type over the Noetherian field
   implies finite presentation (pqf-lem-lft-fp-locnoeth). The identity section gives
   surjectivity. Q_T → T and the base changes of q are affine fppf morphisms, using
   lem-weil-pbc-affine-morphism-permanence and the same base-change results.
3. The inverse to (h,n) ↦ (h,hi(n)) is (h,h') ↦ (h,h⁻¹h'). The latter factors
   through the scheme-theoretic kernel; Yoneda makes the formulas scheme morphisms
   (lem-galois-yoneda-fully-faithful). Thus q is an N-torsor, without pointwise
   surjectivity on all test schemes.
4. On U ×_S U write u₁=u₀g₀₁. Uniqueness gives g₀₂=g₀₁g₁₂. The transitions
   z ↦ q(g₀₁)⁻¹z define a descent datum (def-pd-descent-datum) on Q_U.
   Affine effective descent (lem-galois-fpqc-affine-descent-effective) gives R/S.
   Representable descent glues P → R and the right Q-action since left translations
   commute with right multiplication. The action identities descend as equalities.
5. The map is N-invariant. Its orbit-presheaf map is locally surjective: pull back
   first to U and then along q to lift a Q-coordinate. Two points with the same
   quotient differ by an element of ker(q)=N by the original torsor square.
   Lem-cbc-set-presheaf-sheafification-local-bijection identifies its sheafification
   with h_R; def-weil-pbc-sheafification gives the recorded universal arrow.
6. Over U, (z,t) ↦ (z,zt) has inverse (z,z') ↦ (z,z⁻¹z'). These inverses glue
   by representable descent. Affineness, flatness and local finite presentation
   descend by the three fpqc descent lemmas; affine permanence gives qc and qs.
   Lift points to U and use the identity of Q to get surjectivity. Thus R is a Q-torsor.
7. Locally P → R is q_U; the same descent lemmas give its affine fppf properties.
   The inverse torsor map again factors differences through ker(q)=N. Thus P → R
   with the restricted action is an N-torsor on the specified original total space.
8. Pull this N-torsor back along a section a. Flatness, surjectivity and finite
   presentation persist, as does the torsor square by def-pc-fibre-product.
   For a section b of that fibre, p(pr_P b)=id follows from the pullback equation.
9. Pull back U and its transition datum along every S' → S. The local-lift and
   orbit-equality argument still identifies the sheaf quotient with R ×_S S'.
   The actions and quotient arrows agree by representable descent. The universal
   property of fibre products gives the unique equivariant fibre comparisons,
   preserving both projections, sections and their composites. The same uniqueness
   gives identity and iterated-base-change coherence.
-/
theorem normal_extension_torsor_reduction
    {k : Type u} [Field k] (N G Q : Grp (Over (Spec (.of k))))
    (i : N ⟶ G) (q : G ⟶ Q)
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    [IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] [QuasiSeparated q.hom.hom.left]
    (_hquot : IsFppfGroupQuotient i q)
    (S : Over (Spec (.of k))) (P : RepresentedRightTorsor G S) :
    ∃ d : NormalTorsorReduction.Data i q P,
      (∀ a : S ⟶ d.quotient.space, a ≫ d.quotient.projection = 𝟙 S →
        Nonempty (NormalTorsorReduction.SectionFiber d a)) ∧
      ∀ (S' : Over (Spec (.of k))) (f : S' ⟶ S),
        ∃ (P' : RepresentedRightTorsor G S') (j : P'.space ⟶ P.space),
          IsPullback j P'.projection P.projection f ∧
          P'.action ≫ j = (j ⊗ₘ 𝟙 G.X) ≫ P.action ∧
          ∃ d' : NormalTorsorReduction.Data i q P',
            (∀ a' : S' ⟶ d'.quotient.space, a' ≫ d'.quotient.projection = 𝟙 S' →
              Nonempty (NormalTorsorReduction.SectionFiber d' a')) ∧
            Nonempty (NormalTorsorReduction.BaseChange d f P' j d') := by
  sorry

end AlgebraicGeometry
