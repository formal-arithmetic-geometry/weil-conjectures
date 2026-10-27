module

public import Sheaf.AlgebraicGeometry.InvariantClosedSubstackDescent
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension

/-! # Quotient algebras of disjoint closed substacks

Source: Stacks Project, stacks-sheaves.tex, Tags 06WK and 06WT; stacks-properties.tex,
Tag 0507; morphisms.tex, Tag 01QQ; algebra.tex, Tag 00DT
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).

The direct image is constructed as compatible regular functions on the comma category
of closed-substack objects mapping to a test object. This is the scheme-free model of
sections on the scheme 2-base change. No representatives or unrelated algebra data
are chosen. The binary product is the existing product of ring sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The diagram of regular functions over a closed-substack test object.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
abbrev closedModuliSectionDiagram {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (W : ClosedModuliSubstack F) (x : F.obj) :=
  (CostructuredArrow.proj W.inclusion.toFunctor x).op ⋙
    W.inclusion.toFunctor.op ⋙ moduliStructurePresheaf F

/-- The section ring on the comma model of the closed base change.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
abbrev closedModuliSectionRing {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (W : ClosedModuliSubstack F) (x : F.obj) :=
  RingCat.sectionsSubring (closedModuliSectionDiagram W x ⋙ forget₂ CommRingCat RingCat)

/-- Restriction is precomposition by postcomposition of comma arrows.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
def closedModuliSectionRestriction {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (W : ClosedModuliSubstack F) {x y : F.obj} (f : y ⟶ x) :
    closedModuliSectionRing W x →+* closedModuliSectionRing W y where
  toFun s := ⟨fun i ↦ s.1 (op ((CostructuredArrow.map f).obj i.unop)),
    fun g ↦ s.2 ((CostructuredArrow.map f).map g.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Identity arrows act identically on closed-base-change sections.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: postcomposing a comma arrow with the identity leaves it unchanged, so its
precomposition action on every compatible family is the identity. -/
theorem closedModuliSectionRestriction_id {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F) (x : F.obj) :
    closedModuliSectionRestriction W (𝟙 x) = RingHom.id _ := by
  sorry

/-- Restrictions compose in the contravariant order.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: postcomposing a comma arrow twice equals postcomposition with the composite,
by associativity. Precomposition of compatible families reverses that order. -/
theorem closedModuliSectionRestriction_comp {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F)
    {x y z : F.obj} (f : y ⟶ x) (g : z ⟶ y) :
    closedModuliSectionRestriction W (g ≫ f) =
      (closedModuliSectionRestriction W g).comp (closedModuliSectionRestriction W f) := by
  sorry

/-- Regular functions on closed-base-change objects, with actual pullback restrictions.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
def closedModuliStructurePresheaf {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F) :
    F.objᵒᵖ ⥤ CommRingCat.{max (u + 1) v w} where
  obj x := CommRingCat.of (closedModuliSectionRing W x.unop)
  map f := CommRingCat.ofHom (closedModuliSectionRestriction W f.unop)
  map_id x := congrArg CommRingCat.ofHom (closedModuliSectionRestriction_id W x.unop)
  map_comp f g := congrArg CommRingCat.ofHom
    (closedModuliSectionRestriction_comp W f.unop g.unop)

/-- Pullbacks of a test function form a compatible family on its closed base change.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: for a comma arrow a, its defining equation is inclusion(a) followed by the
target comma arrow equals the source comma arrow. Apply the regular-function functor.
This proves precisely the compatibility needed to define the restriction map. -/
theorem closedModuliPullbacks_compatible {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F)
    (x : F.obj) (r : (moduliStructurePresheaf F).obj (op x)) :
    (fun i : (CostructuredArrow W.inclusion.toFunctor x)ᵒᵖ ↦
      (moduliStructurePresheaf F).map i.unop.hom.op r) ∈
        (closedModuliSectionDiagram W x ⋙ forget₂ CommRingCat RingCat ⋙
          forget RingCat).sections := by
  sorry

/-- Restriction of a test function to every closed-substack object over that test.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
def closedModuliStructureMapApp {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F) (x : F.obj) :
    (moduliStructurePresheaf F).obj (op x) →+*
      (closedModuliStructurePresheaf W).obj (op x) where
  toFun r := ⟨fun i ↦ (moduliStructurePresheaf F).map i.unop.hom.op r,
    closedModuliPullbacks_compatible W x r⟩
  map_one' := by apply Subtype.ext; funext i; exact map_one _
  map_mul' r s := by apply Subtype.ext; funext i; exact map_mul _ r s
  map_zero' := by apply Subtype.ext; funext i; exact map_zero _
  map_add' r s := by apply Subtype.ext; funext i; exact map_add _ r s

/-- Closed restriction is natural on the entire big fppf site, including nonflat arrows.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: a comma arrow over y becomes the same arrow followed by y → x. Pullback of
regular functions along this composite equals the composite of the two pullbacks. -/
theorem closedModuliStructureMap_naturality {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F)
    {x y : F.objᵒᵖ} (f : x ⟶ y) :
    (moduliStructurePresheaf F).map f ≫
        CommRingCat.ofHom (closedModuliStructureMapApp W y.unop) =
      CommRingCat.ofHom (closedModuliStructureMapApp W x.unop) ≫
        (closedModuliStructurePresheaf W).map f := by
  sorry

/-- The explicitly constructed closed-base-change presheaf is an fppf sheaf.
Source: Stacks Tags 06WK, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: identify the comma category over x with the category of scheme objects of
T ×_F W, using strict fullness and cartesian lifting. Its compatible regular functions
are the regular functions of that scheme. A covering pulls back to an fppf covering
of this closed scheme. Fppf descent of functions gives the unique glued family.
This is the sheaf clause in step 2 of the node's proof. -/
theorem closedModuliStructurePresheaf_isSheaf {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F)
    (hF : IsFibredInGroupoids F) :
    Presheaf.IsSheaf (moduliFppfTopology F) (closedModuliStructurePresheaf W) := by
  sorry

/-- The closed-substack algebra with the prescribed sections and restriction map.
Only sheafness and naturality are postponed; all ring and restriction data are explicit.
Source: Stacks Tags 06WK, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
def closedModuliAlgebra {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (W : ClosedModuliSubstack F) (hF : IsFibredInGroupoids F) :
    ModuliAlgebraSheaf F hF :=
  Under.mk
    ({ hom :=
      { app := fun x ↦ CommRingCat.ofHom (closedModuliStructureMapApp W x.unop)
        naturality := fun _ _ f ↦ closedModuliStructureMap_naturality W f } } :
      moduliStructureSheaf F hF ⟶
        ⟨closedModuliStructurePresheaf W, closedModuliStructurePresheaf_isSheaf W hF⟩)

/-- The binary algebra product has its componentwise ring operations and diagonal unit.
Source: Stacks Tag 06WK, finite direct sums
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient). -/
def closedModuliProductAlgebra {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (W₁ W₂ : ClosedModuliSubstack F) (hF : IsFibredInGroupoids F) :
    ModuliAlgebraSheaf F hF :=
  Under.mk (prod.lift (closedModuliAlgebra W₁ hF).hom (closedModuliAlgebra W₂ hF).hom)

/-- The comma section convention is exactly Γ of any representing scheme 2-base change.
Source: Stacks Tags 06TV, 0507
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).
Proof: use the specified equivalence presenting the scheme 2-base change and
cartesian factorization to identify its scheme objects with comma objects over x.
Compatible regular functions on a scheme's big site evaluate at its identity object;
pullback from that object is inverse. These operations respect ring operations. -/
theorem closedModuliAlgebra_sections {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (W : ClosedModuliSubstack F)
    (hF : IsFibredInGroupoids F) (T : Over S)
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (Z : Over S) (j : Z ⟶ T) (hj : HasSchemeModuliBaseChange W.inclusion T t Z j) :
    Nonempty (((closedModuliAlgebra W hF).right.obj.obj
      (op (t.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))))) ≃+*
        Scheme.Γ.obj (op Z.left)) := by
  sorry

/-- Disjoint closed substacks yield quasi-coherent algebras and a locally surjective
canonical restriction map. The last two equations say that a global function restricts
to its original value on each closed-substack object.
Source: Stacks Tags 06WK, 06WT, 0507, 01QQ, 00DT
(blueprint: lem-sfb-disjoint-closed-substacks-algebra-quotient).

Proof:
1. On a scheme object x over T, the closed substack pulls back to j:Z → T. On
an affine Spec A it is Spec(A/I), with the quotient map on regular functions
(def-weil-closed-immersion). Strict fullness identifies all further base changes,
independently of choices of comparison isomorphisms. Affine pushforward base change
(lem-weil-pbc-affine-pushforward-base-change) makes j_* O_Z quasi-coherent and
cartesian for every base arrow, with identity and composition compatibilities.
2. Apply lem-sfb-cartesian-module-fppf-realization. Its section formula is the
closed base-change regular-function presheaf constructed above. Multiplication and
its structure map are pullback of regular functions, hence compatible with descent
(def-sfb-stack-quasi-coherent-algebra).
3. Binary direct sums of quasi-coherent modules are quasi-coherent
(lem-weil-pbc-quasi-coherent-module-direct-sum). They are the underlying modules of
binary products of algebras. Tensor pullback preserves the inclusions, projections,
and biproduct identities (def-pc-module-pullback); apply the same realization criterion.
4. By lem-sfb-smooth-presentation-closed-subsets, the two pulled-back closed supports
are disjoint. Their open complements cover T. Refine by affines: on each such affine
one quotient is the zero ring and the other A/I, so each pair (0,b) or (b,0) lifts
from A. Affine open covers are fppf covers. This is local surjectivity, with no
claim of surjectivity on all global sections.
5. A global function is a compatible family. At every comma object its pullback
is its original component, precisely restriction to the corresponding substack.
All ideals and test schemes were arbitrary; no Noetherian or finite-type assumption
was used. -/
theorem disjoint_closed_substacks_algebra_quotient (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k)))) (hF : IsAlgebraicModuliStack F)
    (W₁ W₂ : ClosedModuliSubstack F)
    (hd : Disjoint (Set.range (moduliPointMap W₁.inclusion))
      (Set.range (moduliPointMap W₂.inclusion))) :
    IsQuasicoherentModuliAlgebra (closedModuliAlgebra W₁ hF.1.1) ∧
    IsQuasicoherentModuliAlgebra (closedModuliAlgebra W₂ hF.1.1) ∧
    IsQuasicoherentModuliAlgebra (closedModuliProductAlgebra W₁ W₂ hF.1.1) ∧
    IsSurjectiveModuliAlgebra
      (Under.homMk (U := Under.mk (𝟙 (moduliStructureSheaf F hF.1.1)))
        (V := closedModuliProductAlgebra W₁ W₂ hF.1.1)
        (closedModuliProductAlgebra W₁ W₂ hF.1.1).hom (Category.id_comp _)) ∧
    (∀ (s : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1)) (x : F.obj)
      (i : CostructuredArrow W₁.inclusion.toFunctor x),
      (closedModuliStructureMapApp W₁ x (s.1 (op x))).1 (op i) =
        s.1 (op (W₁.inclusion.obj i.left))) ∧
    (∀ (s : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1)) (x : F.obj)
      (i : CostructuredArrow W₂.inclusion.toFunctor x),
      (closedModuliStructureMapApp W₂ x (s.1 (op x))).1 (op i) =
        s.1 (op (W₂.inclusion.obj i.left))) := by
  sorry

end CategoryTheory
