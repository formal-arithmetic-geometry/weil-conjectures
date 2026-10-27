module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Groupoid
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Morphism sheafification of a fibred groupoid

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), first four naive
construction paragraphs, and Tag 0435 (lemma-stackify-universal-property)
(blueprint: lem-sfb-groupoid-morphism-sheafification).

Pseudofunctors encode fibred groupoids with coherent pullbacks. Strong transformations
encode pullback-compatible functors, and invertible modifications encode their
invertible natural transformations. The single universe is the larger universe of
`def-weil-size-convention`. The equality of fibre object types below retains the
objects themselves, and the component functors of `q` are identity on these objects.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory Opposite
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

set_option backward.isDefEq.respectTransparency false in
/-- Sheafifying the morphism presheaves of a fibred groupoid retains its fibre objects
and produces a prestack through which every functor into a prestack extends.

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), first four naive
construction paragraphs; Tag 0435 (lemma-stackify-universal-property), morphism extension
(blueprint: lem-sfb-groupoid-morphism-sheafification).

Since the fibres are groupoids, `presheafHom` is the isomorphism presheaf. The
isomorphism `e` identifies its sheafification on the entire slice with the new
isomorphism presheaf, and the displayed equation identifies its unit with `q` on
arrows, including the conjugation by the pullback comparisons of `q`. At the identity
of the slice, `presheafHomObjHomEquiv` identifies this with the required fibre arrows.
The pseudofunctor and strong-transformation axioms express that composition,
identities, inverses and coherent pullbacks extend those of the original groupoid.

Proof: (1) Apply `lem-trf-sieve-set-sheafification-exists` on each slice to obtain
A_{u,v} = I_{u,v}^#. Its unit is locally surjective and locally injective by
`lem-cbc-set-presheaf-sheafification-local-bijection`; finite intersections of covering
sieves cover by the topology axioms in `def-weil-pbc-topos`.
(2) Represent two sections on a common covering sieve, compose their original
arrows, and glue their unit images. Local injectivity makes choices locally equal;
separatedness makes their images equal. The sheaf condition gives a unique composite.
Identities are unit images, and inverses are glued from inverses of representatives.
These constructions commute with restriction.
(3) Represent three arrows simultaneously to check associativity locally, and then
use separatedness. The same argument gives both unit and inverse laws. The unit
preserves composition and identities, giving the fibre functors q, identity on objects.
(4) Relocalize the slice using `def-pur-localized-ringed-site`, and apply
`lem-cbc-sieve-slice-sheafification`. Its unit-compatible comparison defines pullback
on the new arrows. Preservation of composition and inverses follows on representatives.
The original pullback comparisons map under q to natural comparisons; their unit and
associativity equations follow from the original equations on objects.
(5) The associated total category has objects (T,u) and arrows (h,a) with
 a : u -> h^*v. Compose (h,a), (k,b) as (kh,c_{h,k} h^*(b) a).
The comparison cocycle gives associativity and units. The lift (h,1) is cartesian:
an arrow over h l factors uniquely using c_{l,h}^{-1} on its vertical component.
The original cartesian factorization gives q on total categories.
(6) The slice-sheafification comparison identifies the entire new isomorphism
presheaf with I_{u,v}^#, compatibly with its unit. Therefore it is a sheaf and A is a
prestack; at 1_T its sections give the asserted new fibre arrows.
(7) For F into a prestack Z, its maps I_{u,v} -> Isom_Z(Fu,Fv) extend uniquely by
sheafification. Evaluate these extensions at 1_T, retaining F on objects. Checking on
simultaneous representatives and using separatedness proves the functor laws.
(8) Retain F's pullback comparisons. Their naturality follows locally on representatives,
using the unit-compatible slice comparison; separatedness gives it globally. Their
coherence follows from that of F. The extensions agree with F after q, and identity
object components give the invertible modification. Object-descent effectivity is unused. -/
theorem exists_groupoid_morphism_sheafification
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (hP : ∀ T : C, IsGroupoid (P.obj (.mk (op T)))) :
    ∃ A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w},
      (∀ T : C, IsGroupoid (A.obj (.mk (op T)))) ∧ A.IsPrestack J ∧
      ∃ (q : StrongTrans P A)
        (hObj : ∀ T : C, (A.obj (.mk (op T)) : Type w) = P.obj (.mk (op T))),
        (∀ (T : C) (u : P.obj (.mk (op T))),
          (q.app (.mk (op T))).toFunctor.obj u = Eq.mpr (hObj T) u) ∧
        (∀ (T : C) (u v : P.obj (.mk (op T))),
          ∃ e : sheafify (J.over T) (P.presheafHom u v) ≅
              A.presheafHom ((q.app (.mk (op T))).toFunctor.obj u)
                ((q.app (.mk (op T))).toFunctor.obj v),
            ∀ (V : Over T) (φ : (P.presheafHom u v).obj (op V)),
              e.hom.app (op V) ((toSheafify (J.over T) (P.presheafHom u v)).app (op V) φ) =
                (q.naturality V.hom.op.toLoc).inv.toNatTrans.app u ≫
                  (q.app (.mk (op V.left))).toFunctor.map φ ≫
                    (q.naturality V.hom.op.toLoc).hom.toNatTrans.app v) ∧
        (∀ (Z : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}),
          (∀ T : C, IsGroupoid (Z.obj (.mk (op T)))) → Z.IsPrestack J →
          ∀ F : StrongTrans P Z, ∃ H : StrongTrans A Z,
            Nonempty (@CategoryTheory.Iso (StrongTrans P Z)
              (StrongTrans.homCategory (F := P) (G := Z)) (StrongTrans.vcomp q H) F)) := by
  sorry

end CategoryTheory.Pseudofunctor
