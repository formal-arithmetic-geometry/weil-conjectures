module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Affinization of a quasi-compact quasi-separated algebraic stack

Source: Stacks Project, Tag 075S(2), Tag 01I1 and Tag 06TV
(blueprint: lem-sfb-stack-affinization-qcqs).

The actual global sections are compatible families. Their small ring presentation
is supplied in the conclusion, allowing its spectrum to remain in the scheme universe.
The evaluation characterization fixes the map on every scheme test; the induced
ring map is separately recorded, as is uniqueness up to a vertical 2-isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t s

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Pull back a function on an affine target to every scheme object of a fibred category.
The equality transport is the based functor's projection equality; the scheme arrow
is the Yoneda preimage. Source: Stacks Tag 01I1 and Tag 06TV
(blueprint: lem-sfb-stack-affinization-qcqs). -/
def moduliAffineGlobalPullbackFamily {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {B : CommRingCat.{u}}
    {q : Spec B ⟶ S}
    (a : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk q))))
    (b : B) (x : F.obj) : Scheme.Γ.obj (op ((moduliSchemeForget F).obj x)) :=
  ((Scheme.ΓSpecIso B).inv ≫ Scheme.Γ.map
    (eqToHom (congrArg (fun T : Over S ↦ T.left) (a.w_obj x)).symm ≫
      (yoneda.preimage (a.obj x).hom).left).op).hom b

/-- Pullback along an affine-target stack map is a compatible family of regular functions.
Source: Stacks Tag 01I1 and Tag 06TV (blueprint: lem-sfb-stack-affinization-qcqs).
Proof: the based functor preserves arrows. Its image arrow is a commutative triangle
of scheme maps, so functoriality of scheme global sections identifies the two
pullbacks. The ULift only changes the ambient universe of the values. -/
theorem moduliAffineGlobalPullbackFamily_compatible {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {B : CommRingCat.{u}}
    {q : Spec B ⟶ S}
    (a : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk q)))) (b : B) :
    (fun x : F.objᵒᵖ ↦ ULift.up (moduliAffineGlobalPullbackFamily a b x.unop)) ∈
      (moduliStructurePresheaf F ⋙ forget CommRingCat).sections := by
  sorry

/-- The induced pullback from an affine ring to global functions, with pointwise operations.
Source: Stacks Tag 01I1 and Tag 06TV (blueprint: lem-sfb-stack-affinization-qcqs). -/
def moduliAffineGlobalPullback {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    {B : CommRingCat.{u}} {q : Spec B ⟶ S}
    (a : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk q)))) :
    B →+* moduliGlobalSectionsRing (moduliStructureSheaf F hF) where
  toFun b := ⟨fun x ↦ ULift.up (moduliAffineGlobalPullbackFamily a b x.unop),
    moduliAffineGlobalPullbackFamily_compatible a b⟩
  map_one' := Subtype.ext (funext (fun _x ↦ congrArg ULift.up (map_one _)))
  map_mul' b c := Subtype.ext (funext (fun _x ↦ congrArg ULift.up (map_mul _ b c)))
  map_zero' := Subtype.ext (funext (fun _x ↦ congrArg ULift.up (map_zero _)))
  map_add' b c := Subtype.ext (funext (fun _x ↦ congrArg ULift.up (map_add _ b c)))

/-- A qcqs algebraic stack over a field has its canonical qcqs affinization, uniquely
up to 2-isomorphism. The ring `B` and `e` present its actual ring of global functions
in the scheme universe. The pointwise condition is the affine-target correspondence
on every scheme object; the ring-map equality is the identity after identification
by `e`. No finite-type, separated-diagonal or moduli-space hypothesis is used.

Source: Stacks Tag 075S(2), Tag 01I1 and Tag 06TV; Alper, Adequate moduli spaces,
Remarks 4.1.3 and 5.1.2 (blueprint: lem-sfb-stack-affinization-qcqs).

Proof:
1. A global function is a compatible family. Its evaluation on an object over V
   is a ring map to Gamma(V,O). By the scheme affine-target correspondence
   (lem-weil-pbc-morphism-into-affine-scheme), it defines a scheme map to Spec R.
   Compatibility makes these maps functorial. Structural pullbacks from k show
   that they are k-morphisms (def-sfb-stable-pointed-moduli-groupoids).
   Descent along a quasi-compact smooth scheme atlas realizes the same section
   ring as an equalizer of small rings; choose a small presentation B of it.
2. Any other map with these restrictions agrees objectwise by that correspondence.
   The target fibres are discrete, giving the required vertical 2-isomorphism.
3. The pulled-back global function has at x the component of the original family
   at x. Hence the induced map on global functions is the identity under e.
4. Spec B is quasi-separated (lem-weil-pbc-affine-scheme-qcqs). Its structure map
   and diagonal have qcqs scheme base changes by
   lem-weil-pbc-qcqs-morphism-permanence. A quasi-compact etale scheme atlas of
   an algebraic-space test reduces its qcqs assertions to these scheme assertions
   (lem-sfb-representable-stack-quasicompact-tests). The products are algebraic
   by lem-sfb-algebraic-stack-fibre-products.
5. Factor a through its graph into F times Spec B over k. The graph is a base
   change of the target diagonal, and the second projection a base change of the
   structural map of F. Base change and composition preserve quasi-compactness
   directly by the tests of def-sfb-stack-qcqs-morphism, so a is quasi-compact.
6. Apply lem-sfb-stack-quasiseparated-cancellation: the composite to Spec k is
   quasi-separated by hypothesis, and the target structural diagonal is
   quasi-separated by step 4. Thus a is quasi-separated as well. -/
theorem stack_affinization_qcqs (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k)))) (hF : IsAlgebraicModuliStack F)
    (hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, t, s}
      (moduliBaseStructure F))
    (hqs : IsQuasiSeparatedAlgebraicModuliMap (moduliBaseStructure F)) :
    ∃ (B : CommRingCat.{u})
      (e : B ≃+* moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1))
      (q : Spec B ⟶ Spec (.of k))
      (a : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk q)))),
      (∀ (x : F.obj) (b : B),
        moduliAffineGlobalPullbackFamily a b x = ((e b).1 (op x)).down) ∧
      IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, t, s} a ∧
      IsQuasiSeparatedAlgebraicModuliMap a ∧
      moduliAffineGlobalPullback hF.1.1 a = e.toRingHom ∧
      ∀ (a' : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk q)))),
        (∀ (x : F.obj) (b : B),
          moduliAffineGlobalPullbackFamily a' b x = ((e b).1 (op x)).down) →
        Nonempty (ModuliTwoIso a' a) := by
  sorry

end CategoryTheory
