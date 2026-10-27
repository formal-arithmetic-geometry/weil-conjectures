module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.RingTheory.FiniteEtaleSubalgebraUnion
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctor

/-!
# The finite étale scheme of connected components

Source: Milne, Algebraic Groups (2017), Propositions 1.29, 1.30(a,b), 1.31(a,b)
and Remark 1.33, printed pp.15-16
(blueprint: lem-sfb-algebraic-scheme-etale-components).

The four indexing helpers package precisely the separated finite-type schemes, their
terminal object, product and scalar extension. The theorem asserts existence of the
component functors together with the natural quotient maps and all comparison properties.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.EtaleComponents

/-- The domain of the component functor: separated finite-type schemes over a field.
Source: Milne, Algebraic Groups (2017), Proposition 1.29, printed p.15
(blueprint: lem-sfb-algebraic-scheme-etale-components). -/
abbrev Input (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of k)) ↦
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- The point, as an input of the component functor.
Source: Milne, Algebraic Groups (2017), universal property following Proposition 1.29
(blueprint: lem-sfb-algebraic-scheme-etale-components). -/
noncomputable def pointInput (k : Type u) [Field k] : Input k :=
  ⟨Over.mk (𝟙 (Spec (.of k))),
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k)))),
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k)))),
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))⟩

/-- The fibre product over the field, as an input of the component functor.
Source: Milne, Algebraic Groups (2017), Proposition 1.30(b), printed pp.15-16
(blueprint: lem-sfb-algebraic-scheme-etale-components). -/
noncomputable def productInput {k : Type u} [Field k] (X Y : Input k) : Input k := by
  letI : IsSeparated X.obj.hom := X.property.1
  letI : LocallyOfFiniteType X.obj.hom := X.property.2.1
  letI : QuasiCompact X.obj.hom := X.property.2.2
  letI : IsSeparated Y.obj.hom := Y.property.1
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.2.1
  letI : QuasiCompact Y.obj.hom := Y.property.2.2
  exact ⟨Over.mk (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom),
    inferInstanceAs (IsSeparated (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom)),
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom)),
    inferInstanceAs (QuasiCompact (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom))⟩

/-- Scalar extension, as an input of the component functor over the extended field.
Source: Milne, Algebraic Groups (2017), Proposition 1.30(a), printed pp.15-16
(blueprint: lem-sfb-algebraic-scheme-etale-components). -/
noncomputable def baseChangeInput {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Input k) : Input L := by
  letI : IsSeparated X.obj.hom := X.property.1
  letI : LocallyOfFiniteType X.obj.hom := X.property.2.1
  letI : QuasiCompact X.obj.hom := X.property.2.2
  exact ⟨(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X.obj,
    inferInstanceAs (IsSeparated
      (pullback.snd X.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))),
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd X.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))),
    inferInstanceAs (QuasiCompact
      (pullback.snd X.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))))⟩

/-- Universal finite étale component schemes, functorial and compatible with the point,
products and arbitrary field extensions; their fibres are geometrically connected and
are precisely the connected components of the underlying space.
Source: Milne, Algebraic Groups (2017), Propositions 1.29-1.31 and Remark 1.33,
printed pp.15-16 (blueprint: lem-sfb-algebraic-scheme-etale-components).

Proof plan:
1. For A = Γ(X,O), use `lem-sfb-finite-etale-subalgebra-directed-union` to form B.
After an algebraic closure, a finite étale subalgebra of dimension d splits into d
orthogonal nonzero idempotents. Flat base change of global sections for qcqs schemes
and the clopen-idempotent correspondence bound d by the finite number of irreducible
components of X after base change. Directedness and maximal dimension give B finite
étale. For empty X both A and B are zero, so the same construction applies.
2. Set Π(X) = Spec B. The inclusion B → A gives q by the morphism-into-affine
bijection. Maps from finite étale algebras factor uniquely through B, giving exactly
the asserted bijection on morphisms into every finite étale scheme.
3. Apply uniqueness to q_Y f to define Π(f); uniqueness proves identity, composition
and naturality. For Spec k, B = k and q is the identity, giving the point comparison.
4. Separated finite-type base change preserves the domain. Flat base change of global
sections and `lem-sfb-maximal-ind-etale-field-base-change` identify B after arbitrary
field extension with its scalar extension. Taking spectra and the affine fibre-product
identification give the comparison and identify the actual q maps.
5. Split B as a finite product of separable fields. Each point fibre is the open
subscheme defined by its coordinate idempotent, hence is nonempty. A disconnected
fibre would give a nontrivial idempotent of its field factor, since every idempotent
of A lies in B. Thus these fibres are connected and exactly the connected components.
6. Extend a residue field to its algebraic closure. The base-change comparison and
associativity of fibre products identify the extended fibre with a component fibre
over that closure, which is nonempty and connected by step 5. The algebraic-closure
criterion implies connectedness after every extension of the residue field.
7. The product of the two component schemes is finite étale. Universality gives the
comparison from the component scheme of the product. Separatedness and finite type
are preserved by products, so all preceding steps apply to that product.
8. Over a separable closure the component fibres U_i and V_j are geometrically
connected, so U_i × V_j are nonempty connected clopen pieces and are exactly the
components of the product. Thus the comparison is a Galois-equivariant bijection on
geometric points. Full faithfulness of the étale geometric-point functor lifts the
inverse and proves that it is an isomorphism. Its two projection equations are the
defining factorization equations. Empty schemes give empty sets of component pairs.
-/
theorem exists_component_functors :
    ∃ (P : ∀ (k : Type u) [Field k], Input k ⥤ Over (Spec (.of k)))
      (q : ∀ (k : Type u) [Field k],
        ObjectProperty.ι (fun X : Over (Spec (.of k)) ↦
          IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⟶ P k),
      (∀ (k : Type u) [Field k] (X : Input k),
        IsFinite ((P k).obj X).hom ∧ Etale ((P k).obj X).hom ∧
        (∀ (E : Over (Spec (.of k))) [IsFinite E.hom] [Etale E.hom],
          Function.Bijective (fun h : (P k).obj X ⟶ E ↦ (q k).app X ≫ h))) ∧
      (∀ (k : Type u) [Field k],
        ∃ e : (P k).obj (pointInput k) ≅ (pointInput k).obj,
          (q k).app (pointInput k) ≫ e.hom = 𝟙 (pointInput k).obj) ∧
      (∀ (k : Type u) [Field k] (X Y : Input k),
        ∃ e : (P k).obj (productInput X Y) ≅
          Over.mk (pullback.fst ((P k).obj X).hom ((P k).obj Y).hom ≫ ((P k).obj X).hom),
          ((q k).app (productInput X Y)).left ≫ e.hom.left ≫
              pullback.fst ((P k).obj X).hom ((P k).obj Y).hom =
            pullback.fst X.obj.hom Y.obj.hom ≫ ((q k).app X).left ∧
          ((q k).app (productInput X Y)).left ≫ e.hom.left ≫
              pullback.snd ((P k).obj X).hom ((P k).obj Y).hom =
            pullback.snd X.obj.hom Y.obj.hom ≫ ((q k).app Y).left) ∧
      (∀ (k L : Type u) [Field k] [Field L] [Algebra k L] (X : Input k),
        ∃ e : (P L).obj (baseChangeInput (L := L) X) ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj ((P k).obj X),
          (q L).app (baseChangeInput (L := L) X) ≫ e.hom =
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map ((q k).app X)) ∧
      (∀ (k : Type u) [Field k] (X : Input k) (t : ((P k).obj X).left),
        Nonempty ((((q k).app X).left).fiber t) ∧
        ∀ (L : Type u) [Field L] [Algebra (((P k).obj X).left.residueField t) L],
          ConnectedSpace ↥(pullback (((q k).app X).left.fiberToSpecResidueField t)
            (Spec.map (CommRingCat.ofHom
              (algebraMap (((P k).obj X).left.residueField t) L))))) ∧
      (∀ (k : Type u) [Field k] (X : Input k) (x : X.obj.left),
        (((q k).app X).left ⁻¹' {((q k).app X).left x}) = connectedComponent x) := by
  sorry

end AlgebraicGeometry.EtaleComponents
