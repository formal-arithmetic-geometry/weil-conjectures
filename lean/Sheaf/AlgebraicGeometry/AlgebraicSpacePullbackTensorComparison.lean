module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.Paper.RingedTopoiTensorComparisonData

/-! # Canonical tensor comparison for algebraic-space pullback

Source: Stacks Project, Cohomology on Sites, Tag 07A4; spaces-perfect.tex, Tag 0DKI.
(blueprint: def-sfb-space-pullback-tensor-comparison).
The ordinary comparison is fixed on local tensors. Its totalization is fixed on
every signed summand; its derived class is fixed by the shared derived counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex
variable {S : Scheme.{u}}

/-- Local tensor sections in the transported small-model pullback, using the recorded unit.
Source: Stacks 03D7 (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def localSection {X Y : AlgebraicSpace S} (f : X ⟶ Y) (M : Y.SmallModules)
    {G : Over S} {x : yoneda.obj G ⟶ X.obj.obj}
    (U : Neighbourhood G x) (V : Neighbourhood G (x ≫ f.hom.hom))
    (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left)
    (ha : Compatible f U V a) (b : (ringDiagram x).obj (op U))
    (m : M.val.obj (op V.right)) : ((pullback f).obj M).val.obj (op U.right) :=
  moduleTensorSection f (Y.smallModuleEquivalence.inverse.obj M)
    ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V) (relativeChart f U V a ha) b
    ((Y.smallModuleEquivalence.counitIso.inv.app M).val.app (op V.right) m)

/-- The ordinary pullback tensor map is normalized by b tensor (m tensor n).
The scalar b goes on the first factor and the second factor gets the unit scalar.
Source: Stacks 03EL, 07A4 (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def OrdinaryTensorFormula {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (M N : Y.SmallModules)
    (e : (pullback f).obj
        (((SheafOfModules.KFlatTotalTensorModel.tensor Y.smallStructureSheaf).obj M).obj N) ≅
      ((SheafOfModules.KFlatTotalTensorModel.tensor X.smallStructureSheaf).obj
        ((pullback f).obj M)).obj ((pullback f).obj N)) : Prop :=
  ∀ (G : Over S) (x : yoneda.obj G ⟶ X.obj.obj)
    (U : Neighbourhood G x) (V : Neighbourhood G (x ≫ f.hom.hom))
    (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left)
    (ha : Compatible f U V a) (b : (ringDiagram x).obj (op U))
    (m : M.val.obj (op V.right)) (n : N.val.obj (op V.right)),
    e.hom.val.app (op U.right)
      (localSection f _ U V a ha b
        (SheafOfModules.ringedComparisonPure Y.smallStructureSheaf M N (op V.right) m n)) =
      SheafOfModules.ringedComparisonPure X.smallStructureSheaf
        ((pullback f).obj M) ((pullback f).obj N) (op U.right)
        (localSection f M U V a ha b m) (localSection f N U V a ha 1 n)

/-- The ordinary normalized tensor isomorphism exists uniquely.
Source: Stacks 03EL, 07A4 (blueprint: def-sfb-space-pullback-tensor-comparison).
Proof: present inverse image locally by sections on compatible charts and then
extend scalars. Send b tensor (m tensor n) to (b tensor m) tensor (1 tensor n).
Balancedness gives the map; multiplying the two scalars gives its inverse.
Both commute with chart refinement and sheafification. Local pure sections generate
the sheaf tensor, so the displayed equations give uniqueness. Transport through
the existing basis equivalences preserves these equations and the inverse. -/
theorem ordinaryTensor_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (M N : Y.SmallModules) :
    ∃! e : (pullback f).obj
        (((SheafOfModules.KFlatTotalTensorModel.tensor Y.smallStructureSheaf).obj M).obj N) ≅
      ((SheafOfModules.KFlatTotalTensorModel.tensor X.smallStructureSheaf).obj
        ((pullback f).obj M)).obj ((pullback f).obj N), OrdinaryTensorFormula f M N e := by
  sorry

/-- The ordinary comparison selected by its unique local-tensor formula.
Source: Stacks 03EL (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def ordinaryTensor {X Y : AlgebraicSpace S} (f : X ⟶ Y) (M N : Y.SmallModules) :=
  Classical.choose (ordinaryTensor_existsUnique f M N)

/-- The total comparison is uniquely determined by the ordinary comparison on summands.
Source: Stacks 07A4 (blueprint: def-sfb-space-pullback-tensor-comparison).
Proof: pullback, being a left adjoint conjugated by equivalences, preserves coproducts.
Apply its ordinary tensor comparison on each summand indexed by p+q=i. Naturality
makes this commute with the two differentials, whose signs are 1 and (-1)^p on
both sides. The inverse is formed summandwise. The coproduct universal property
gives uniqueness in every degree, hence uniqueness of the chain isomorphism. -/
theorem ordinaryTotal_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : CochainComplex Y.SmallModules ℤ) :
    ∃! e : ((pullback f).mapHomologicalComplex (.up ℤ)).obj ((total Y).obj (P, Q)) ≅
      (total X).obj (((pullback f).mapHomologicalComplex (.up ℤ)).obj P,
        ((pullback f).mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ (p q i : ℤ) (h : p + q = i),
        (pullback f).map (CochainComplex.ιMapBifunctor P Q
          (SheafOfModules.KFlatTotalTensorModel.tensor Y.smallStructureSheaf) p q i h) ≫
            e.hom.f i = (ordinaryTensor f (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((pullback f).mapHomologicalComplex (.up ℤ)).obj P)
            (((pullback f).mapHomologicalComplex (.up ℤ)).obj Q)
            (SheafOfModules.KFlatTotalTensorModel.tensor X.smallStructureSheaf) p q i h := by
  sorry

/-- The summand-normalized total comparison.
Source: Stacks 07A4 (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def ordinaryTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : CochainComplex Y.SmallModules ℤ) :=
  Classical.choose (ordinaryTotal_existsUnique f P Q)

variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]

/-- The canonical derived comparison is pinned by the ordinary total map and the
shared left-derived counit on every pair of flat-term K-flat representatives.
Source: Stacks 07A4, 0DKI (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def CanonicalTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (α : tensor Y ⋙ derivedPullback f ≅
      ((derivedPullback f).prod (derivedPullback f)) ⋙ tensor X) : Prop :=
  ∀ (P Q : CochainComplex Y.SmallModules ℤ) (hP : FlatKFlat Y P) (hQ : FlatKFlat Y Q),
    ∃ (hp : FlatKFlat X (((pullback f).mapHomologicalComplex (.up ℤ)).obj P))
      (hq : FlatKFlat X (((pullback f).mapHomologicalComplex (.up ℤ)).obj Q)),
      (derivedPullback f).map (tensorModel Y P Q hP hQ).hom ≫
          α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (tensor X).map (Prod.mkHom
            ((counit f).app P)
            ((counit f).app Q)) =
        (counit f).app ((total Y).obj (P, Q)) ≫
          DerivedCategory.Q.map (ordinaryTotal f P Q).hom ≫
          (tensorModel X _ _ hp hq).hom

/-- Existence and uniqueness of the representative-normalized derived comparison.
Source: Stacks 06YS, 07A4 (blueprint: def-sfb-space-pullback-tensor-comparison).
Proof: flat-term K-flat resolutions form a resolving class. Tensor pullback preserves
flat terms, and the adjunction and exact restriction of scalars show it preserves
K-flatness on this class. Its derived counit is invertible there. The ordinary total
comparison and the specified tensor representative isomorphisms therefore induce
the displayed map. Naturality of these comparisons descends it to the two derived
variables. Resolving representatives are essentially surjective, so the equation
also proves uniqueness. Inverting the ordinary comparison and the representative
isomorphisms gives the inverse, naturally in both variables. -/
theorem canonicalTensor_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃! α : tensor Y ⋙ derivedPullback f ≅
      ((derivedPullback f).prod (derivedPullback f)) ⋙ tensor X,
      CanonicalTensorComparison f α := by
  sorry

/-- The unique canonical derived pullback tensor comparison, in the source orientation.
Source: Stacks 07A4, 0DKI (blueprint: def-sfb-space-pullback-tensor-comparison). -/
def derivedTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) :=
  Classical.choose (canonicalTensor_existsUnique f)

end AlgebraicGeometry.AlgebraicSpace.SingleComplex
