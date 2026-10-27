module

public import Sheaf.AlgebraicGeometry.StackScalarAlgebra
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic

import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Flat scalar extension of sections on an algebraic stack

Source: Stacks Project, stacks-cohomology.tex, Tags 0765 and 0771(4), degree zero;
stacks-sheaves.tex, Tags 06WK and 06WH
(blueprint: lem-sfb-stack-flat-scalar-sections).

Restriction is precomposition on the actual 2-fibre product. The section comparison
is specified on every pure tensor, together with naturality and the structural unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace CategoryTheory

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- Spec S to Spec R as a map of representable fibred groupoids over k.
Source: Stacks 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def flatScalarSpecMap :
    BasedFunctor
      (discreteModuli (yoneda.obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k S))))))
      (discreteModuli (yoneda.obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))))) :=
  discreteModuliMap (yoneda.map (Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (by
      change Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) = _
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact (IsScalarTower.algebraMap_apply k R S a).symm)))

variable {F : BasedCategory.{v, w} (Over (Spec (.of k)))}
variable (p : BasedFunctor F (discreteModuli (yoneda.obj
  (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))))))

/-- The actual scalar 2-base change, with no replacement by isomorphism classes.
Source: Stacks 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
abbrev flatScalarStack := moduliTwoFiberProduct p (flatScalarSpecMap (k := k) (S := S))

/-- The projection q to the original stack.
Source: Stacks 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
abbrev flatScalarProjection := moduliTwoFiberFst p (flatScalarSpecMap (k := k) (S := S))

/-- The projection p_S to Spec S, retaining its structural triangle over k.
Source: Stacks 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
abbrev flatScalarBaseProjection :=
  moduliTwoFiberSnd p (flatScalarSpecMap (k := k) (S := S))

/-- Scalar base change remains fibred in groupoids.
Source: Stacks 06WH (blueprint: lem-sfb-stack-flat-scalar-sections).
Proof: take cartesian lifts in both factors and pull back their vertical comparison
isomorphism. Unique cartesian factorization in the two factors gives the unique
factorization in the full iso-comma subcategory. -/
theorem flatScalarStack_isFibred (hF : IsFibredInGroupoids F) :
    IsFibredInGroupoids (flatScalarStack (S := S) p) := by
  sorry

/-- Literal scalar restriction satisfies fppf descent.
Source: Stacks 06WH (blueprint: lem-sfb-stack-flat-scalar-sections).
Proof: covers and overlaps under q are the same scheme covers and overlaps.
Apply the sheaf condition of A to this matching-family diagram. -/
theorem flatScalarRestriction_isSheaf (hF : IsFibredInGroupoids F)
    (A : ModuliAlgebraSheaf F hF) :
    Presheaf.IsSheaf (moduliFppfTopology (flatScalarStack (S := S) p))
      ((flatScalarProjection (S := S) p).toFunctor.op ⋙ A.right.obj) := by
  sorry

/-- Structure functions are unchanged under the projection q over schemes.
Source: Stacks 06TV, 06WH (blueprint: lem-sfb-stack-flat-scalar-sections).
Proof: the first projection is over the base by reflexivity. Consequently its
underlying scheme functor, regular functions, ULift, and restriction maps agree. -/
theorem flatScalarStructure_eq :
    moduliStructurePresheaf (flatScalarStack (S := S) p) =
      (flatScalarProjection (S := S) p).toFunctor.op ⋙ moduliStructurePresheaf F := by
  sorry

/-- Restrict an algebra by precomposing its values, operations and structure map.
Source: Stacks 06WH (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def flatScalarRestriction (hF : IsFibredInGroupoids F) (A : ModuliAlgebraSheaf F hF) :
    ModuliAlgebraSheaf (flatScalarStack (S := S) p) (flatScalarStack_isFibred p hF) :=
  Under.mk
    ({ hom := eqToHom (flatScalarStructure_eq (S := S) p) ≫
        Functor.whiskerLeft (flatScalarProjection (S := S) p).toFunctor.op A.hom.hom } :
      moduliStructureSheaf _ (flatScalarStack_isFibred p hF) ⟶
        ⟨_, flatScalarRestriction_isSheaf (S := S) p hF A⟩)

/-- The algebra map on global sections, evaluated componentwise.
Source: Stacks 06W6 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def moduliAlgebraSectionsMap {B : AlgebraicGeometry.Scheme.{u}}
    {C : BasedCategory.{v, w} (Over B)} {hC : IsFibredInGroupoids C}
    {A A' : ModuliAlgebraSheaf C hC} (f : A ⟶ A') :
    moduliGlobalSectionsRing A.right →+* moduliGlobalSectionsRing A'.right where
  toFun a := ⟨fun x ↦ f.right.hom.app x (a.1 x), fun g ↦ by
    exact (congrArg (fun t ↦ t (a.1 _)) (f.right.hom.naturality g).symm).trans
      (congrArg (fun t ↦ f.right.hom.app _ t) (a.2 g))⟩
  map_one' := Subtype.ext (funext (fun x ↦ map_one (f.right.hom.app x).hom))
  map_mul' a b := Subtype.ext (funext (fun x ↦ map_mul (f.right.hom.app x).hom _ _))
  map_zero' := Subtype.ext (funext (fun x ↦ map_zero (f.right.hom.app x).hom))
  map_add' a b := Subtype.ext (funext (fun x ↦ map_add (f.right.hom.app x).hom _ _))

/-- The structural R-action on compatible algebra section families.
Source: Stacks 06TV, 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
@[instance_reducible] def moduliStructuralSectionsAlgebra {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : Algebra R (moduliGlobalSectionsRing A.right) :=
  RingHom.toAlgebra
    { toFun := fun r ↦ ⟨fun x ↦ A.hom.hom.app x (moduliScalarMap p x.unop r), fun g ↦ by
        have h := congrArg (fun f ↦ f (ULift.up r)) (moduliScalarMap_naturality p g)
        change (moduliStructurePresheaf F).map g (moduliScalarMap p _ r) =
          moduliScalarMap p _ r at h
        exact (congrArg (fun f ↦ f (moduliScalarMap p _ r))
          (A.hom.hom.naturality g).symm).trans
            (congrArg (fun t ↦ A.hom.hom.app _ t) h)⟩
      map_one' := Subtype.ext (funext (fun x ↦
        map_one ((A.hom.hom.app x).hom.comp (moduliScalarMap p x.unop))))
      map_mul' a b := Subtype.ext (funext (fun x ↦
        map_mul ((A.hom.hom.app x).hom.comp (moduliScalarMap p x.unop)) a b))
      map_zero' := Subtype.ext (funext (fun x ↦
        map_zero ((A.hom.hom.app x).hom.comp (moduliScalarMap p x.unop))))
      map_add' a b := Subtype.ext (funext (fun x ↦
        map_add ((A.hom.hom.app x).hom.comp (moduliScalarMap p x.unop)) a b)) }

/-- The existing global section ring bundled with its specified structural base action.
Source: Stacks 06TV, 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def moduliSectionsAlgebra {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : CommAlgCat R :=
  letI := moduliStructuralSectionsAlgebra p A
  CommAlgCat.of R (moduliGlobalSectionsRing A.right)

/-- Pull a global section back by literal precomposition with q.
Source: Stacks 06W6, 0771 (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def flatScalarSectionRestriction {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) :
    moduliSectionsAlgebra p A →+*
      moduliSectionsAlgebra (flatScalarBaseProjection p)
        (flatScalarRestriction (S := S) p hF A) where
  toFun a := ⟨fun x ↦ a.1 (op ((flatScalarProjection (S := S) p).obj x.unop)),
    fun f ↦ a.2 ((flatScalarProjection (S := S) p).toFunctor.map f.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction on algebra morphisms is precomposition on every component.
Source: Stacks 06WH (blueprint: lem-sfb-stack-flat-scalar-sections). -/
def flatScalarRestrictionMap {hF : IsFibredInGroupoids F}
    {A B : ModuliAlgebraSheaf F hF} (f : A ⟶ B) :
    flatScalarRestriction (S := S) p hF A ⟶ flatScalarRestriction (S := S) p hF B :=
  Under.homMk
    { hom := Functor.whiskerLeft (flatScalarProjection (S := S) p).toFunctor.op f.right.hom }
    (by ext x a; exact congrArg (fun t ↦ t.hom.app _ a) (Under.w f))

/-- Flat scalar extension preserves quasi-coherent algebras and their surjections,
and its canonical comparison of section rings is an S-algebra isomorphism natural in A.
Source: Stacks 0765, 0771(4), 06WK, 06WH
(blueprint: lem-sfb-stack-flat-scalar-sections).

Proof:
1. Apply lem-sfb-stack-quasi-coherent-scheme-restriction to A. Its scheme-test
modules and tensor comparisons show restriction is quasi-coherent. A surjection
has surjective scheme-test maps; restriction keeps these maps, so the converse
surjection criterion gives a sheaf surjection. This needs no flatness of q.
2. Those comparisons make A locally quasi-coherent with flat comparison maps.
Apply lem-sfb-stack-higher-images-flat-comparison to the qcqs map p in degree zero.
The scheme restrictions G_R and G_S of p_*A satisfy g^*G_R isomorphic to G_S.
The degree-zero direct-image formula identifies their sections with the two
stack section rings, and their restriction with q^*.
3. Apply lem-weil-pbc-module-pullback-affine-sections on the whole affine schemes,
then the preceding comparison. The resulting bijective module map sends a tensor s
to q^*a times the structural section of s.
4. Multiplying pure tensors shows multiplicativity and preservation of one.
Restriction commutes with each algebra map, giving naturality on pure tensors and
then on all tensors by additivity. The formula at 1 tensor s is precisely the
structural section, including for the structure algebra. -/
theorem stack_flat_scalar_sections (hF : IsAlgebraicModuliStack F)
    (_hpqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} p)
    (_hpqs : IsQuasiSeparatedAlgebraicModuliMap p)
    (_hflat : (algebraMap R S).Flat) :
    (∀ (A : ModuliAlgebraSheaf F hF.1.1), IsQuasicoherentModuliAlgebra A →
      IsQuasicoherentModuliAlgebra (flatScalarRestriction (S := S) p hF.1.1 A)) ∧
    (∀ (A B : ModuliAlgebraSheaf F hF.1.1) (f : A ⟶ B),
      IsQuasicoherentModuliAlgebra A → IsQuasicoherentModuliAlgebra B →
      IsSurjectiveModuliAlgebra f →
      IsSurjectiveModuliAlgebra (flatScalarRestrictionMap (S := S) p f)) ∧
    ∃ e : ∀ (A : ModuliAlgebraSheaf F hF.1.1) (_ : IsQuasicoherentModuliAlgebra A),
      (S ⊗[R] moduliSectionsAlgebra p A) ≃ₐ[S]
        moduliSectionsAlgebra (flatScalarBaseProjection p)
          (flatScalarRestriction (S := S) p hF.1.1 A),
      (∀ (A : ModuliAlgebraSheaf F hF.1.1) (hA : IsQuasicoherentModuliAlgebra A)
          (a : moduliSectionsAlgebra p A) (s : S),
        e A hA (s ⊗ₜ[R] a) =
          flatScalarSectionRestriction p A a *
            algebraMap S (moduliSectionsAlgebra (flatScalarBaseProjection p)
              (flatScalarRestriction (S := S) p hF.1.1 A)) s) ∧
      (∀ (A B : ModuliAlgebraSheaf F hF.1.1)
          (hA : IsQuasicoherentModuliAlgebra A) (hB : IsQuasicoherentModuliAlgebra B)
          (f : A ⟶ B) (s : S) (a : moduliSectionsAlgebra p A),
        moduliAlgebraSectionsMap (flatScalarRestrictionMap p f) (e A hA (s ⊗ₜ[R] a)) =
          e B hB (s ⊗ₜ[R] moduliAlgebraSectionsMap f a)) ∧
      (∀ (hO : IsQuasicoherentModuliAlgebra
          (Under.mk (𝟙 (moduliStructureSheaf F hF.1.1)))) (s : S),
        e (Under.mk (𝟙 (moduliStructureSheaf F hF.1.1))) hO (s ⊗ₜ[R] 1) =
          algebraMap S (moduliSectionsAlgebra (flatScalarBaseProjection p)
            (flatScalarRestriction (S := S) p hF.1.1
              (Under.mk (𝟙 (moduliStructureSheaf F hF.1.1))))) s) := by
  sorry

end CategoryTheory
