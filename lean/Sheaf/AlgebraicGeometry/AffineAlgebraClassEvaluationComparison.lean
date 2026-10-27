module

public import Sheaf.AlgebraicGeometry.AffineAlgebraClassComparisonData
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.AffineTildeTotalTensor
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Affine algebra-class comparison preserves evaluation and open restriction

Source: Stacks Project, perfect.tex, Tag 0A6H(3)(a); sites-cohomology.tex,
Tag 08J9; duality.tex, Tag 0E2U.
(blueprint: lem-trf-affine-algebra-class-evaluation-comparison).

The comparison and localization maps are actual evaluation transposes, as defined
in AffineAlgebraClassComparisonData. The proposition below records each commuting
square and the hypotheses under which those maps are invertible.

## Main statements

- `sheafAlgebraMultiplication`, `sheafClassMap`: actual tilde-algebra product and class transpose.
- `Compatible`: all evaluation, algebra-class and restriction squares.
- `affine_algebraClass_evaluation_comparison`: existence of the normalized comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.AffineClassComparison

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The ordinary tilde tensor isomorphism, uniquely fixed by pure tensor sections.
Its inverse constructs the ordinary sheaf-algebra product from ordinary multiplication.
Source: Stacks 01I8 (blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
@[irreducible] def ordinaryTensorIso (B : Type u) [CommRing B] (M N : ModuleCat.{u} B) :
    tilde (R := .of B) (M ⊗ N) ≅ tilde (R := .of B) M ⊗ tilde (R := .of B) N :=
  @asIso _ _ _ _ (affine_tilde_tensor (.of B) M N).choose_spec.2.2.choose
    (affine_tilde_tensor (.of B) M N).choose_spec.2.2.choose_spec.2.1

/-- The associated sheaf of an ordinary module, placed in degree zero and localized.
This object does not depend on a realization system.
Source: Stacks 06Z0, 0E2U (blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
abbrev sheafZeroComplex (B : Type u) [CommRing B] (M : ModuleCat.{u} B) :
    schemeDerivedCategory (Spec (.of B)) :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
    ((tilde.functor (.of B)).obj M))

/-- The factorization identifies realized M[0] with the actual sheaf tilde M[0].
Source: Stacks 06Z0 (blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
@[irreducible] def zeroRealization (s : Realizations.{u, w}) (B : Type u) [CommRing B]
    (M : ModuleCat.{u} B) : (s.F B).obj (zeroComplex B M) ≅ sheafZeroComplex B M :=
  letI : (tilde.functor (.of B)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  (s.factor B).app ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (tilde.functor (.of B))
        (.up ℤ) 0).app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication of the actual sheaf algebra tilde C, localized in degree zero.
The ordinary product is inverse tilde tensor followed by tilde of mul', so this
construction uses no realization system, no F(mu), and no realization tensor arrow.
Source: Stacks 01I8, 0E2U (blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
@[irreducible] def sheafAlgebraMultiplication (B C : Type u)
    [CommRing B] [CommRing C] [Algebra B C] :
    sheafZeroComplex B (ModuleCat.of B C) ⊗ sheafZeroComplex B (ModuleCat.of B C) ⟶
      sheafZeroComplex B (ModuleCat.of B C) :=
  letI := SheafOfModules.isMonoidal_W (Spec (.of B)).sheaf
  letI := SheafOfModules.monoidalCategory (Spec (.of B)).sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor (Spec (.of B)).sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (Spec (.of B)).sheaf
  let M : SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
    (tilde.functor (.of B)).obj (ModuleCat.of B C)
  let P := (HomologicalComplex.single _ (.up ℤ) 0).obj M
  pullbackTensorModelMap (Spec (.of B)) P P ≫
    DerivedCategory.Q.map
      ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) M P).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorLeft M)
          (.up ℤ) 0).hom.app M ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map
          ((ordinaryTensorIso B (ModuleCat.of B C) (ModuleCat.of B C)).inv ≫
            (tilde.functor (.of B)).map (ModuleCat.ofHom (LinearMap.mul' B C))))

/-- The sheaf algebra-class transpose uses actual multiplication of tilde C,
transported to realized C[0] through the termwise-tilde factorization. Multiplication
is independent of the realization system; identifying it with F(mu_C) after the
tensor comparison is a conclusion of the main theorem, not part of this definition.
Source: Stacks 0E2U, 01I8, 08J9
(blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
@[irreducible] def sheafClassMap (s : Realizations.{u, w}) (B C : Type u)
    [CommRing B] [CommRing C] [Algebra B C] (T : DMod B)
    (ξ : zeroComplex B (ModuleCat.of B C) ⟶ T) :
    (s.F B).obj (zeroComplex B (ModuleCat.of B C)) ⟶
      sheafHom B ((s.F B).obj (zeroComplex B (ModuleCat.of B C))) ((s.F B).obj T) :=
  (schemeDerivedTensorHomEquiv (Spec (.of B)) _ _ _).symm
    (((zeroRealization s B (ModuleCat.of B C)).hom ⊗ₘ
        (zeroRealization s B (ModuleCat.of B C)).hom) ≫
      sheafAlgebraMultiplication B C ≫
      (zeroRealization s B (ModuleCat.of B C)).inv ≫ (s.F B).map ξ)

/-- The evaluation, naturality, algebra-class, scalar, and restriction conclusions
for the representative-normalized affine realization system. Naturality is stated
for actual derived morphisms, not only for morphisms of chosen complexes.
Source: Stacks 0A6H(3)(a), 08J9, 08DL, 0E2U
(blueprint: lem-trf-affine-algebra-class-evaluation-comparison). -/
structure Compatible (s : Realizations.{u, w}) : Prop where
  normalized : Normalized s
  invertible : ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra B C] (T : DMod B),
    DerivedCategory.IsPseudoCoherent (zeroComplex B (ModuleCat.of B C)) →
      (∃ t : ℤ, T.IsGE t) → IsIso (gamma s B (zeroComplex B (ModuleCat.of B C)) T)
  evaluation_eq : ∀ (B : Type u) [CommRing B] (E T : DMod B),
    schemeDerivedTensorHomEquiv (Spec (.of B)) _ _ _ (gamma s B E T) =
      (s.tensor B (hom B E T) E).hom ≫ (s.F B).map (evaluation B E T)
  naturality : ∀ (B : Type u) [CommRing B] (E E' T T' : DMod B)
    (a : E' ⟶ E) (b : T ⟶ T'),
    (s.F B).map ((ordinaryModuleDerivedInternalHom B).map (a.op, b)) ≫ gamma s B E' T' =
      gamma s B E T ≫ (derivedInternalHom (Opens.grothendieckTopology (Spec (.of B)))
        (Spec (.of B)).sheaf).map (((s.F B).map a).op, (s.F B).map b)
  class_eq : ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (T : DMod B) (ξ : zeroComplex B (ModuleCat.of B C) ⟶ T),
    (s.F B).map
        (classMap B (zeroComplex B (ModuleCat.of B C)) T (algebraMultiplication B C) ξ) ≫
        gamma s B (zeroComplex B (ModuleCat.of B C)) T = sheafClassMap s B C T ξ
  scalar_eq : ∀ (B : Type u) [CommRing B] (E T : DMod B) (b : B),
    (s.F B).map (b • 𝟙 (hom B E T)) ≫ gamma s B E T =
      gamma s B E T ≫ (derivedInternalHom (Opens.grothendieckTopology (Spec (.of B)))
        (Spec (.of B)).sheaf).map (𝟙 _, (s.F B).map (b • 𝟙 T))
  algebraScalar_eq : ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (T : DMod B) (c : C),
    (s.F B).map ((ordinaryModuleDerivedInternalHom B).map
        ((algebraScalar B C c).op, 𝟙 T)) ≫ gamma s B (zeroComplex B (ModuleCat.of B C)) T =
      gamma s B (zeroComplex B (ModuleCat.of B C)) T ≫
        (derivedInternalHom (Opens.grothendieckTopology (Spec (.of B)))
          (Spec (.of B)).sheaf).map (((s.F B).map (algebraScalar B C c)).op, 𝟙 _)
  restriction_invertible : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) →
      ∀ K L : schemeDerivedCategory (Spec (.of B)), IsIso (openHom s φ K L)
  localization_invertible : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) →
      ∀ (C : Type u) [CommRing C] [Algebra B C] (T : DMod B),
      DerivedCategory.IsPseudoCoherent (zeroComplex B (ModuleCat.of B C)) →
        (∃ t : ℤ, T.IsGE t) → IsIso (localization φ (zeroComplex B (ModuleCat.of B C)) T)
  restriction_eq : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) (E T : DMod B),
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map (gamma s B E T) ≫
        openHom s φ ((s.F B).obj E) ((s.F B).obj T) ≫
        (derivedInternalHom (Opens.grothendieckTopology (Spec (.of D)))
          (Spec (.of D)).sheaf).map
            (X := (op ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj ((s.F B).obj E)),
              (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj ((s.F B).obj T)))
            (Y := (op ((s.F D).obj ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)),
              (s.F D).obj ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T)))
            (((s.rho φ hj).inv.app E).op, (s.rho φ hj).hom.app T) =
      (s.rho φ hj).hom.app (hom B E T) ≫ (s.F D).map (localization φ E T) ≫
        gamma s D ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)
          ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T)
  localization_class : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (E T : DMod B) (μ : E ⊗ E ⟶ E) (ξ : E ⟶ T),
    (ModuleCat.ordinaryDerivedExtendScalars φ).map (classMap B E T μ ξ) ≫
        localization φ E T =
      classMap D ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)
        ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T)
        (Functor.LaxMonoidal.μ (ModuleCat.ordinaryDerivedExtendScalars φ) E E ≫
          (ModuleCat.ordinaryDerivedExtendScalars φ).map μ)
        ((ModuleCat.ordinaryDerivedExtendScalars φ).map ξ)
  zero_invertible : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) →
      ∀ M : ModuleCat.{u} B, IsIso (zeroComparison φ M)
  algebra_multiplication : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (_hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)))
    (C : Type u) [CommRing C] [Algebra B C],
    Functor.LaxMonoidal.μ (ModuleCat.ordinaryDerivedExtendScalars φ) _ _ ≫
        (ModuleCat.ordinaryDerivedExtendScalars φ).map (algebraMultiplication B C) ≫
        zeroComparison φ (ModuleCat.of B C) =
      (zeroComparison φ (ModuleCat.of B C) ⊗ₘ zeroComparison φ (ModuleCat.of B C)) ≫
        baseChangedMultiplication φ C
  algebra_class : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)))
    (C : Type u) [CommRing C] [Algebra B C] (T : DMod B)
    (ξ : zeroComplex B (ModuleCat.of B C) ⟶ T),
    (ModuleCat.ordinaryDerivedExtendScalars φ).map
        (classMap B (zeroComplex B (ModuleCat.of B C)) T (algebraMultiplication B C) ξ) ≫
        localization φ (zeroComplex B (ModuleCat.of B C)) T ≫
        (ordinaryModuleDerivedInternalHom D).map
          (X := (op ((ModuleCat.ordinaryDerivedExtendScalars φ).obj
            (zeroComplex B (ModuleCat.of B C))), (ModuleCat.ordinaryDerivedExtendScalars φ).obj T))
          (Y := (op (zeroComplex D ((ModuleCat.extendScalars φ).obj (ModuleCat.of B C))),
            (ModuleCat.ordinaryDerivedExtendScalars φ).obj T))
          (((@CategoryTheory.inv _ _ _ _ (zeroComparison φ (ModuleCat.of B C))
            (zero_invertible φ hj (ModuleCat.of B C)))).op, 𝟙 _) =
      zeroComparison φ (ModuleCat.of B C) ≫
        classMap D (zeroComplex D ((ModuleCat.extendScalars φ).obj (ModuleCat.of B C)))
          ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T) (baseChangedMultiplication φ C)
          ((@CategoryTheory.inv _ _ _ _ (zeroComparison φ (ModuleCat.of B C))
            (zero_invertible φ hj (ModuleCat.of B C))) ≫
            (ModuleCat.ordinaryDerivedExtendScalars φ).map ξ)
  successive_localization : ∀ {B D A : Type u} [CommRing B] [CommRing D] [CommRing A]
    (φ : B →+* D) (ψ : D →+* A) (E T : DMod B),
    (ModuleCat.ordinaryDerivedExtendScalars ψ).map (localization φ E T) ≫
        localization ψ ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)
          ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T) =
      (s.extensionComp φ ψ).inv.app (hom B E T) ≫ localization (ψ.comp φ) E T ≫
        (ordinaryModuleDerivedInternalHom A).map
          (((s.extensionComp φ ψ).inv.app E).op, (s.extensionComp φ ψ).hom.app T)

/-- The canonical affine algebra-class comparison, normalized by evaluation,
commutes with scalar actions, multiplication transposes and successive affine opens.
The degree-zero algebra case is included by `algebraMultiplication`, `algebra_class`
and `algebraScalar_eq`; invertibility requires precisely pseudo-coherence and a
lower bound on the second input. `gamma` is the specified arrow and hence becomes
the asserted canonical isomorphism, rather than merely some isomorphism of objects.

Source: Stacks Project, Tag 0A6H(3)(a), Tag 06Z0, Tag 08J9, Tag 0E2U
(blueprint: lem-trf-affine-algebra-class-evaluation-comparison).

Proof:
1. Choose K-flat module resolutions. Associated sheaf preserves their K-flatness
(lem-pc-affine-tilde-kflat), and the normalized ordinary tilde tensor arrow extends
across every signed total-tensor summand (lem-pc-affine-tilde-total-tensor,
lem-weil-pbc-affine-tilde-tensor). Descend through localization to obtain the tensor
comparison of lem-pc-affine-derived-pullback-tensor-tilde. The affine equivalence
lem-pc-affine-qcoh-derived-equivalence supplies the realization and factorization.
2. Define gamma as the sheaf tensor-Hom transpose of realized module evaluation.
The inverse-transpose identity gives evaluation_eq. The ringed derived tensor-Hom
adjunction (lem-sf-ringed-derived-tensor-hom-adjunction) fixes this normalization.
3. For pseudo-coherent E and bounded-below T, the finite-free Hom computation
lem-sc-affine-pseudo-coherent-rhom-qcoherent puts the target in D_QCoh. Full
faithfulness of the affine equivalence identifies composition with gamma with the
bijection of tensor-Hom adjunctions on all objects. Essential surjectivity supplies
a right inverse; injectivity supplies the left inverse, proving invertible.
4. Uncurry both naturality composites. Naturality of evaluation and tensor gives
the same map, so injectivity of transpose proves naturality, including B scalars
and precomposition by multiplication by c in C. No chain representative of a
particular derived morphism is required.
5. Uncurry the realized multiplication-class map. Its inverse transpose is
realized multiplication followed by realized xi, using tensor naturality.
On K-flat resolutions mapping to C[0], module multiplication sends p tensor q
to the product of their images in C. The ordinary tilde tensor isomorphism is
normalized on pure tensor sections, so applying tilde sends this map to the actual
product of the sheaf algebra tilde C. The total-tensor normalization, localization
counit and factorization therefore identify F(mu_C) after the tensor comparison
with sheafAlgebraMultiplication transported through zeroRealization. Following
by F(xi) gives the independent sheaf class transpose; injectivity yields class_eq.
6. An affine open immersion is flat (the local ring maps are isomorphisms and
lem-weil-pbc-flat-morphism-affine-criterion applies). Exact scalar extension
commutes with cohomology (lem-weil-pbc-flat-tensor-exact), preserves a lower bound,
and extends finite-free pseudo-coherent representatives. Thus the hypotheses
of step 3 hold after restriction and zeroComparison is invertible.
7. Termwise unit-normalized tilde pullback (lem-weil-pbc-tilde-pullback-base-change)
and the original K-flat pullback counit give rho and its representative equation.
Pure tensors give rho_tensor. Restricting K-injective resolutions still gives
K-injectives (lem-sc-derived-k-injective-restrict-open); ordinary Hom restriction
(lem-sc-hom-complex-restrict-open) preserves evaluation. Hence openHom is the
isomorphism of lem-sc-derived-internal-hom-restrict-open.
8. Transpose extended evaluation to define lambda = localization. Uncurry both
sides of restriction_eq. The representative tensor and evaluation equations from
steps 1 and 7 give exactly the same extended evaluation, hence equality.
9. Step 3 over both rings and the restriction equation make F_D(lambda) invertible.
The affine equivalence reflects isomorphisms, proving localization_invertible.
Uncurrying localization_class gives extended xi composed with multiplication.
On pure tensors (d tensor c)(e tensor c') = de tensor cc', so the ordinary
base-changed algebra multiplication and algebra_class equations follow.
10. For successive affine opens both scalar-extension counit composites send
 e tensor (d tensor p) to e psi(d) tensor p. The original derived-pullback
composition (lem-pc-ringed-spaces-derived-pullback-composition) and ordinary tilde
pullback give rho_comp. Successive Hom restrictions restrict the same families.
Uncurrying successive_localization gives the same extended original evaluation,
so the two maps agree. Applying localization_class twice gives the corresponding
successive algebra-class square, and restriction_eq gives the successive gamma
square. Identity restrictions use the same equations with the unit element.
All these arguments apply also to zero rings, zero complexes and empty affine opens. -/
theorem affine_algebraClass_evaluation_comparison :
    ∃ s : Realizations.{u, w}, Compatible s := by
  sorry

end AlgebraicGeometry.AffineClassComparison
