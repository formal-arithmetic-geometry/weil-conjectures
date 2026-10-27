module

public import Sheaf.AlgebraicGeometry.AffineActionQuotientStack
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Sheaf.AlgebraicGeometry.EquivariantAffineAlgebra
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
import Sheaf.AlgebraicGeometry.ActionGroupoidTorsorComparison
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Quasi-coherent algebra descent on arbitrary affine action quotients

Source: Stacks Project, Tags 06WT, 03LF, 04TK, 050X and 075S
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

The torsor construction is used without a finite-generation assumption. Coactions
are right coactions; the left scheme action uses the antipode before the factor swap.
All comparisons below are normalized on atlas sections and tensor generators.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (G : Scheme.{u})
variable [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
variable (D : Type u) [CommRing D] [Algebra k D]
variable (ρ : HopfAction.AlgebraCoaction k Γ(G, ⊤) D)

/-- The actual coordinate-defined left action, with the antipode convention.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionLeftMap : (G.asOver (Spec (.of k)) ⊗ affineActionScheme k D).left ⟶
    (affineActionScheme k D).left :=
  (((G.isoSpec.asOver (Spec (.of k))).hom ▷ affineActionScheme k D).left) ≫
    (pullbackSpecIso k Γ(G, ⊤) D).hom ≫
      Spec.map (CommRingCat.ofHom
        (((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k Γ(G, ⊤))
          (AlgHom.id k D)).comp ((Algebra.TensorProduct.comm k D Γ(G, ⊤)).toAlgHom.comp
            ρ.map)).toRingHom))

/-- The coordinate-defined action is a morphism over k.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: All constituent coordinate maps are k-algebra maps. Contravariance of Spec
and the two canonical affine comparisons give the asserted equality. -/
theorem coactionLeftMap_over :
    coactionLeftMap k G D ρ ≫ (affineActionScheme k D).hom =
      (G.asOver (Spec (.of k)) ⊗ affineActionScheme k D).hom := by
  sorry

/-- The left action arrow in the category of schemes over k.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionLeftArrow : G.asOver (Spec (.of k)) ⊗ affineActionScheme k D ⟶
    affineActionScheme k D :=
  Over.homMk (coactionLeftMap k G D ρ) (coactionLeftMap_over k G D ρ)

/-- The coaction identities give exactly the left action identities.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Counitality is the identity law. Coassociativity is the right-action law;
applying inversion reverses multiplication and gives g acting as right multiplication
by g inverse, hence the displayed left-action law. Check on coordinate tensor generators. -/
theorem coactionLeftArrow_laws :
    (MonObj.one (X := G.asOver (Spec (.of k))) ▷ affineActionScheme k D) ≫
        coactionLeftArrow k G D ρ = (λ_ (affineActionScheme k D)).hom ∧
    (MonObj.mul (X := G.asOver (Spec (.of k))) ▷ affineActionScheme k D) ≫
        coactionLeftArrow k G D ρ =
      (α_ (G.asOver (Spec (.of k))) (G.asOver (Spec (.of k)))
        (affineActionScheme k D)).hom ≫
          G.asOver (Spec (.of k)) ◁ coactionLeftArrow k G D ρ ≫
            coactionLeftArrow k G D ρ := by
  sorry

/-- The left action has specified data, rather than an existentially chosen map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
@[instance_reducible]
def coactionLeftAction : ModObj (G.asOver (Spec (.of k))) (affineActionScheme k D) where
  smul := coactionLeftArrow k G D ρ
  one_smul := (coactionLeftArrow_laws k G D ρ).1
  mul_smul := (coactionLeftArrow_laws k G D ρ).2

/-- The quotient uses the existing total category of scheme torsors, for arbitrary D.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionQuotient : BasedCategory (Over (Spec (.of k))) :=
  letI := coactionLeftAction k G D ρ
  SchemeAction.torsorGroupoid (G.asOver (Spec (.of k))) (affineActionScheme k D)

/-- The canonical atlas object is the trivial torsor at the identity chart.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionAtlasObject : (coactionQuotient k G D ρ).obj :=
  letI := coactionLeftAction k G D ρ
  SchemeAction.trivialObject (G.asOver (Spec (.of k))) (affineActionScheme k D)
    ⟨affineActionScheme k D, 𝟙 _⟩

/-- The canonical atlas functor, with its actual torsor formulas.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionAtlas :
    BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme k D)))
      (coactionQuotient k G D ρ) :=
  letI := coactionLeftAction k G D ρ
  SchemeAction.quotientAtlas (G.asOver (Spec (.of k))) (affineActionScheme k D)

/-- The torsor quotient is fibred in groupoids, with the recorded pullbacks.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Use the specified torsorPullback and torsorPullbackArrow. Any cartesian
equivariant arrow factors uniquely through a scheme pullback. Arrows over identities
are isomorphisms, and the same universal property makes every total arrow cartesian. -/
theorem coactionQuotient_isFibred : IsFibredInGroupoids (coactionQuotient k G D ρ) := by
  sorry

/-- The actual category of quasi-coherent algebra sheaves on the quotient.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
abbrev CoactionQuotientAlgebras :=
  ObjectProperty.FullSubcategory (IsQuasicoherentModuliAlgebra : ObjectProperty
    (ModuliAlgebraSheaf (coactionQuotient k G D ρ)
      (coactionQuotient_isFibred k G D ρ)))

/-- Atlas sections of an algebra sheaf, using the actual trivial-torsor object.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
abbrev coactionAtlasRing (M : CoactionQuotientAlgebras k G D ρ) : CommRingCat.{u + 1} :=
  M.obj.right.obj.obj (op (coactionAtlasObject k G D ρ))

/-- The structure map into atlas sections, including the canonical universe transport.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionAtlasUnit (M : CoactionQuotientAlgebras k G D ρ) :
    D →+* coactionAtlasRing k G D ρ M :=
  (M.obj.hom.hom.app (op (coactionAtlasObject k G D ρ))).hom.comp
    (ULift.ringEquiv.symm.toRingHom.comp (Scheme.ΓSpecIso (.of D)).inv.hom)

/-- The coefficient action on atlas sections is the specified structure action.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
instance coactionAtlasRing.algebra (M : CoactionQuotientAlgebras k G D ρ) :
    Algebra k (coactionAtlasRing k G D ρ M) :=
  ((coactionAtlasUnit k G D ρ M).comp (algebraMap k D)).toAlgebra

variable (A : Type u) [CommRing A] [Algebra k A] [Algebra A D]
variable [IsScalarTower k A D]

/-- The invariant structure map on the affine atlas.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionBaseArrow : affineActionScheme k D ⟶ affineActionScheme k A :=
  (Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom k A D).toRingHom)).asOver (Spec (.of k))

/-- Scalar-extension coactions are uniquely determined on pure tensors.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Invariance of A makes the tensor formula A-balanced. Multiplication and
unit follow from the algebra coaction on D. Counitality and coassociativity hold on
pure tensors by the original identities. These tensors generate the algebra, proving
uniqueness of the coaction including its proof fields. -/
theorem coactionScalarExtension_existsUnique
    (hA : ∀ a : A, ρ.map (algebraMap A D a) = algebraMap A D a ⊗ₜ[k] 1)
    (C : Type u) [CommRing C] [Algebra A C] :
    ∃! σ : HopfAction.AlgebraCoaction k Γ(G, ⊤) (D ⊗[A] C),
      ∀ (d : D) (c : C) (n : ℕ) (d' : Fin n → D) (h : Fin n → Γ(G, ⊤)),
        ρ.map d = ∑ i, d' i ⊗ₜ[k] h i →
        σ.map (d ⊗ₜ[A] c) = ∑ i, (d' i ⊗ₜ[A] c) ⊗ₜ[k] h i := by
  sorry

/-- The uniquely characterized scalar-extension coaction.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionScalarExtension
    (hA : ∀ a : A, ρ.map (algebraMap A D a) = algebraMap A D a ⊗ₜ[k] 1)
    (C : Type u) [CommRing C] [Algebra A C] :
    HopfAction.AlgebraCoaction k Γ(G, ⊤) (D ⊗[A] C) :=
  Classical.choose (coactionScalarExtension_existsUnique k G D ρ A hA C)

/-- The structural morphism and its chart normalization, for arbitrary D.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Form the smooth action groupoid G times Spec D; source and target are
smooth by base change and inversion. The smooth-groupoid quotient theorem and the
torsor comparison give algebraicity. On a torsor trivialization the invariant map
to Spec A agrees on overlaps, so fpqc descent gives the unique chart map in the
displayed normalization. The atlas composite is affine. Pulling the relative
diagonal back to Spec D times_A Spec D gives the affine map
(g,x) mapping to (x,g acting on x). Representable fppf locality descends affineness
of the diagonal. The atlas/affine-diagonal criterion gives qcqs, without finite
generation of D. These are steps 1--4 of the node. -/
theorem affine_action_quotient_structure
    [Smooth (G ↘ Spec (.of k))] [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))]
    (hA : ∀ a : A, ρ.map (algebraMap A D a) = algebraMap A D a ⊗ₜ[k] 1) :
    IsAlgebraicModuliStack (coactionQuotient k G D ρ) ∧
    ∃ ψ : BasedFunctor (coactionQuotient k G D ρ)
        (discreteModuli (yoneda.obj (affineActionScheme k A))),
      Nonempty (ModuliTwoIso ((coactionAtlas k G D ρ).comp ψ)
        (discreteModuliMap (yoneda.map (coactionBaseArrow k D A)))) ∧
      IsQuasiCompactAlgebraicModuliMap.{u, u, u + 1, u, u + 1, v, w} ψ ∧
      IsQuasiSeparatedAlgebraicModuliMap ψ := by
  sorry

/-- The total space of an actual torsor object.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionTorsorSpace (x : (coactionQuotient k G D ρ).obj) :
    Over (Spec (.of k)) :=
  letI := coactionLeftAction k G D ρ
  x.space

/-- The actual action on the torsor space, without a replacement action.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
@[instance_reducible]
def coactionTorsorAction (x : (coactionQuotient k G D ρ).obj) :
    ModObj (G.asOver (Spec (.of k))) (coactionTorsorSpace k G D ρ x) :=
  letI := coactionLeftAction k G D ρ
  x.action

/-- The actual torsor projection, retaining its domain and base scheme.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionTorsorProjection (x : (coactionQuotient k G D ρ).obj) :
    coactionTorsorSpace k G D ρ x ⟶ (coactionQuotient k G D ρ).p.obj x :=
  letI := coactionLeftAction k G D ρ
  x.projection

/-- The actual equivariant map of a torsor to the affine action scheme.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionTorsorMap (x : (coactionQuotient k G D ρ).obj) :
    coactionTorsorSpace k G D ρ x ⟶ affineActionScheme k D :=
  letI := coactionLeftAction k G D ρ
  x.map

/-- The actual map on torsor spaces of a total arrow.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionTorsorHom {x y : (coactionQuotient k G D ρ).obj} (f : x ⟶ y) :
    coactionTorsorSpace k G D ρ x ⟶ coactionTorsorSpace k G D ρ y :=
  letI := coactionLeftAction k G D ρ
  f.map

/-- Forgetting the scalar-extension coordinate on the affine chart.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionScalarArrow (C : Type u) [CommRing C] [Algebra A C] :
    affineActionScheme k (D ⊗[A] C) ⟶ affineActionScheme k D :=
  (Spec.map (CommRingCat.ofHom
    (AlgHom.restrictScalars k
      (Algebra.TensorProduct.includeLeft : D →ₐ[A] D ⊗[A] C)).toRingHom)).asOver (Spec (.of k))

/-- The base-change equivalence is the literal lift/forget-lift torsor formula.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Compatibility in the 2-fibre product says that the torsor map to Spec D
and its structural map to Spec C have the same A-map. The affine fibre-product
universal property gives a unique map to Spec(D tensor_A C). Its two components
make it equivariant. Conversely forget the lift. Neither construction changes
the torsor, its projection, its action or its total arrows. Uniqueness gives
inverse functors over the base and compatibility with base pullbacks. This is
step 5 of the node, with the canonical tensor coaction from its generator formula. -/
theorem affine_action_quotient_baseChange
    [Smooth (G ↘ Spec (.of k))] [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))]
    (hA : ∀ a : A, ρ.map (algebraMap A D a) = algebraMap A D a ⊗ₜ[k] 1)
    (ψ : BasedFunctor (coactionQuotient k G D ρ)
      (discreteModuli (yoneda.obj (affineActionScheme k A))))
    (hψ : Nonempty (ModuliTwoIso ((coactionAtlas k G D ρ).comp ψ)
      (discreteModuliMap (yoneda.map (coactionBaseArrow k D A)))))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra k C] [IsScalarTower k A C] :
    ∃ (F : BasedFunctor
        (moduliTwoFiberProduct ψ
          (discreteModuliMap (yoneda.map (coactionBaseArrow k C A))))
        (coactionQuotient k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)))
      (H : BasedFunctor
        (coactionQuotient k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C))
        (moduliTwoFiberProduct ψ
          (discreteModuliMap (yoneda.map (coactionBaseArrow k C A))))),
      Nonempty (F.comp H ≅ BasedFunctor.id _) ∧
      Nonempty (H.comp F ≅ BasedFunctor.id _) ∧
      (∀ x,
        coactionTorsorSpace k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
          (F.obj x) = coactionTorsorSpace k G D ρ x.obj.left) ∧
      (∀ x, HEq
        (coactionTorsorAction k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
          (F.obj x)) (coactionTorsorAction k G D ρ x.obj.left)) ∧
      (∀ x, HEq
        (coactionTorsorProjection k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
          (F.obj x)) (coactionTorsorProjection k G D ρ x.obj.left)) ∧
      (∀ x, HEq
        (coactionTorsorMap k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
          (F.obj x) ≫ coactionScalarArrow k D A C)
        (coactionTorsorMap k G D ρ x.obj.left)) ∧
      (∀ x, ∃ ebase : (coactionQuotient k G D ρ).p.obj x.obj.left = x.obj.right.left,
        HEq
          (coactionTorsorMap k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
            (F.obj x) ≫ (Spec.map (CommRingCat.ofHom
              (AlgHom.restrictScalars k
                (Algebra.TensorProduct.includeRight : C →ₐ[A] D ⊗[A] C)).toRingHom)).asOver
                (Spec (.of k)))
          (coactionTorsorProjection k G D ρ x.obj.left ≫ eqToHom ebase ≫
            yoneda.preimage x.obj.right.hom)) ∧
      (∀ {x y} (f : x ⟶ y), HEq
        (coactionTorsorHom k G (D ⊗[A] C) (coactionScalarExtension k G D ρ A hA C)
          (F.map f)) (coactionTorsorHom k G D ρ f.hom.left)) := by
  sorry

/-- Sections of the structure sheaf are the actual invariant subring.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: A structure section is determined on the atlas by the sheaf condition.
The two restrictions to G times Spec D coincide exactly when rho(d)=d tensor 1.
Conversely an invariant element gives equal sections on every torsor trivialization
and hence glues uniquely. Addition, multiplication and unit are computed on the atlas.
The displayed formula is this evaluation, with only the canonical ULift and Gamma-Spec
transports. It is the B=D case of step 10, and includes the zero ring. -/
theorem affine_action_structure_sections :
    ∃ gamma : moduliGlobalSectionsRing
        (moduliStructureSheaf (coactionQuotient k G D ρ) (coactionQuotient_isFibred k G D ρ))
        ≃+* RingHom.eqLocus ρ.map.toRingHom Algebra.TensorProduct.includeLeftRingHom,
      ∀ b, (gamma b).val = (Scheme.ΓSpecIso (.of D)).hom
        (b.val (op (coactionAtlasObject k G D ρ))).down := by
  sorry

/-- The right-arrow source object, parametrized by (g,x) with point x.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightSource : (coactionQuotient k G D ρ).obj :=
  letI := coactionLeftAction k G D ρ
  SchemeAction.trivialObject (G.asOver (Spec (.of k))) (affineActionScheme k D)
    ⟨G.asOver (Spec (.of k)) ⊗ affineActionScheme k D, snd _ _⟩

/-- The right-arrow target object has point g inverse acting on x.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightTarget : (coactionQuotient k G D ρ).obj :=
  letI := coactionLeftAction k G D ρ
  SchemeAction.trivialObject (G.asOver (Spec (.of k))) (affineActionScheme k D)
    ⟨G.asOver (Spec (.of k)) ⊗ affineActionScheme k D,
      lift ((fst _ _)⁻¹) (snd _ _) ≫ coactionLeftArrow k G D ρ⟩

/-- The source projection arrow into the canonical atlas object.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightSourceArrow :
    coactionRightSource k G D ρ ⟶ coactionAtlasObject k G D ρ :=
  letI := coactionLeftAction k G D ρ
  (SchemeAction.trivialTorsorFunctor (G.asOver (Spec (.of k)))
    (affineActionScheme k D)).map
      (⟨snd _ _, 1, by simp⟩ : SchemeAction.ActionHom _ _ _ _)

/-- The target projection arrow into the canonical atlas object.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightTargetArrow :
    coactionRightTarget k G D ρ ⟶ coactionAtlasObject k G D ρ :=
  letI := coactionLeftAction k G D ρ
  (SchemeAction.trivialTorsorFunctor (G.asOver (Spec (.of k)))
    (affineActionScheme k D)).map
      (⟨lift ((fst _ _)⁻¹) (snd _ _) ≫ coactionLeftArrow k G D ρ, 1,
        by simp⟩ : SchemeAction.ActionHom _ _ _ _)

/-- The actual groupoid arrow whose parameter is the inverse left-action label.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightTransport : coactionRightSource k G D ρ ⟶ coactionRightTarget k G D ρ :=
  letI := coactionLeftAction k G D ρ
  (SchemeAction.trivialTorsorFunctor (G.asOver (Spec (.of k)))
    (affineActionScheme k D)).map
      (⟨𝟙 _, (fst _ _)⁻¹, by simp only [Category.id_comp]; rfl⟩ :
        SchemeAction.ActionHom (G.asOver (Spec (.of k))) (affineActionScheme k D)
          ⟨G.asOver (Spec (.of k)) ⊗ affineActionScheme k D, snd _ _⟩
          ⟨G.asOver (Spec (.of k)) ⊗ affineActionScheme k D,
            lift ((fst _ _)⁻¹) (snd _ _) ≫ coactionLeftArrow k G D ρ⟩)

/-- Pull back a Hopf coefficient from G into the ring on the right-arrow source.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRightCoefficient (M : CoactionQuotientAlgebras k G D ρ) (h : Γ(G, ⊤)) :
    M.obj.right.obj.obj (op (coactionRightSource k G D ρ)) :=
  (M.obj.hom.hom.app (op (coactionRightSource k G D ρ)))
    (ULift.up ((fst (G.asOver (Spec (.of k))) (affineActionScheme k D)).left.appTop h))

/-- The coaction is exactly the atlas descent transport, on every finite tensor expansion.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def IsAtlasCoaction (M : CoactionQuotientAlgebras k G D ρ)
    (B : HopfAction.EquivariantAffineAlgebra.{u, u, u, u + 1} k Γ(G, ⊤) D ρ)
    (e : B.algebra ≃+* coactionAtlasRing k G D ρ M) : Prop :=
  ∀ (b : B.algebra) (n : ℕ) (b' : Fin n → B.algebra) (h : Fin n → Γ(G, ⊤)),
    B.coaction.map b = ∑ i, b' i ⊗ₜ[k] h i →
    M.obj.right.obj.map (coactionRightTransport k G D ρ).op
      (M.obj.right.obj.map (coactionRightTargetArrow k G D ρ).op (e b)) =
      ∑ i, M.obj.right.obj.map (coactionRightSourceArrow k G D ρ).op (e (b' i)) *
        coactionRightCoefficient k G D ρ M (h i)

/-- Atlas-normalized descent, with all algebra maps, surjections and invariant sections.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Use the action-groupoid torsor comparison, then module descent (06WT).
The affine tilde/Gamma and tensor comparisons transport multiplication and unit;
fullness descends them and faithfulness checks associativity, commutativity and units.
Reparametrize a left arrow by its inverse to read a right coaction. Evaluate its
descent isomorphism on b tensor 1. Identity and cocycle become counitality and
coassociativity, and compatibility with the structure map becomes equivariance.
Conversely send b tensor l to rho(b) l. Its inverse uses the antipode; the Hopf
equations prove both inverse composites. Equality on tensor generators identifies
all algebra homomorphisms. Module descent preserves cokernels; affine tilde
detects zero cokernels, proving the surjection equivalence. Maps from the unit
module are determined by their value on 1, whose descent condition is exactly
invariance. Evaluation on the atlas gives the displayed ring isomorphism,
natural in all algebra maps. These are steps 6--10 of the node. -/
theorem affine_action_quasicoherent_descent
    [Smooth (G ↘ Spec (.of k))] [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] :
    ∃ (F : CoactionQuotientAlgebras k G D ρ ≌
          HopfAction.EquivariantAffineAlgebra.{u, u, u, u + 1} k Γ(G, ⊤) D ρ)
      (e : ∀ M : CoactionQuotientAlgebras k G D ρ,
        (F.functor.obj M).algebra ≃+* coactionAtlasRing k G D ρ M)
      (gamma : ∀ M : CoactionQuotientAlgebras k G D ρ,
        moduliGlobalSectionsRing M.obj.right ≃+*
          (F.functor.obj M).invariants),
      (∀ M, IsAtlasCoaction k G D ρ M (F.functor.obj M) (e M)) ∧
      (∀ (M : CoactionQuotientAlgebras k G D ρ) (d : D),
        e M ((F.functor.obj M).unit d) = coactionAtlasUnit k G D ρ M d) ∧
      (∀ (M N : CoactionQuotientAlgebras k G D ρ) (f : M ⟶ N)
        (b : (F.functor.obj M).algebra),
        e N ((F.functor.map f).map b) =
          (f.hom.right.hom.app (op (coactionAtlasObject k G D ρ))) (e M b)) ∧
      (∀ (M N : CoactionQuotientAlgebras k G D ρ) (f : M ⟶ N),
        IsSurjectiveModuliAlgebra f.hom ↔ Function.Surjective (F.functor.map f).map) ∧
      (∀ (M : CoactionQuotientAlgebras k G D ρ)
        (b : moduliGlobalSectionsRing M.obj.right),
        e M (gamma M b).val = b.val (op (coactionAtlasObject k G D ρ))) ∧
      (∀ (M N : CoactionQuotientAlgebras k G D ρ) (f : M ⟶ N)
        (b : moduliGlobalSectionsRing M.obj.right)
        (c : moduliGlobalSectionsRing N.obj.right),
        (∀ x, c.val x = (f.hom.right.hom.app x) (b.val x)) →
        (gamma N c).val = (F.functor.map f).map (gamma M b).val) := by
  sorry


variable (E : Type u) [CommRing E] [Algebra k E]
variable (σ : HopfAction.AlgebraCoaction k Γ(G, ⊤) E)
variable (f : D →ₐ[k] E)
variable (hf : σ.map.comp f =
  (Algebra.TensorProduct.map f (AlgHom.id k Γ(G, ⊤))).comp ρ.map)

/-- The actual scheme map dual to an equivariant algebra map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionChartArrow : affineActionScheme k E ⟶ affineActionScheme k D :=
  (Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of k))

/-- An equivariant algebra map gives exactly an equivariant left scheme map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Use hf on coordinate functions. The tensor map commutes with the factor
swap and with the Hopf antipode, so the left-action coordinate maps commute as well.
The affine Spec equivalence and its product comparison give the displayed equality. -/
theorem coactionChartArrow_equivariant
    (hf : σ.map.comp f =
      (Algebra.TensorProduct.map f (AlgHom.id k Γ(G, ⊤))).comp ρ.map) :
    coactionLeftArrow k G E σ ≫ coactionChartArrow k D E f =
      G.asOver (Spec (.of k)) ◁ coactionChartArrow k D E f ≫
        coactionLeftArrow k G D ρ := by
  sorry

/-- Change of equivariant target preserves the actual torsor and its action.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionChangeObject (x : (coactionQuotient k G E σ).obj) :
    (coactionQuotient k G D ρ).obj :=
  letI := coactionLeftAction k G D ρ
  letI := coactionLeftAction k G E σ
  letI : IsModHom (G.asOver (Spec (.of k))) (coactionChartArrow k D E f) :=
    ⟨coactionChartArrow_equivariant k G D ρ E σ f hf⟩
  { base := x.base
    space := x.space
    action := x.action
    projection := x.projection
    invariant := x.invariant
    local_trivial := x.local_trivial
    map := x.map ≫ coactionChartArrow k D E f
    equivariant := fun W g p ↦ by
      rw [← Category.assoc, x.equivariant, IsModHom.map_smul, Category.assoc] }

/-- Restriction between quotient stacks is postcomposition of the equivariant torsor map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionChange : BasedFunctor (coactionQuotient k G E σ) (coactionQuotient k G D ρ) :=
  letI := coactionLeftAction k G D ρ
  letI := coactionLeftAction k G E σ
  { obj := coactionChangeObject k G D ρ E σ f hf
    map a :=
      { base := a.base
        map := a.map
        cartesian := a.cartesian
        equivariant := a.equivariant
        commutes := by dsimp [coactionChangeObject]; rw [← Category.assoc, a.commutes] }
    map_id _ := SchemeAction.TorsorHom.ext rfl rfl
    map_comp _ _ := SchemeAction.TorsorHom.ext rfl rfl
    w := rfl }

/-- Literal restriction of an algebra sheaf along the specified quotient-stack map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def IsCoactionRestriction (M : CoactionQuotientAlgebras k G D ρ)
    (N : CoactionQuotientAlgebras k G E σ)
    (e : N.obj.right.obj ≅ (coactionChange k G D ρ E σ f hf).toFunctor.op ⋙ M.obj.right.obj) :
    Prop :=
  ∀ x, N.obj.hom.hom.app x ≫ e.hom.app x =
    M.obj.hom.hom.app (op ((coactionChange k G D ρ E σ f hf).obj x.unop))

/-- Restriction is an algebra sheaf and preserves quasi-coherence.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: An fppf covering of a torsor object is sent to the same covering of its
underlying scheme; its overlaps have the same pullback. Thus precomposition is
a sheaf. The structure ring at every object is unchanged, so the algebra map
restricts literally. Pullback of local free presentations proves quasi-coherence.
This is restriction along the map of quotient stacks, not tensor on invariant sections. -/
theorem coactionRestriction_exists (M : CoactionQuotientAlgebras k G D ρ) :
    ∃ (N : CoactionQuotientAlgebras k G E σ)
      (e : N.obj.right.obj ≅
        (coactionChange k G D ρ E σ f hf).toFunctor.op ⋙ M.obj.right.obj),
      IsCoactionRestriction k G D ρ E σ f hf M N e := by
  sorry

/-- The comparison arrow between the actual atlases is uniquely fixed on torsor spaces.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Take the identity on G times the map Spec E to Spec D. The product
square is cartesian. Left translation commutes with this map, and its orbit-map
equality is precisely coactionChartArrow_equivariant. These are exactly the
fields of the total torsor arrow, and the given space and base maps determine it. -/
theorem coactionChangeAtlasArrow_existsUnique :
    ∃! a : (coactionChange k G D ρ E σ f hf).obj (coactionAtlasObject k G E σ) ⟶
        coactionAtlasObject k G D ρ,
      coactionTorsorHom k G D ρ a = G.asOver (Spec (.of k)) ◁ coactionChartArrow k D E f ∧
      (coactionQuotient k G D ρ).p.map a = coactionChartArrow k D E f := by
  sorry

/-- The canonical atlas arrow, fixed uniquely rather than chosen arbitrarily.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionChangeAtlasArrow :
    (coactionChange k G D ρ E σ f hf).obj (coactionAtlasObject k G E σ) ⟶
      coactionAtlasObject k G D ρ :=
  Classical.choose (coactionChangeAtlasArrow_existsUnique k G D ρ E σ f hf)

/-- Restriction on atlas sections is the sheaf restriction along the canonical atlas arrow.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionRestrictionRingMap (M : CoactionQuotientAlgebras k G D ρ)
    (N : CoactionQuotientAlgebras k G E σ)
    (e : N.obj.right.obj ≅ (coactionChange k G D ρ E σ f hf).toFunctor.op ⋙ M.obj.right.obj) :
    coactionAtlasRing k G D ρ M →+* coactionAtlasRing k G E σ N :=
  (e.inv.app (op (coactionAtlasObject k G E σ))).hom.comp
    (M.obj.right.obj.map (coactionChangeAtlasArrow k G D ρ E σ f hf).op).hom

/-- The atlas section ring is a D-algebra by its specified structure map.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
instance coactionAtlasRing.baseAlgebra (M : CoactionQuotientAlgebras k G D ρ) :
    Algebra D (coactionAtlasRing k G D ρ M) :=
  (coactionAtlasUnit k G D ρ M).toAlgebra

/-- The complete tensor formula for restriction under equivariant scalar extension.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Restrict the sheaf literally to the target quotient. Its atlas over
Spec E is the pullback of the atlas sheaf on Spec D. The affine module pullback
comparison identifies its sections with B tensor_D E, and the algebra tensor
comparison gives multiplication and unit. Thus b restricts to b tensor 1 and the
new scalar a acts as 1 tensor a. Compatible global sections restrict by the same
formula, so the invariant-section identification commutes with restriction.
Naturality of the affine pullback comparison makes this compatible with every
algebra homomorphism and with successive scalar extensions. For the node take
D here to be D tensor_A C and E to be (D tensor_A C) tensor_C Cprime, with the
canonical tensor associativity identification. The formula is valid without
flatness or finite generation and asserts no isomorphism on tensor products of invariants. -/
theorem coactionRestriction_scalarExtension [Algebra D E] [IsScalarTower k D E]
    (h : σ.map.comp (IsScalarTower.toAlgHom k D E) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k D E)
        (AlgHom.id k Γ(G, ⊤))).comp ρ.map)
    (M : CoactionQuotientAlgebras k G D ρ) :
    ∃ (N : CoactionQuotientAlgebras k G E σ)
      (e : N.obj.right.obj ≅
        (coactionChange k G D ρ E σ (IsScalarTower.toAlgHom k D E) h).toFunctor.op ⋙
          M.obj.right.obj)
      (t : coactionAtlasRing k G E σ N ≃+* (coactionAtlasRing k G D ρ M) ⊗[D] E),
      IsCoactionRestriction k G D ρ E σ (IsScalarTower.toAlgHom k D E) h M N e ∧
      (∀ b, t (coactionRestrictionRingMap k G D ρ E σ
        (IsScalarTower.toAlgHom k D E) h M N e b) = b ⊗ₜ[D] 1) ∧
      (∀ a : E, t (coactionAtlasUnit k G E σ N a) = 1 ⊗ₜ[D] a) ∧
      (∀ (b : moduliGlobalSectionsRing M.obj.right)
        (c : moduliGlobalSectionsRing N.obj.right),
        (∀ x, (e.hom.app (op x)) (c.val (op x)) =
          b.val (op ((coactionChange k G D ρ E σ (IsScalarTower.toAlgHom k D E) h).obj x))) →
        t (c.val (op (coactionAtlasObject k G E σ))) =
          (@id (coactionAtlasRing k G D ρ M)
            (b.val (op (coactionAtlasObject k G D ρ)))) ⊗ₜ[D] 1) := by
  sorry

variable (ψ : BasedFunctor (coactionQuotient k G D ρ)
  (discreteModuli (yoneda.obj (affineActionScheme k A))))

/-- The map of the underlying test scheme to Spec A, with the based-functor transport.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionBaseObjectMap (x : (coactionQuotient k G D ρ).obj) :
    (coactionQuotient k G D ρ).p.obj x ⟶ affineActionScheme k A :=
  eqToHom (ψ.w_obj x).symm ≫ yoneda.preimage (ψ.obj x).hom

/-- Pullbacks of a base function form a compatible family on all torsor objects.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: The based functor sends any total arrow to a commutative triangle
over Spec A. Apply global sections contravariantly. Functoriality of Gamma
and the canonical based-object transports give equality of the two pullbacks. -/
theorem coactionBaseSection_compatible (a : A) :
    ∀ {x y : (coactionQuotient k G D ρ).objᵒᵖ} (g : x ⟶ y),
      (moduliStructurePresheaf (coactionQuotient k G D ρ)).map g
        (ULift.up ((coactionBaseObjectMap k G D ρ A ψ x.unop).left.appTop
          ((Scheme.ΓSpecIso (.of A)).inv a))) =
      ULift.up ((coactionBaseObjectMap k G D ρ A ψ y.unop).left.appTop
        ((Scheme.ΓSpecIso (.of A)).inv a)) := by
  sorry

/-- The actual structural map on global sections is pullback of regular functions.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent). -/
def coactionBaseSections : A →+* moduliGlobalSectionsRing
    (moduliStructureSheaf (coactionQuotient k G D ρ) (coactionQuotient_isFibred k G D ρ)) where
  toFun a := ⟨fun x ↦ ULift.up ((coactionBaseObjectMap k G D ρ A ψ x.unop).left.appTop
    ((Scheme.ΓSpecIso (.of A)).inv a)), coactionBaseSection_compatible k G D ρ A ψ a⟩
  map_one' := Subtype.ext (funext (fun _ ↦ congrArg ULift.up
    (by simp only [map_one])))
  map_mul' a b := Subtype.ext (funext (fun _ ↦ congrArg ULift.up
    (by simp only [map_mul])))
  map_zero' := Subtype.ext (funext (fun _ ↦ congrArg ULift.up
    (by simp only [map_zero])))
  map_add' a b := Subtype.ext (funext (fun _ ↦ congrArg ULift.up
    (by simp only [map_add])))

/-- The structure-section formula is the given base map, hence c maps to 1 tensor c.
Source: Stacks 03LF, 04WM and 06WT
(blueprint: lem-sfb-affine-action-quasicoherent-descent).

Proof: Evaluate the normalized structural functor at the identity atlas
object. Its comparison to Spec(algebraMap A D) makes pullback of a base function
exactly algebraMap A D. The Gamma-Spec counit cancels its inverse. Apply this
with A=C and D=D tensor_A C: the algebra map C to the tensor algebra is
includeRight, which is c mapping to 1 tensor c. Together with the atlas-normalized
structure-section isomorphism this proves the final structural-map clause. -/
theorem affine_action_structure_baseMap
    (hψ : Nonempty (ModuliTwoIso ((coactionAtlas k G D ρ).comp ψ)
      (discreteModuliMap (yoneda.map (coactionBaseArrow k D A))))) :
    ∀ a : A, (Scheme.ΓSpecIso (.of D)).hom
      ((coactionBaseSections k G D ρ A ψ a).val
        (op (coactionAtlasObject k G D ρ))).down = algebraMap A D a := by
  sorry

end AlgebraicGeometry
