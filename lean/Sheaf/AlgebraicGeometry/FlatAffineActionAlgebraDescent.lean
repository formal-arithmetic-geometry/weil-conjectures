module

public import Sheaf.AlgebraicGeometry.FlatAffineActionStackPresentation
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Sheaf.RingTheory.EquivariantCoactionAlgebra
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.AffineGroupTorsorStackification
import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Algebra descent on a flat affine action quotient

Source: Stacks Project, Tag 06WT and Tag 03LF
(blueprint: lem-sfb-flat-affine-action-algebra-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj
namespace AlgebraicGeometry.SchemeAction
variable (k : Type u) [Field k] (H : Scheme.{u}) [H.Over (Spec (.of k))]
variable [GrpObj (H.asOver (Spec (.of k)))] [IsAffine H]
variable (E : Type u) [CommRing E] [Algebra k E]
variable [ModObj (H.asOver (Spec (.of k))) (affineActionScheme k E)]

/-- Affineness of the group structure map follows from affineness of both schemes.
Source: Stacks 01S5 (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
instance actionAlgebraAffineHom : IsAffineHom (H.asOver (Spec (.of k))).hom :=
  @isAffineHom_of_isAffine H (Spec (.of k)) (H ↘ Spec (.of k))
    (inferInstanceAs (IsAffine H)) inferInstance

/-- The chart object is the actual trivial torsor with its orbit map.
Source: Stacks 04WM (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraChart {T : Over (Spec (.of k))} (p : T ⟶ affineActionScheme k E) :=
  trivialObject (H.asOver (Spec (.of k))) (affineActionScheme k E) ⟨T, p⟩

/-- Restriction from the universal trivial torsor to a scheme point of the atlas.
Source: Stacks 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraChartArrow {T : Over (Spec (.of k))} (p : T ⟶ affineActionScheme k E) :
    actionAlgebraChart k H E p ⟶ actionAlgebraChart k H E (𝟙 (affineActionScheme k E)) :=
  (trivialTorsorFunctor (H.asOver (Spec (.of k))) (affineActionScheme k E)).map
    (⟨p, 1, by simp⟩ : ActionHom (H.asOver (Spec (.of k))) (affineActionScheme k E)
      ⟨T, p⟩ ⟨affineActionScheme k E, 𝟙 _⟩)

/-- The right action underlying the coaction is h inverse acting on x.
Source: Stacks 03LF (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraRightPoint :
    affineActionScheme k E ⊗ H.asOver (Spec (.of k)) ⟶ affineActionScheme k E :=
  (snd (affineActionScheme k E) (H.asOver (Spec (.of k))))⁻¹ •
    fst (affineActionScheme k E) (H.asOver (Spec (.of k)))

/-- The inverse presentation arrow goes from x to h inverse acting on x.
Its contravariant restriction therefore transports source coordinates to target coordinates.
Source: Stacks 03LF, 04WM (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraTransport :
    actionAlgebraChart k H E (fst (affineActionScheme k E) (H.asOver (Spec (.of k)))) ⟶
      actionAlgebraChart k H E (actionAlgebraRightPoint k H E) :=
  (trivialTorsorFunctor (H.asOver (Spec (.of k))) (affineActionScheme k E)).map
    (⟨𝟙 _, (snd (affineActionScheme k E) (H.asOver (Spec (.of k))))⁻¹,
      by simp [actionAlgebraRightPoint]⟩ :
      ActionHom (H.asOver (Spec (.of k))) (affineActionScheme k E)
        ⟨_, fst (affineActionScheme k E) (H.asOver (Spec (.of k)))⟩
        ⟨_, actionAlgebraRightPoint k H E⟩)

variable [Algebra.FiniteType k E]
variable [LocallyOfFiniteType (H.asOver (Spec (.of k))).hom]
variable [QuasiCompact (H.asOver (Spec (.of k))).hom]

/-- The canonical fibred structure, supplied by the published presentation theorem.
Source: Stacks 06WT, 04WM (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
abbrev actionAlgebraFibred :
    IsFibredInGroupoids (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E)) :=
  (flat_affine_action_stack_presentation.{u, u, u + 1, 0, 0} k E (H.asOver (Spec (.of k)))).1.1.1

/-- The full category of quasi-coherent algebras on this actual torsor quotient.
Source: Stacks 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
abbrev ActionQuasiCoherentAlgebras :=
  ObjectProperty.FullSubcategory
    (IsQuasicoherentModuliAlgebra
      (F := torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E))
      (hF := actionAlgebraFibred k H E))

/-- Pullback of an atlas algebra section to a test point of the atlas.
Source: Stacks 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraRestriction (A : ActionQuasiCoherentAlgebras k H E)
    {T : Over (Spec (.of k))} (p : T ⟶ affineActionScheme k E) :=
  A.obj.right.obj.map (actionAlgebraChartArrow k H E p).op

/-- The structure algebra is quasi-coherent.
Source: Stacks 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent).
Proof: on each slice the structure module is free of rank one; the identity is its
one-generator presentation. Thus it satisfies the local free presentation predicate. -/
theorem actionStructureAlgebra_quasiCoherent :
    IsQuasicoherentModuliAlgebra
      (Under.mk (𝟙 (moduliStructureSheaf
        (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E))
        (actionAlgebraFibred k H E)))) := by
  sorry

/-- The actual structure algebra, with its identity structure map.
Source: Stacks 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionStructureAlgebra : ActionQuasiCoherentAlgebras k H E :=
  ⟨Under.mk (𝟙 (moduliStructureSheaf
      (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E))
      (actionAlgebraFibred k H E))), actionStructureAlgebra_quasiCoherent k H E⟩

/-- The coefficient of a regular function on H in the target chart algebra.
Source: Stacks 06WT, 03LF (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionAlgebraCoefficient (A : ActionQuasiCoherentAlgebras k H E) (c : Γ(H, ⊤)) :=
  A.obj.hom.hom.app
    (op (actionAlgebraChart k H E
      (fst (affineActionScheme k E) (H.asOver (Spec (.of k))))))
    (ULift.up ((snd (affineActionScheme k E) (H.asOver (Spec (.of k)))).left.appTop c))

/-- The source coaction is the one dual to the inverse left action.
The finite-sum formula determines it uniquely by the affine tensor comparison.
Source: Stacks 03LF (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def IsActionAlgebraCoaction (ρ : HopfAction.AlgebraCoaction k Γ(H, ⊤) E) : Prop :=
  ∀ (e : E) (n : ℕ) (a : Fin n → E) (c : Fin n → Γ(H, ⊤)),
    ρ.map e = ∑ i, a i ⊗ₜ[k] c i →
      (actionAlgebraRightPoint k H E).left.appTop ((Scheme.ΓSpecIso (.of E)).inv e) =
        ∑ i, (fst (affineActionScheme k E) (H.asOver (Spec (.of k)))).left.appTop
          ((Scheme.ΓSpecIso (.of E)).inv (a i)) *
          (snd (affineActionScheme k E) (H.asOver (Spec (.of k)))).left.appTop (c i)

/-- The map from a torsor object to the invariant spectrum supplied by a based functor.
Source: Stacks 04WM, 06WT (blueprint: lem-sfb-flat-affine-action-algebra-descent). -/
def actionInvariantObjectMap
    (φ : BasedFunctor (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E))
      (discreteModuli (yoneda.obj (affineInvariantSpectrum k E
        (H.asOver (Spec (.of k)))))))
    (x : (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E)).obj) :
    x.base ⟶ affineInvariantSpectrum k E (H.asOver (Spec (.of k))) :=
  eqToHom (φ.w_obj x).symm ≫ yoneda.preimage (φ.obj x).hom

/-- Pullback along the actual trivial-torsor atlas and affine sections give algebra
 descent, identify surjections in both directions, and give natural invariant sections.
 The final normalized map is the map induced by the invariant morphism.
 Source: Stacks 06WT and 03LF (blueprint: lem-sfb-flat-affine-action-algebra-descent).

 Proof:
 1. Identify the action groupoid with s(x,h)=h inverse acting on x and t(x,h)=x.
    Its arrow to the torsor quotient is h, so the inverse arrow used for restriction
    has label h inverse. The torsor stackification identifies its atlas with pi.
 2. Apply lem-sfb-groupoid-module-descent-tensor-cokernel. On the affine atlas use
    lem-weil-pbc-affine-tilde-gamma-adjunction, the affine pullback section comparison,
    and the affine tensor section comparison. Fullness descends multiplication and
    unit; faithfulness checks associativity, commutativity, unit laws and all maps.
 3. Apply lem-sfb-hopf-coaction-linearization. Multiplicativity of the descended
    product and compatibility of the unit say exactly that the module coaction is
    an algebra coaction extending rho_E. Its generator formula is the displayed
    finite-sum transport formula; it fixes the functor as atlas pullback.
 4. Local surjectivity is vanishing of the module-sheaf cokernel. Module descent
    and lem-weil-pbc-quasi-coherent-module-cokernel-image identify this cokernel
    with D prime modulo the image of D. Thus it vanishes exactly for a surjection.
 5. A section is a module map from the structure module, by evaluation at one.
    Full faithfulness identifies it with an equivariant E-linear map E to D.
    Its value d at one satisfies rho_D(d)=d tensor one, and conversely every such d
    defines the map e to ed. Restriction preserves all ring operations and commutes
    with every algebra map, giving the stated natural ring isomorphisms.
 6. For the structure algebra, atlas restriction is E. The presentation theorem's
    invariant morphism restricts to the invariant inclusion. Therefore its map on
    global sections, followed by the invariant identification, sends e to e.
    All module and algebra constructions above allow arbitrary generators. -/
theorem flat_affine_action_algebra_descent :
    ∃ ρ : HopfAction.AlgebraCoaction k Γ(H, ⊤) E,
      IsActionAlgebraCoaction k H E ρ ∧
      ∃ F : ActionQuasiCoherentAlgebras k H E ≌
          HopfAction.EquivariantAlgebra.{u, u, u, u + 1} k Γ(H, ⊤) E ρ,
        ∃ j : ∀ A : ActionQuasiCoherentAlgebras k H E,
            (F.functor.obj A).algebra ≃+*
              A.obj.right.obj.obj
                (op (actionAlgebraChart k H E (𝟙 (affineActionScheme k E)))),
          (∀ (A : ActionQuasiCoherentAlgebras k H E) (e : E),
            j A ((F.functor.obj A).structureMap e) =
              A.obj.hom.hom.app
                (op (actionAlgebraChart k H E (𝟙 (affineActionScheme k E))))
                (ULift.up ((Scheme.ΓSpecIso (.of E)).inv e))) ∧
          (∀ (A B : ActionQuasiCoherentAlgebras k H E) (f : A ⟶ B)
            (d : (F.functor.obj A).algebra),
            j B ((F.functor.map f).val d) =
              f.hom.right.hom.app
                (op (actionAlgebraChart k H E (𝟙 (affineActionScheme k E)))) (j A d)) ∧
          (∀ (A : ActionQuasiCoherentAlgebras k H E) (d : (F.functor.obj A).algebra)
            (n : ℕ) (a : Fin n → (F.functor.obj A).algebra) (c : Fin n → Γ(H, ⊤)),
            (F.functor.obj A).coaction.map d = ∑ i, a i ⊗ₜ[k] c i →
              A.obj.right.obj.map (actionAlgebraTransport k H E).op
                (actionAlgebraRestriction k H E A (actionAlgebraRightPoint k H E) (j A d)) =
                ∑ i, actionAlgebraRestriction k H E A
                  (fst (affineActionScheme k E) (H.asOver (Spec (.of k)))) (j A (a i)) *
                  actionAlgebraCoefficient k H E A (c i)) ∧
          (∀ (A B : ActionQuasiCoherentAlgebras k H E) (f : A ⟶ B),
            IsSurjectiveModuliAlgebra f.hom ↔ Function.Surjective (F.functor.map f).val) ∧
          ∃ r : ∀ A : ActionQuasiCoherentAlgebras k H E,
              moduliGlobalSectionsRing A.obj.right ≃+*
                HopfAction.EquivariantAlgebra.invariants (F.functor.obj A),
            (∀ (A : ActionQuasiCoherentAlgebras k H E)
              (z : moduliGlobalSectionsRing A.obj.right),
              j A (r A z).val =
                z.val (op (actionAlgebraChart k H E (𝟙 (affineActionScheme k E))))) ∧
            (∀ (A B : ActionQuasiCoherentAlgebras k H E) (f : A ⟶ B)
              (z : moduliGlobalSectionsRing A.obj.right)
              (z' : moduliGlobalSectionsRing B.obj.right),
              (∀ x, z'.val x = f.hom.right.hom.app x (z.val x)) →
                (F.functor.map f).val (r A z).val = (r B z').val) ∧
            ∃ φ : BasedFunctor
                (torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E))
                (discreteModuli (yoneda.obj
                  (affineInvariantSpectrum k E (H.asOver (Spec (.of k)))))),
              Nonempty (ModuliTwoIso
                ((quotientAtlas (H.asOver (Spec (.of k))) (affineActionScheme k E)).comp φ)
                (discreteModuliMap (yoneda.map
                  (affineInvariantProjection k E (H.asOver (Spec (.of k))))))) ∧
              ∃ smap : affineInvariants k E (H.asOver (Spec (.of k))) →+*
                  moduliGlobalSectionsRing (actionStructureAlgebra k H E).obj.right,
                (∀ (e : affineInvariants k E (H.asOver (Spec (.of k))))
                  (x : (torsorGroupoid (H.asOver (Spec (.of k)))
                    (affineActionScheme k E)).obj),
                  (smap e).val (op x) = ULift.up
                    ((actionInvariantObjectMap k H E φ x).left.appTop
                      ((Scheme.ΓSpecIso (.of
                        (affineInvariants k E (H.asOver (Spec (.of k)))))).inv e))) ∧
                ∀ e : affineInvariants k E (H.asOver (Spec (.of k))),
                  j (actionStructureAlgebra k H E)
                    (r (actionStructureAlgebra k H E) (smap e)).val =
                    ULift.up ((Scheme.ΓSpecIso (.of E)).inv e.val) := by
  sorry

end AlgebraicGeometry.SchemeAction
