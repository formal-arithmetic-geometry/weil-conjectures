module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Sheaf.RingTheory.HopfActionModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Rational coactions on cohomology of linearized quasi-coherent modules

Source: Stacks Project, coherent.tex, Tag 02KH, and cohomology.tex, Tags 01F7--01FB.
The universal-element construction and boundary compatibility are agent-written consequences.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wC wD

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.LinearizedCohomology

open Scheme.Modules

variable {k : Type u} [Field k]
variable {G : Grp (Over (Spec (.of k)))} {Y : Over (Spec (.of k))}

/-- Identify the explicit tensor pullback with the existing categorical pullback by
uniqueness of left adjoints to the same direct image. This transports the recorded
linearization, without introducing a second notion of linearization.
Source: Stacks, Tags 0096--0097.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def tensorComparison {X Z : Scheme.{u}} (f : X ⟶ Z) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

/-- The existing linearization in the explicit tensor-pullback model.
Source: Stacks, Tag 0097; the sheaf cocycle in the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def tensorLift (a : ModObj G.X Y) {E : Y.left.Modules}
    (D : GroupSchemeLinearization.Linearization a E)
    (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ Y) :
    (tensorPullback x.left).obj E ≅
      (tensorPullback (GroupSchemeLinearization.act a T g x).left).obj E :=
  (tensorComparison x.left).app E ≪≫ D.lift T g x ≪≫
    ((tensorComparison (GroupSchemeLinearization.act a T g x).left).app E).symm

/-- Equivariant coefficient maps: equality of sheaf maps on all test schemes.
Source: Stacks, Tag 01F7; coefficient naturality and the node's linearization square.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def IsEquivariant (a : ModObj G.X Y) {E F : Y.left.Modules}
    (D : GroupSchemeLinearization.Linearization a E)
    (D' : GroupSchemeLinearization.Linearization a F) (f : E ⟶ F) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : T ⟶ G.X) (x : T ⟶ Y),
    (tensorPullback x.left).map f ≫ (tensorLift a D' T g x).hom =
      (tensorLift a D T g x).hom ≫
        (tensorPullback (GroupSchemeLinearization.act a T g x).left).map f

/-- The affine test scheme of a commutative k-algebra, including the zero algebra.
Source: Stacks, Tag 02KH.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
abbrev test (A : Type u) [CommRing A] [Algebra k A] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The actual scalar extension of Y is the product in schemes over k.
Source: Stacks, Tag 02KH.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
abbrev base (Y : Over (Spec (.of k))) (A : Type u) [CommRing A] [Algebra k A] :=
  Y ⊗ test (k := k) A

/-- The pullback coefficient module on Y_A, using the explicit tensor pullback.
Source: Stacks, Tag 02KH.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
abbrev baseModule (E : Y.left.Modules) (A : Type u) [CommRing A] [Algebra k A] :=
  (tensorPullback (fst Y (test (k := k) A)).left).obj E

/-- Cohomology over A, by restricting the established right-derived global sections
along A to the global functions of Y_A. This also works for A = 0.
Source: Stacks, Tags 01DZ and 02KH.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def baseH (E : Y.left.Modules) (A : Type u) [CommRing A] [Algebra k A] (i : ℕ) :
    ModuleCat.{u} A :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd Y (test (k := k) A)).left.appTop).hom)).obj
      ((RingedSpace.moduleCohomology (base Y A).left.toRingedSpace i).obj (baseModule E A))

/-- Inverse translation on Y_A, as an actual morphism of schemes over k.
Source: Stacks, Tag 01F7; step 2 of the universal-element construction.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def inverseTranslation (a : ModObj G.X Y) (A : Type u) [CommRing A] [Algebra k A]
    (g : test (k := k) A ⟶ G.X) : base Y A ⟶ base Y A :=
  lift (GroupSchemeLinearization.act a (base Y A)
    (snd Y (test (k := k) A) ≫ g⁻¹) (fst Y (test (k := k) A)))
    (snd Y (test (k := k) A))

/-- The canonical coefficient isomorphism t_g^* E_A to E_A. It is the inverse of
θ at (g⁻¹,y), equivalently θ at (g,g⁻¹y), by the sheaf cocycle.
Source: Stacks, Tag 0097; step 2 of the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def actionCoefficient (a : ModObj G.X Y) {E : Y.left.Modules}
    (D : GroupSchemeLinearization.Linearization a E)
    (A : Type u) [CommRing A] [Algebra k A] (g : test (k := k) A ⟶ G.X) :
    (tensorPullback (inverseTranslation a A g).left).obj (baseModule E A) ≅
      baseModule E A :=
  ((tensorPullbackSectionComp (inverseTranslation a A g).left
    (fst Y (test (k := k) A)).left).app E).symm ≪≫
  eqToIso (congrArg (fun f : (base Y A).left ⟶ Y.left ↦ (tensorPullback f).obj E)
    (congrArg Over.Hom.left
      (lift_fst (GroupSchemeLinearization.act a (base Y A)
        (snd Y (test (k := k) A) ≫ g⁻¹) (fst Y (test (k := k) A)))
        (snd Y (test (k := k) A))))) ≪≫
  (tensorLift a D (base Y A) (snd Y (test (k := k) A) ≫ g⁻¹)
    (fst Y (test (k := k) A))).symm

/-- The cohomological action is inverse-translation pullback followed by its canonical
coefficient map, on the recorded right-derived module cohomology.
Source: Stacks, Tags 01F7--01FB; step 2 of the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def action (a : ModObj G.X Y) {E : Y.left.Modules}
    (D : GroupSchemeLinearization.Linearization a E)
    (A : Type u) [CommRing A] [Algebra k A] (g : test (k := k) A ⟶ G.X) (i : ℕ)
    (z : baseH E A i) : baseH E A i :=
  ((RingedSpace.moduleCohomology (base Y A).left.toRingedSpace i).map
    (actionCoefficient a D A g).hom)
      (moduleCohomologyPullback (inverseTranslation a A g).left (baseModule E A) i z)

/-- The recorded k-linear cohomology morphism induced by a coefficient morphism.
Source: Stacks, Tag 01DZ.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def map {E F : Y.left.Modules} (f : E ⟶ F) (i : ℕ) :
    scalarCohomology Y.hom E i →ₗ[k] scalarCohomology Y.hom F i :=
  ((ModuleCat.restrictScalars (scalarMap Y.hom ⊤)).map
    ((RingedSpace.moduleCohomology Y.left.toRingedSpace i).map f)).hom

/-- The canonical cohomological boundary with the k-vector-space structure restricted
from the global functions, using the recorded boundary rather than an arbitrary delta.
Source: Stacks, Tags 01DZ and 0B8S.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def boundary
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings Y.left.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex Y.left.Modules) (hS : S.ShortExact) (i : ℕ) :
    scalarCohomology Y.hom S.X₃ i →ₗ[k] scalarCohomology Y.hom S.X₁ (i + 1) :=
  ((ModuleCat.restrictScalars (scalarMap Y.hom ⊤)).map
    (RingedSpace.moduleCohomologyBoundary Y.left.toRingedSpace S hS i)).hom

/-- Degree-zero identification with sections via the canonical right-derived-zero isomorphism.
Source: Stacks, Tag 01DZ.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def zeroSection (E : Y.left.Modules) (A : Type u) [CommRing A] [Algebra k A]
    (z : baseH E A 0) : Γ(baseModule E A, ⊤) :=
  letI : PreservesFiniteLimits
      (RingedSpace.globalSectionsFunctor (base Y A).left.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings (base Y A).left.toRingedSpace) (op ⊤)))
  (((RingedSpace.globalSectionsFunctor
    (base Y A).left.toRingedSpace).rightDerivedZeroIsoSelf).hom.app (baseModule E A)) z

/-- The section action, given by the actual unit and linearization coefficient sheaf maps.
It is θ at (g,g⁻¹y) applied to the pullback of s along inverse translation.
Source: Stacks, Tag 01F7; the degree-zero formula in the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def sectionAction (a : ModObj G.X Y) {E : Y.left.Modules}
    (D : GroupSchemeLinearization.Linearization a E)
    (A : Type u) [CommRing A] [Algebra k A] (g : test (k := k) A ⟶ G.X)
    (s : Γ(baseModule E A, ⊤)) : Γ(baseModule E A, ⊤) :=
  (((tensorPullbackSectionAdjunction (inverseTranslation a A g).left).unit.app
    (baseModule E A)) ≫ (pushforward (inverseTranslation a A g).left).map
      (actionCoefficient a D A g).hom).app ⊤ s

/-- Evaluation of a right-coordinate coaction at an algebra-valued point, with scalar
extension in the order A tensor V. The point is specified by its coordinate algebra map.
Source: Milne, Algebraic Groups, Remark 4.1; the universal-element construction in the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def evaluate [IsAffine G.X.left] {V : Type u} [AddCommGroup V] [Module k V]
    (c : V →ₗ[k] V ⊗[k] Γ(G.X.left, ⊤))
    (A : Type u) [CommRing A] [Algebra k A] (x : Γ(G.X.left, ⊤) →ₐ[k] A) :
    V →ₗ[k] A ⊗[k] V :=
  (TensorProduct.comm k V A).toLinearMap ∘ₗ x.toLinearMap.lTensor V ∘ₗ c

/-- Extend evaluation A-linearly to A tensor V, by b tensor z mapping to b times
its evaluation on z. This is the actual evaluation operator of the coaction.
Source: Milne, Remark 4.1; step 5 of the node.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction) -/
def evaluatedAction [IsAffine G.X.left] {V : Type u} [AddCommGroup V] [Module k V]
    (c : V →ₗ[k] V ⊗[k] Γ(G.X.left, ⊤))
    (A : Type u) [CommRing A] [Algebra k A] (x : Γ(G.X.left, ⊤) →ₐ[k] A) :
    A ⊗[k] V →ₗ[k] A ⊗[k] V :=
  TensorProduct.lift
    ((Algebra.lsmul k k (A ⊗[k] V)).toLinearMap.compl₂ (evaluate c A x))

/-- All cohomology groups of a linearized quasi-coherent module carry the canonical
rational coaction, characterized by the action over every commutative algebra.
The scalar-extension equivalences are fixed by b tensor z mapping to b times p* z.
The family is natural in equivariant sheaf maps, and the canonical cohomology boundary
is equivariant for every short exact linearized sequence.

Source: Stacks Project, coherent.tex, Tag 02KH, and cohomology.tex, Tags 01F7--01FB.
(blueprint: lem-sfb-linearized-qcoherent-cohomology-coaction)

Proof:
1. Every k-module is flat (lem-weil-pbc-module-over-field-flat), so every k-algebra A
   is flat, including A=0 (def-weil-pbc-flat-ring-map, def-weil-flat-morphism).
   The specified flat comparison is bijective by lem-pc-flat-cohomology-separated
   and def-pc-flat-cohomology-comparison. Transport it from Ext to right-derived
   module cohomology by new-module-cohomology-ext-pullback-comparison. Naturality
   for scalar multiplication identifies its formula with b times p* z.
2. Inverse translation t_g and the sheaf linearization give actionCoefficient q_g.
   Compose its cohomology map with t_g* using def-weil-pbc-module-cohomology-fmap.
   The basic-properties node gives linearity and the displayed degree-zero formula.
3. Pull the sheaf cocycle back at (g,h,(gh)⁻¹y). It gives t_gh=t_h t_g and
   q_gh=q_g t_g*(q_h). The functoriality and basic-properties nodes give r(g)r(h)=r(gh)
   and r(e)=1, hence inverse r(g⁻¹). These are sheaf equalities on all test schemes.
4. For every algebra map A to A', functoriality gives compatibility both for the
   pure-tensor base-change formula and for r(g); no flatness of A to A' is needed.
5. Take A=k[G] and its universal point. Apply its action to beta(1 tensor z),
   then beta inverse and the tensor flip. Algebra-map naturality gives the evaluation
   formula for every A-point. Thus the characterization fixes a canonical coaction.
6. Evaluate at the two universal points over k[G] tensor k[G]. The group law of
   step 3 proves coassociativity as an equality of tensors; evaluation at the unit
   proves the counit identity. This uses no density or reducedness assertion.
7. A map commuting with the linearization commutes with q_g and with beta.
   Coefficient naturality of the fmap-functorial node, at the universal point,
   proves the naturality equation for c in every degree.
8. Flat base change preserves the short exact row, by the flat-base-change and
   flat-module-pullback-exact-pushforward-injective nodes. Apply
   lem-sfb-module-cohomology-fmap-boundary to the base-change units, to scalar
   multiplication on the row, and to q_g over inverse translation. The resulting
   identities show that beta and r(g) commute with the canonical boundaries.
   Evaluate at the universal point to get the final comodule equation. Step 7
   handles the other maps in the long exact sequence of pqf-def-cohomology. -/
theorem exists_coaction
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (Y : Over (Spec (.of k))) [CompactSpace Y.left] [IsSeparated Y.hom]
    (a : ModObj G.X Y) :
    ∃ c : ∀ (E : Y.left.Modules) (_ : E.IsQuasicoherent)
      (_ : GroupSchemeLinearization.Linearization a E) (i : ℕ),
      scalarCohomology Y.hom E i →ₗ[k]
        scalarCohomology Y.hom E i ⊗[k] Γ(G.X.left, ⊤),
      (∀ (E : Y.left.Modules) (hE : E.IsQuasicoherent)
        (D : GroupSchemeLinearization.Linearization a E) (i : ℕ),
        HopfAction.Coassociative k Γ(G.X.left, ⊤)
          (scalarCohomology Y.hom E i) (c E hE D i) ∧
        HopfAction.Counital k Γ(G.X.left, ⊤)
          (scalarCohomology Y.hom E i) (c E hE D i) ∧
        ∃ beta : ∀ (A : Type u) [CommRing A] [Algebra k A],
          A ⊗[k] scalarCohomology Y.hom E i ≃ₗ[A] baseH E A i,
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (b : A) (z : scalarCohomology Y.hom E i),
            beta A (b ⊗ₜ[k] z) = b •
              @id (baseH E A i)
                (moduleCohomologyPullback (fst Y (test (k := k) A)).left E i z)) ∧
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (x : Γ(G.X.left, ⊤) →ₐ[k] A) (z : A ⊗[k] scalarCohomology Y.hom E i),
            beta A (evaluatedAction (c E hE D i) A x z) =
              action a D A
                ((Spec.map (CommRingCat.ofHom x.toRingHom)).asOver (Spec (.of k)) ≫
                  G.X.left.isoSpec.inv.asOver (Spec (.of k))) i (beta A z))) ∧
      (∀ (E : Y.left.Modules) (_ : E.IsQuasicoherent)
        (D : GroupSchemeLinearization.Linearization a E) (A : Type u) [CommRing A] [Algebra k A]
        (g : test (k := k) A ⟶ G.X) (z : baseH E A 0),
        zeroSection E A (action a D A g 0 z) = sectionAction a D A g (zeroSection E A z)) ∧
      (∀ (E F : Y.left.Modules) (hE : E.IsQuasicoherent) (hF : F.IsQuasicoherent)
        (D : GroupSchemeLinearization.Linearization a E)
        (D' : GroupSchemeLinearization.Linearization a F)
        (f : E ⟶ F) (_ : IsEquivariant a D D' f) (i : ℕ),
        (map f i).rTensor Γ(G.X.left, ⊤) ∘ₗ c E hE D i = c F hF D' i ∘ₗ map f i) ∧
      (∀ [HasDerivedCategory.{wC}
          (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace))]
        [HasDerivedCategory.{wD}
          (ModuleCat.{u} ((moduleRings Y.left.toRingedSpace).obj.obj (op ⊤)))]
        (S : ShortComplex Y.left.Modules) (hS : S.ShortExact)
        (h₁ : S.X₁.IsQuasicoherent) (_ : S.X₂.IsQuasicoherent)
        (h₃ : S.X₃.IsQuasicoherent)
        (D₁ : GroupSchemeLinearization.Linearization a S.X₁)
        (D₂ : GroupSchemeLinearization.Linearization a S.X₂)
        (D₃ : GroupSchemeLinearization.Linearization a S.X₃)
        (_ : IsEquivariant a D₁ D₂ S.f) (_ : IsEquivariant a D₂ D₃ S.g) (i : ℕ),
        (boundary S hS i).rTensor Γ(G.X.left, ⊤) ∘ₗ c S.X₃ h₃ D₃ i =
          c S.X₁ h₁ D₁ (i + 1) ∘ₗ boundary S hS i) := by
  sorry

end AlgebraicGeometry.LinearizedCohomology
