/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Descent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # Formal functions for proper algebraic spaces over an affine base

Source: Stacks Project, spaces-cohomology.tex, Tag 08AZ (theorem-formal-functions),
and Tag 08B1 (lemma-formal-functions-stalk), final paragraph
(blueprint: lem-sfb-space-affine-formal-functions).

Positive level n+1 is indexed by n : ℕ. Cohomology uses injective resolutions in ALL
module sheaves on the existing equivalent small ringed model. The roof normalization
specifies the restriction maps, including their ordinary tensor units. The last scalar
formula expresses linearity over the completed ring using its coordinate actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (a : Y.left ≅ Spec (.of A))

/-- The scheme Spec(A/I^(n+1)), with its given map to the base scheme S.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalBase (I : Ideal A) (n : ℕ) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ a.inv ≫ Y.hom)

/-- The quotient morphism as a scheme over S.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalBaseOverMap (I : Ideal A) (n : ℕ) :
    affineFormalBase A Y a I n ⟶ Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ a.inv)

/-- The canonical quotient morphism to the represented affine base.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalBaseMap (I : Ideal A) (n : ℕ) :
    schemeSpace (affineFormalBase A Y a I n) ⟶ schemeSpace Y :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map
    (affineFormalBaseOverMap A Y a I n))

/-- The scheme quotient transition, retaining its map to S.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalBaseTransition (I : Ideal A) (n m : ℕ) (h : n ≤ m) :
    affineFormalBase A Y a I n ⟶ affineFormalBase A Y a I m :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h))))) (by
      dsimp [affineFormalBase]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp]
      rfl)

variable {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)

/-- The actual sheaf fibre product X ×_Spec(A) Spec(A/I^(n+1)).
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalSpace (I : Ideal A) (n : ℕ) : AlgebraicSpace S :=
  enlargedFibreProduct f (affineFormalBaseMap A Y a I n)

/-- The closed-fibre projection j_(n+1) to X.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalι (I : Ideal A) (n : ℕ) : affineFormalSpace A Y a f I n ⟶ X :=
  enlargedFibreProductFst f (affineFormalBaseMap A Y a I n)

/-- The prescribed tensor pullback F_(n+1), functorially in F.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalModule (I : Ideal A) (n : ℕ) : X.Modules ⥤
    (affineFormalSpace A Y a f I n).Modules :=
  moduleTensorPullback (affineFormalι A Y a f I n)

/-- Cohomology with its actual affine-base A-action, derived in all module sheaves.
Source: Stacks 08AZ (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalH (q : ℕ) : X.Modules ⥤ ModuleCat.{u} A :=
  X.smallModuleRestriction ⋙ (affineScalarSections A Y a X f).rightDerived q

/-- The cohomology of the infinitesimal fibre with scalars restricted to A.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalHn (I : Ideal A) (q n : ℕ) : X.Modules ⥤ ModuleCat.{u} A :=
  affineFormalModule A Y a f I n ⋙
    affineFormalH A Y a (affineFormalι A Y a f I n ≫ f) q

/-- The canonical embedding of the smaller thickening into the larger one.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalTransition (I : Ideal A) (n m : ℕ) (h : n ≤ m) :
    affineFormalSpace A Y a f I n ⟶ affineFormalSpace A Y a f I m :=
  ObjectProperty.homMk (Limits.pullback.map f.hom (affineFormalBaseMap A Y a I n).hom
    f.hom (affineFormalBaseMap A Y a I m).hom (𝟙 X.obj)
    ((Scheme.fppfTopology.over S).yoneda.map (affineFormalBaseTransition A Y a I n m h))
    (𝟙 (schemeSpace Y).obj) (by simp) (by
      symm
      change (Scheme.fppfTopology.over S).yoneda.map
          (affineFormalBaseTransition A Y a I n m h) ≫
          (Scheme.fppfTopology.over S).yoneda.map (affineFormalBaseOverMap A Y a I m) =
        (Scheme.fppfTopology.over S).yoneda.map (affineFormalBaseOverMap A Y a I n) ≫ 𝟙 _
      rw [← Functor.map_comp, Category.comp_id]
      congr 1
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ a.inv) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ a.inv
      rw [← Category.assoc, ← Spec.map_comp]
      rfl))

/-- Tensor associativity identifies the iterated restriction with F_(n+1).
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalTensorTransition (I : Ideal A) (n m : ℕ) (h : n ≤ m) :
    affineFormalModule A Y a f I m ⋙
        moduleTensorPullback (affineFormalTransition A Y a f I n m h) ≅
      affineFormalModule A Y a f I n :=
  moduleTensorComposition (affineFormalTransition A Y a f I n m h)
      (affineFormalι A Y a f I m) ≪≫
    eqToIso (congrArg moduleTensorPullback (by
      apply ObjectProperty.hom_ext
      dsimp [affineFormalTransition, affineFormalι, enlargedFibreProductFst]
      simp only [Limits.pullback.map, Limits.pullback.lift_fst, Category.comp_id]))

/-- The coefficient arrow defining restriction from the m+1 fibre to the n+1 fibre.
Source: Stacks 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalCoefficient (I : Ideal A) (n m : ℕ) (h : n ≤ m) (F : X.Modules) :
    (affineFormalModule A Y a f I m).obj F ⟶
      (moduleDirectImage (affineFormalTransition A Y a f I n m h)).obj
        ((affineFormalModule A Y a f I n).obj F) :=
  (moduleTensorAdjunction (affineFormalTransition A Y a f I n m h)).unit.app _ ≫
    (moduleDirectImage (affineFormalTransition A Y a f I n m h)).map
      ((affineFormalTensorTransition A Y a f I n m h).hom.app F)

variable {Z : AlgebraicSpace S} (j : Z ⟶ X)

/-- Transport a specified coefficient arrow through the existing small-model equivalences.
Source: Stacks 03G8, 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalSmallCoefficient {M : X.Modules} {N : Z.Modules}
    (b : M ⟶ (moduleDirectImage j).obj N) :
    X.smallModuleRestriction.obj M ⟶
      (smallModuleDirectImage j).obj (Z.smallModuleRestriction.obj N) :=
  X.smallModuleRestriction.map
    (b ≫ (moduleDirectImage j).map (Z.smallModuleEquivalence.unitIso.hom.app N))

/-- Push a compatible global section through the canonical structure-module map.
This is a real section, fixed on every chart by regular-function pullback.
Source: Stacks 03G8 (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalPushSection (N : Z.SmallModules)
    (s : SheafOfModules.unit Z.smallStructureRings ⟶ N) :
    SheafOfModules.unit X.smallStructureRings ⟶ (smallModuleDirectImage j).obj N :=
  (smallModuleUnitIso X).hom ≫ X.smallModuleRestriction.map
    (moduleStructureMap j ≫ (moduleDirectImage j).map (fullModuleSection Z N s))

/-- Resolution-roof formula for the canonical cohomological coefficient restriction.
The intermediate resolution is of j_*N; no assertion that j_* preserves injectives is
made. A chain map from j_* of the N-resolution to that resolution supplies the roof.
Source: Stacks 08B1 and Cohomology on Sites, injective-resolution functoriality
(blueprint: lem-sfb-space-affine-formal-functions). -/
def AffineFormalRestrictionNormalized {M : X.Modules} {N : Z.Modules}
    (g : Z ⟶ schemeSpace Y) (b : M ⟶ (moduleDirectImage j).obj N) (q : ℕ)
    (r : (affineFormalH A Y a f q).obj M →ₗ[A]
      (affineFormalH A Y a g q).obj N) : Prop :=
  ∀ (P : InjectiveResolution (X.smallModuleRestriction.obj M))
    (Q : InjectiveResolution (Z.smallModuleRestriction.obj N))
    (K : InjectiveResolution
      ((smallModuleDirectImage j).obj (Z.smallModuleRestriction.obj N))),
    ∃ (t : ((smallModuleDirectImage j).mapHomologicalComplex (.up ℕ)).obj Q.cocomplex ⟶
        K.cocomplex)
      (v : P.cocomplex ⟶ K.cocomplex)
      (w : ((affineScalarSections A Y a Z g).mapHomologicalComplex (.up ℕ)).obj
          Q.cocomplex ⟶
        ((affineScalarSections A Y a X f).mapHomologicalComplex (.up ℕ)).obj K.cocomplex),
      (smallModuleDirectImage j).map (Q.ι.f 0) ≫ t.f 0 = K.ι.f 0 ∧
      P.ι.f 0 ≫ v.f 0 = affineFormalSmallCoefficient j b ≫ K.ι.f 0 ∧
      (∀ (k : ℕ) (s : (affineScalarSections A Y a Z g).obj (Q.cocomplex.X k)),
        w.f k s = affineFormalPushSection j (Q.cocomplex.X k) s ≫ t.f k) ∧
      IsIso (HomologicalComplex.homologyMap w q) ∧
      HomologicalComplex.homologyMap
          (((affineScalarSections A Y a X f).mapHomologicalComplex (.up ℕ)).map v) q =
        (P.isoRightDerivedObj (affineScalarSections A Y a X f) q).inv ≫
          ModuleCat.ofHom r ≫
          (Q.isoRightDerivedObj (affineScalarSections A Y a Z g) q).hom ≫
          HomologicalComplex.homologyMap w q

/-- The inverse limit is the actual submodule of compatible cohomology sequences.
Source: Stacks 08AZ (blueprint: lem-sfb-space-affine-formal-functions). -/
def affineFormalLimit (I : Ideal A) (q : ℕ) (F : X.Modules)
    (t : ∀ (n m : ℕ), n ≤ m →
      (affineFormalHn A Y a f I q m).obj F →ₗ[A]
        (affineFormalHn A Y a f I q n).obj F) :
    Submodule A (∀ n : ℕ, (affineFormalHn A Y a f I q n).obj F) where
  carrier := {x | ∀ (n m : ℕ) (h : n ≤ m), t n m h (x m) = x n}
  zero_mem' := fun _ _ _ ↦ map_zero _
  add_mem' hx hy n m h := by simp only [Pi.add_apply, map_add, hx n m h, hy n m h]
  smul_mem' c x hx n m h := by simp only [Pi.smul_apply, map_smul, hx n m h]

/-- All the clauses of formal functions, retaining the actual infinitesimal restrictions.
The ring-completion scalar law is written with a representative of each residue class;
this is precisely its coordinatewise action, independent of that representative.
Source: Stacks 08AZ and 08B1 (blueprint: lem-sfb-space-affine-formal-functions). -/
structure AffineFormalFunctions (I : Ideal A) (q : ℕ) (F : X.Modules) where
  restriction (n : ℕ) : (affineFormalH A Y a f q).obj F →ₗ[A]
    (affineFormalHn A Y a f I q n).obj F
  restriction_normalized (n : ℕ) :
    AffineFormalRestrictionNormalized A Y a f (affineFormalι A Y a f I n)
      (affineFormalι A Y a f I n ≫ f)
      ((moduleTensorAdjunction (affineFormalι A Y a f I n)).unit.app F) q (restriction n)
  transition (n m : ℕ) (h : n ≤ m) :
    (affineFormalHn A Y a f I q m).obj F →ₗ[A]
      (affineFormalHn A Y a f I q n).obj F
  transition_normalized (n m : ℕ) (h : n ≤ m) :
    AffineFormalRestrictionNormalized A Y a (affineFormalι A Y a f I m ≫ f)
      (affineFormalTransition A Y a f I n m h)
      (affineFormalι A Y a f I n ≫ f) (affineFormalCoefficient A Y a f I n m h F) q
      (transition n m h)
  transition_id (n : ℕ) : transition n n le_rfl = LinearMap.id
  transition_comp (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    (transition n m hnm).comp (transition m l hml) = transition n l (hnm.trans hml)
  kills (n : ℕ) :
    (I ^ (n + 1) • ⊤ : Submodule A ((affineFormalH A Y a f q).obj F)) ≤
      (restriction n).ker
  theta (n : ℕ) :
    ((affineFormalH A Y a f q).obj F ⧸
      (I ^ (n + 1) • ⊤ : Submodule A ((affineFormalH A Y a f q).obj F))) →ₗ[A]
        (affineFormalHn A Y a f I q n).obj F
  theta_projection (n : ℕ) :
    (theta n).comp (Submodule.mkQ (I ^ (n + 1) • ⊤)) = restriction n
  theta_transition (n m : ℕ) (h : n ≤ m) :
    (transition n m h).comp (theta m) = (theta n).comp
      (AdicCompletion.transitionMap I ((affineFormalH A Y a f q).obj F)
        (Nat.succ_le_succ h))
  [limitModule : Module (AdicCompletion I A)
    (affineFormalLimit A Y a f I q F transition)]
  coordinate_action (c : AdicCompletion I A)
      (x : affineFormalLimit A Y a f I q F transition) (n : ℕ) (b : A)
      (hb : Ideal.Quotient.mk (I ^ (n + 1)) b = AdicCompletion.evalₐ I (n + 1) c) :
    (c • x).val n = b • x.val n
  comparison : AdicCompletion I ((affineFormalH A Y a f q).obj F) ≃ₗ[AdicCompletion I A]
    affineFormalLimit A Y a f I q F transition
  comparison_projection (x : AdicCompletion I ((affineFormalH A Y a f q).obj F))
      (n : ℕ) :
    (comparison x).val n = theta n (AdicCompletion.eval I _ (n + 1) x)

/-- Formal functions over a Noetherian affine base, natural in the coherent module.
Source: Stacks, spaces-cohomology.tex, Tag 08AZ in situation-formal-functions;
Tag 08B1, final paragraph, identifies quotient cohomology with the displayed fibres
(blueprint: lem-sfb-space-affine-formal-functions).

Proof:
1. Properness over the Noetherian affine base makes every etale chart locally
Noetherian. Finite generation descends along finite affine etale refinements by
lem-weil-pbc-faithfully-flat-descent-finite-module. Thus the cover form of coherence
is the chartwise form below. Put J=I O_X, G_n=J^n F and Q_n=F/G_n. The coherent
abelian-category lemma makes G_n and Q_n coherent, using finite generators of I^n.
2. The enlarged ringed-site model and module/abelian evaluation comparison identify
module-resolution cohomology with additive cohomology, with the same scalar actions.
The universal right-derived delta functor supplies natural A-linear exact sequences.
3. On Spec(B) etale over X, tensor restriction to X_n is P/I^n P. These formulas glue
j_(n,*) F_n = Q_n and identify the quotient arrows and transitions. Affine higher-image
vanishing and affine cohomology give the canonical edge isomorphisms. On resolutions
these are exactly the roofs in AffineFormalRestrictionNormalized.
4. Multiplication by I^n on Q_n is zero, hence on its cohomology. The restriction maps
kill I^n H and factor uniquely through theta_n. Quotient functoriality gives transitions.
5. The exact sequence for G_n,F,Q_n identifies K_n=ker(H(F)→H(Q_n)) with the image
of H(G_n), and the boundary image B_n inside L_n=H^(q+1)(G_n). Naturality commutes
with all deeper quotient maps, including q=0.
6. Proper coherent higher images and the affine-base higher-image sections comparison
make L_n finite over A.
7. The ideal-power cohomology image bound in degree q gives c with K_(n+c)⊆I^n H.
8. In degree q+1 the same bound gives Im(L_(n+m)→L_n)⊆I^(m-b)L_n. Artin-Rees
on B_n⊆L_n, together with I^n B_n=0, makes B_n∩I^t L_n=0 for t≥d_n+n.
9. For r≥2n+b+d_n, the boundary of Im(H(Q_r)→H(Q_n)) vanishes; its image is
therefore exactly Im(H(F)→H(Q_n)). The reverse inclusion follows by composition.
10. Every compatible x_n is in that image. Lift x_(n+c) to u in H(F) and send it
to u mod I^n H. Step 7 gives lift independence and compatibility, hence a completed
class. Sums and scalar multiples of lifts prove A-linearity.
11. The two inverse identities follow coordinatewise: the lift maps back to x_n;
conversely a representative of a completed class at n+c reduces to its nth class.
12. Each theta_n is A/I^n-linear, so the comparison commutes coordinatewise with
completed scalars. Coefficient maps commute with quotient projections and the natural
edge isomorphisms, giving the final naturality formula. No flatness, completeness or
locality is used. Zero modules, unit ideals and empty spaces follow the same formulas.
-/
theorem exists_affineFormalFunctions [IsNoetherianRing A] (I : Ideal A)
    (hf : MapIsProper f) (q : ℕ) :
    ∃ d : ∀ (F : X.Modules), F.IsQuasicoherent →
        (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj F)) → AffineFormalFunctions A Y a f I q F,
      ∀ (F G : X.Modules) (hF : F.IsQuasicoherent)
        (hFc : ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj F)) (hG : G.IsQuasicoherent)
        (hGc : ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj G)) (g : F ⟶ G)
        (x : AdicCompletion I ((affineFormalH A Y a f q).obj F)) (n : ℕ),
        ((d G hG hGc).comparison
          (AdicCompletion.map I ((affineFormalH A Y a f q).map g).hom x)).val n =
        ((affineFormalHn A Y a f I q n).map g).hom
          (((d F hF hFc).comparison x).val n) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
