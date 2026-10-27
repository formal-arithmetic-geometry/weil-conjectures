module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Triangular coordinates and their specified rank-one reflections

Source: Milne, Algebraic Groups (2017), Theorem 23.31 and Remark 23.33, p.494,
and the explicit supporting triangular-coordinate assertion in
lem-sfb-triangular-reflection-orbits (blueprint: def-sfb-triangular-reflection-data).

This packages the hypotheses, with actual subgroup inclusions and morphisms on schemes.
Every condition on subgroup functors is tested on arbitrary commutative algebras.
Additive-group points are written by polynomial substitution, the centralizer is the
recorded scheme-theoretic centralizer of the image of λ, and the contraction functor
is spelled out by its affine-line orbit extension with value 1 at zero.
The paired word subgroup records a word and its induced character automorphism together.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.TriangularReflection

open TrivialTorusCoherent (Character)

variable {F : Type u} [Field F]

/-- Conjugating a subgroup's points by a rational point, after scalar extension.
Source: Milne, p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def conjugatePoints {H G : Grp (Over (Spec (.of F)))} (j : H ⟶ G)
    (g : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) (A : CommAlgCat.{u} F) :
    Set (StandardGroupSchemes.affine F A ⟶ G.X) :=
  {x | ∃ y : StandardGroupSchemes.affine F A ⟶ H.X,
    x = (toUnit _ ≫ g) * (y ≫ j.hom.hom) * (toUnit _ ≫ g)⁻¹}

/-- Closed generation, expressed by the smallest-closed-subgroup universal property.
Source: Milne, p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def generates {I : Type u} {U : Grp (Over (Spec (.of F)))}
    (H : I → Grp (Over (Spec (.of F)))) (j : ∀ a : I, H a ⟶ U) : Prop :=
  ∀ (L : Grp (Over (Spec (.of F)))) (l : L ⟶ U),
    IsClosedSubgroupScheme l.hom.hom →
      (∀ a : I, ∃ f : H a ⟶ L, f ≫ l = j a) → IsIso l

/-- Extension of torus conjugation to the multiplicative monoid A¹. Its action laws
are identities on all affine test schemes; the restricted morphism is conjugation.
Source: Milne, p.494 and Section 13 (blueprint: def-sfb-triangular-reflection-data). -/
def monoidExtension {T U G : Grp (Over (Spec (.of F)))}
    (iT : T ⟶ G) (iU : U ⟶ G) (eta : RankOneRoots.Cocharacter T)
    (a : StandardGroupSchemes.additive F ⊗ U.X ⟶ U.X) : Prop :=
  ((StandardGroupSchemes.map F (Polynomial.toLaurentAlg (R := F))) ⊗ₘ 𝟙 U.X) ≫
      a ≫ iU.hom.hom =
    (fst _ _ ≫ eta.hom.hom ≫ iT.hom.hom) * (snd _ _ ≫ iU.hom.hom) *
      (fst _ _ ≫ eta.hom.hom ≫ iT.hom.hom)⁻¹ ∧
  (∀ (A : CommAlgCat.{u} F) (x : StandardGroupSchemes.affine F A ⟶ U.X),
    lift (StandardGroupSchemes.map F (Polynomial.aeval (1 : A))) x ≫ a = x) ∧
  ∀ (A : CommAlgCat.{u} F) (t s : A) (x : StandardGroupSchemes.affine F A ⟶ U.X),
    lift (StandardGroupSchemes.map F (Polynomial.aeval t))
        (lift (StandardGroupSchemes.map F (Polynomial.aeval s)) x ≫ a) ≫ a =
      lift (StandardGroupSchemes.map F (Polynomial.aeval (t * s))) x ≫ a

/-- Triangular coordinates, simple additive groups and compatible rank-one data.
The character group and cocharacters are the recorded actual group-scheme Hom sets.
The composition condition fixes the integer pairing; no abstract substitute lattice
or abstract normalizer action is used.
Source: Milne, Theorem 23.31 and Remark 23.33, p.494; the supporting assertion's
hypotheses in lem-sfb-triangular-reflection-orbits
(blueprint: def-sfb-triangular-reflection-data). -/
structure Data (F : Type u) [Field F] where
  /-- Ambient affine group and its torus and two triangular factors. -/
  G : Grp (Over (Spec (.of F)))
  T : Grp (Over (Spec (.of F)))
  U : Grp (Over (Spec (.of F)))
  V : Grp (Over (Spec (.of F)))
  /-- The three specified subgroup inclusions. -/
  iT : T ⟶ G
  iU : U ⟶ G
  iV : V ⟶ G
  /-- Ambient affine finite type, smoothness and connectedness. -/
  algebraic : SolvableGroupStructure.IsAlgebraic G
  smooth : Smooth G.X.hom
  connected : ConnectedSpace G.X.left
  /-- The torus is split and maximal. -/
  maximal : ReductiveTorusCentralizer.IsMaximalTorus iT
  split : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)
  /-- The two factors are closed smooth connected unipotent subgroups. -/
  closedU : IsClosedSubgroupScheme iU.hom.hom
  closedV : IsClosedSubgroupScheme iV.hom.hom
  smoothU : Smooth U.X.hom
  smoothV : Smooth V.X.hom
  connectedU : ConnectedSpace U.X.left
  connectedV : ConnectedSpace V.X.left
  unipotentU : SolvableGroupStructure.IsUnipotent U
  unipotentV : SolvableGroupStructure.IsUnipotent V
  /-- The actual restricted conjugation action, used by the recorded stability predicate. -/
  adjointAction : ModObj T.X G.X
  adjointFormula : adjointAction.smul = RankOneRoots.adjointMap iT
  normalizedU : @TorusCharacterTangent.IsStable F _ T G adjointAction U iU
  normalizedV : @TorusCharacterTangent.IsStable F _ T G adjointAction V iV
  /-- Multiplication V × T × U is an open immersion. -/
  bigCell : IsOpenImmersion
    (((fst (V.X ⊗ T.X) U.X ≫ fst V.X T.X ≫ iV.hom.hom) *
      (fst (V.X ⊗ T.X) U.X ≫ snd V.X T.X ≫ iT.hom.hom) *
      (snd (V.X ⊗ T.X) U.X ≫ iU.hom.hom)).left)
  /-- Composition pairing, fixed by the integer power map. -/
  pairing : Character T → RankOneRoots.Cocharacter T → ℤ
  composition (chi : Character T) (eta : RankOneRoots.Cocharacter T) :
    eta.hom.hom ≫ chi.toMul.hom.hom =
      (𝟙 (StandardGroupSchemes.multiplicative F)) ^ pairing chi eta
  /-- The finite nonempty independent set of nonzero simple characters. -/
  D : Finset (Character T)
  nonempty : D.Nonempty
  nonzero (alpha : D) : alpha.val ≠ 0
  independent : LinearIndependent ℤ (fun alpha : D ↦ alpha.val)
  /-- One positive cocharacter of common positive height. -/
  lam : RankOneRoots.Cocharacter T
  n : ℤ
  positive : 0 < n
  height (alpha : D) : pairing alpha.val lam = n
  /-- The centralizer and two contraction functors are the specified factors. A point g
  lies in U_G(μ) when μ(t) g μ(t)⁻¹ extends along G_m ⊆ A¹ with value 1 at zero. -/
  centralizer (A : CommAlgCat.{u} F) :
    ReductiveTorusCentralizer.centralizerPoints (lam ≫ iT) A =
      (RankOneRoots.pointImage iT (StandardGroupSchemes.affine F A) : Set _)
  contraction (A : CommAlgCat.{u} F) (g : StandardGroupSchemes.affine F A ⟶ G.X) :
    (∃ q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ G.X,
      (𝟙 (StandardGroupSchemes.affine F A) ⊗ₘ
          StandardGroupSchemes.map F (Polynomial.toLaurentAlg (R := F))) ≫ q =
        (snd _ _ ≫ (lam ≫ iT).hom.hom) * (fst _ _ ≫ g) *
          (snd _ _ ≫ (lam ≫ iT).hom.hom)⁻¹ ∧
      lift (𝟙 _) 1 ≫ q = 1) ↔
      g ∈ RankOneRoots.pointImage iU (StandardGroupSchemes.affine F A)
  oppositeContraction (A : CommAlgCat.{u} F) (g : StandardGroupSchemes.affine F A ⟶ G.X) :
    (∃ q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ G.X,
      (𝟙 (StandardGroupSchemes.affine F A) ⊗ₘ
          StandardGroupSchemes.map F (Polynomial.toLaurentAlg (R := F))) ≫ q =
        (snd _ _ ≫ (Grp.ofHom (ι[StandardGroupSchemes.multiplicative F]) ≫ lam ≫ iT).hom.hom) *
            (fst _ _ ≫ g) *
          (snd _ _ ≫
            (Grp.ofHom (ι[StandardGroupSchemes.multiplicative F]) ≫ lam ≫ iT).hom.hom)⁻¹ ∧
      lift (𝟙 _) 1 ≫ q = 1) ↔
      g ∈ RankOneRoots.pointImage iV (StandardGroupSchemes.affine F A)
  /-- Simple subgroups, their inclusions, and additive parametrizations. -/
  Ua : D → Grp (Over (Spec (.of F)))
  Va : D → Grp (Over (Spec (.of F)))
  u : ∀ alpha : D, Ua alpha ⟶ U
  v : ∀ alpha : D, Va alpha ⟶ V
  closedUa (alpha : D) : IsClosedSubgroupScheme (u alpha).hom.hom
  closedVa (alpha : D) : IsClosedSubgroupScheme (v alpha).hom.hom
  parameterU : ∀ alpha : D, Grp.mk (StandardGroupSchemes.additive F) ≅ Ua alpha
  parameterV : ∀ alpha : D, Grp.mk (StandardGroupSchemes.additive F) ≅ Va alpha
  normalizedUa (alpha : D) :
    @TorusCharacterTangent.IsStable F _ T G adjointAction (Ua alpha) (u alpha ≫ iU)
  normalizedVa (alpha : D) :
    @TorusCharacterTangent.IsStable F _ T G adjointAction (Va alpha) (v alpha ≫ iV)
  /-- T conjugates the two additive parameters by alpha and -alpha. -/
  scalingU (alpha : D) (A : CommAlgCat.{u} F)
      (t : StandardGroupSchemes.affine F A ⟶ T.X) (z : A) :
    (t ≫ iT.hom.hom) *
        (StandardGroupSchemes.map F (Polynomial.aeval z) ≫
          (parameterU alpha).hom.hom.hom ≫ (u alpha).hom.hom ≫ iU.hom.hom) *
        (t ≫ iT.hom.hom)⁻¹ =
      StandardGroupSchemes.map F (Polynomial.aeval
          (RankOneRoots.multiplicativeValue A (t ≫ alpha.val.toMul.hom.hom) * z)) ≫
        (parameterU alpha).hom.hom.hom ≫ (u alpha).hom.hom ≫ iU.hom.hom
  scalingV (alpha : D) (A : CommAlgCat.{u} F)
      (t : StandardGroupSchemes.affine F A ⟶ T.X) (z : A) :
    (t ≫ iT.hom.hom) *
        (StandardGroupSchemes.map F (Polynomial.aeval z) ≫
          (parameterV alpha).hom.hom.hom ≫ (v alpha).hom.hom ≫ iV.hom.hom) *
        (t ≫ iT.hom.hom)⁻¹ =
      StandardGroupSchemes.map F (Polynomial.aeval
          (RankOneRoots.multiplicativeValue A (t ≫ (-alpha.val).toMul.hom.hom) * z)) ≫
        (parameterV alpha).hom.hom.hom ≫ (v alpha).hom.hom ≫ iV.hom.hom
  generateU : generates Ua u
  generateV : generates Va v
  /-- Normalizer representatives with their actual conjugation automorphisms of T. -/
  representative : D → (𝟙_ (Over (Spec (.of F))) ⟶ G.X)
  normalizes (alpha : D) : representative alpha ∈ RankOneRoots.normalizer iT
  torusAction : D → (T ≅ T)
  conjugationT (alpha : D) :
    (torusAction alpha).hom.hom.hom ≫ iT.hom.hom =
      (toUnit T.X ≫ representative alpha) * iT.hom.hom *
        (toUnit T.X ≫ representative alpha)⁻¹
  /-- Specified simple reflections and coroots. -/
  reflection : D → (Character T ≃ₗ[ℤ] Character T)
  coroot : D → RankOneRoots.Cocharacter T
  reflectionFormula (alpha : D) (chi : Character T) :
    reflection alpha chi = chi - pairing chi (coroot alpha) • alpha.val
  reflectionAction (alpha : D) (chi : Character T) :
    (reflection alpha chi).toMul = (torusAction alpha).inv ≫ chi.toMul
  corootTwo (alpha : D) : pairing alpha.val (coroot alpha) = 2
  conjugationSimple (alpha : D) (A : CommAlgCat.{u} F) :
    conjugatePoints (u alpha ≫ iU) (representative alpha) A =
      (RankOneRoots.pointImage (v alpha ≫ iV) (StandardGroupSchemes.affine F A) : Set _)
  /-- Every cocharacter nonnegative on D has an A¹-monoid extension on U. -/
  monoidExtensions (eta : RankOneRoots.Cocharacter T) :
    (∀ alpha : D, 0 ≤ pairing alpha.val eta) →
      ∃ a : StandardGroupSchemes.additive F ⊗ U.X ⟶ U.X, monoidExtension iT iU eta a
  /-- Cocharacters killing exactly one simple direction, with common other height. -/
  eta : D → RankOneRoots.Cocharacter T
  m : D → ℤ
  positiveM (alpha : D) : 0 < m alpha
  zeroHeight (alpha : D) : pairing alpha.val (eta alpha) = 0
  otherHeight (alpha beta : D) : beta ≠ alpha → pairing beta.val (eta alpha) = m alpha
  /-- Chosen monoid extensions and their evaluation-at-zero homomorphisms. -/
  action : D → (StandardGroupSchemes.additive F ⊗ U.X ⟶ U.X)
  extendsEta (alpha : D) : monoidExtension iT iU (eta alpha) (action alpha)
  projection : ∀ alpha : D, U ⟶ Ua alpha
  evaluationZero (alpha : D) :
    lift (1 : U.X ⟶ StandardGroupSchemes.additive F) (𝟙 U.X) ≫ action alpha =
      (projection alpha).hom.hom ≫ (u alpha).hom.hom
  retract (alpha : D) : u alpha ≫ projection alpha = 𝟙 (Ua alpha)
  /-- The smooth connected kernel and semidirect product. -/
  K : D → Grp (Over (Spec (.of F)))
  kernelInclusion : ∀ alpha : D, K alpha ⟶ U
  closedK (alpha : D) : IsClosedSubgroupScheme (kernelInclusion alpha).hom.hom
  smoothK (alpha : D) : Smooth (K alpha).X.hom
  connectedK (alpha : D) : ConnectedSpace (K alpha).X.left
  kernel (alpha : D) : IsPullback (kernelInclusion alpha).hom.hom (toUnit (K alpha).X)
    (projection alpha).hom.hom η[(Ua alpha).X]
  semidirect (alpha : D) : IsIso
    ((fst (Ua alpha).X (K alpha).X ≫ (u alpha).hom.hom) *
      (snd (Ua alpha).X (K alpha).X ≫ (kernelInclusion alpha).hom.hom))
  fixedSubgroup (alpha : D) (A : CommAlgCat.{u} F)
      (x : StandardGroupSchemes.affine F A ⟶ U.X) :
    x ≫ iU.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (eta alpha ≫ iT) A ↔
      x ∈ RankOneRoots.pointImage (u alpha) (StandardGroupSchemes.affine F A)
  kernelNormalized (alpha : D) (A : CommAlgCat.{u} F) :
    conjugatePoints (kernelInclusion alpha ≫ iU) (representative alpha) A =
      (RankOneRoots.pointImage (kernelInclusion alpha ≫ iU)
        (StandardGroupSchemes.affine F A) : Set _)

/-- The reflection subgroup of the actual character lattice.
Source: Milne, Remark 23.33, p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def Data.weyl (d : Data F) : Subgroup (Character d.T ≃ₗ[ℤ] Character d.T) :=
  Subgroup.closure (Set.range d.reflection)

/-- Paired words retain both the representative in G(F) and the automorphism on X.
Taking a generated subgroup permits exactly words in the generators and their inverses.
Source: Milne, p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def Data.words (d : Data F) :
    Subgroup ((𝟙_ (Over (Spec (.of F))) ⟶ d.G.X) ×
      (Character d.T ≃ₗ[ℤ] Character d.T)) :=
  Subgroup.closure (Set.range (fun alpha : d.D ↦
    (d.representative alpha, d.reflection alpha)))

/-- The orbit of the specified simple characters; no adjoint-weight assertion is made.
Source: Milne, Remark 23.33, p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def Data.roots (d : Data F) : Set (Character d.T) :=
  {rho | ∃ (w : d.weyl) (alpha : d.D), w.val alpha.val = rho}

/-- The rational span in Q tensor X, retaining all central directions in the ambient X.
Source: Milne, Appendix C and p.494 (blueprint: def-sfb-triangular-reflection-data). -/
def Data.rootSpace (d : Data F) : Submodule ℚ (ℚ ⊗[ℤ] Character d.T) :=
  Submodule.span ℚ ((fun chi : Character d.T ↦ (1 : ℚ) ⊗ₜ[ℤ] chi) '' d.roots)

end AlgebraicGeometry.TriangularReflection
