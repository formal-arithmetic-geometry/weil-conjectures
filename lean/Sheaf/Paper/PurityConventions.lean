/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.TateTwistFiniteLocallyFree
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.PurityNormalBundle
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.EtaleCohomology.TateTwist.KummerClassTorsor

/-!
# Purity conventions and the concrete rank-one datum

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-def-purity-conv/_section.md` (blueprint: sk-def-purity-conv).

The coefficient, site, twist, affine-line, normal-cone, exceptional-image,
section-invariant and deformation constructions are the imported published ones.
Here the Kummer boundary is extended to every positive annihilating exponent,
with the coefficient comparison fixed on all pure tensors. A natural-number
index r denotes the positive exponent N = r + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityConventions

/-- The scalar module of the coefficient quotient over the lifted residue ring.
Source: blueprint sk-def-purity-conv, coefficient extension in the Kummer paragraph
(blueprint: sk-def-purity-conv). -/
def coefficientModule (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) :=
  letI := Module.compHom A
    ((Scheme.finiteEtaleTwistScalar m A hA).comp ULift.ringEquiv.toRingHom)
  ModuleCat.of (ULift.{u + 1} (ZMod m)) A

/-- A constant coefficient section in the published pro-etale ring sheaf.
Source: blueprint sk-def-purity-conv, pure tensors
(blueprint: sk-def-purity-conv). -/
def coefficientSection (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (W : T.ProEtᵒᵖ) (a : A) : (Scheme.tateFiniteCoefficient T A).obj.obj W :=
  ((toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app W).hom a

/-- The actual finite-twist underlying abelian sheaf, using the existing scalar extension.
Source: blueprint sk-def-purity-conv, A_T(1) = mu tensor A
(blueprint: sk-def-purity-conv). -/
def finiteLine (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) :
    Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf _).obj
    (Scheme.tateFiniteLine T l A r (Scheme.finiteEtaleTwistScalar _ A hA))

/-- Restriction of roots on etale objects is uniquely determined by their units.
Source: blueprint sk-def-purity-conv, root-sheaf comparison
(blueprint: sk-def-purity-conv).
Proof: restriction preserves kernels, and the restricted pro-etale units are the
same units on every etale object. The etale kernel inclusion therefore factors
uniquely through the restricted pro-etale root kernel. This factorization is
restriction of roots and commutes with power transitions. -/
theorem rootRestriction_existsUnique (T : Scheme.{u}) (m : ℕ) :
    ∃! f : T.rootsOfUnitySheaf m ⟶
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
          (Scheme.proEtaleRootsOfUnitySheaf T m),
      f ≫ (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map
          (Scheme.proEtaleRootsOfUnityInclusion T m) =
        kernel.ι (m • 𝟙 T.gmSheaf) ≫ ⟨𝟙 _⟩ := by
  let F := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  have hp : F.map (Scheme.proEtaleUnitsPower T m) =
      m • 𝟙 (F.obj (Scheme.proEtaleUnitsSheaf T)) := by
    change F.map (m • 𝟙 _) = _
    rw [F.map_nsmul]
    exact congrArg (fun f ↦ m • f) (F.map_id _)
  let e : T.gmSheaf ⟶ F.obj (Scheme.proEtaleUnitsSheaf T) := ⟨𝟙 _⟩
  have hz : m • kernel.ι (m • 𝟙 T.gmSheaf) = 0 := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using
      kernel.condition (m • 𝟙 T.gmSheaf)
  have hw : (kernel.ι (m • 𝟙 T.gmSheaf) ≫ e) ≫
      F.map (Scheme.proEtaleUnitsPower T m) = 0 := by
    rw [hp, Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, hz, zero_comp]
  let hk := isLimitOfHasKernelOfPreservesLimit F (Scheme.proEtaleUnitsPower T m)
  obtain ⟨f, hf⟩ := KernelFork.IsLimit.lift' hk
    (kernel.ι (m • 𝟙 T.gmSheaf) ≫ e) hw
  refine ⟨f, hf, fun g hg ↦ ?_⟩
  apply Fork.IsLimit.hom_ext hk
  exact hg.trans hf.symm

/-- The restriction map on roots, retained before taking its comparison-adjunction mate.
Source: blueprint sk-def-purity-conv, restriction of roots
(blueprint: sk-def-purity-conv). -/
def rootRestriction (T : Scheme.{u}) (m : ℕ) :
    T.rootsOfUnitySheaf m ⟶
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
        (Scheme.proEtaleRootsOfUnitySheaf T m) :=
  Classical.choose (rootRestriction_existsUnique T m)

/-- The normalization of coefficient comparison on every local pure tensor.
The roots comparison is the published restriction map, fixed by its inclusion in units.
Its adjoint sends an etale root to its restriction on the same pro-etale object.
Source: blueprint sk-def-purity-conv, specified coefficient identification
(blueprint: sk-def-purity-conv). -/
def IsCoefficientComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (e : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA) : Prop :=
  ∀ (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj W),
    (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _) e.hom).hom.app W
      (Scheme.kummerCoefficientInsertionApp T (l ^ (r + 1))
        (coefficientModule A (l ^ (r + 1)) hA) a W z) =
      Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hA)
        ((Scheme.toProEt T).obj W.unop)
        (coefficientSection T A ((Scheme.toProEt T).op.obj W) a)
        ((rootRestriction T (l ^ (r + 1))).hom.app W z)

/-- There is exactly one coefficient comparison with the specified local tensor formula.
Source: blueprint sk-def-purity-conv, comparison paragraph
(blueprint: sk-def-purity-conv).
Proof: roots restriction is the published kernel-normalized comparison. On the etale
cover of lem-pur-twist-sheaf-locally-free it sends each residue to itself, hence is an
isomorphism. The finite constant ring identification of lem-sf-comparison-pullback-exact
and preservation of finite limits and colimits transport the universal bilinear map.
This gives the displayed tensor formula and a local inverse. The inverses glue. Every
section of a sheafified tensor is locally a sum of pure tensors, so that formula forces
uniqueness. Neither freeness of A over Z/l^N nor e dividing n is needed. -/
theorem coefficientComparison_existsUnique (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    ∃! e : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA,
      IsCoefficientComparison T l A r hA e := by
  sorry

/-- The unique comparison, with its root and pure-tensor normalization retained.
Source: blueprint sk-def-purity-conv, coefficient identification
(blueprint: sk-def-purity-conv). -/
def coefficientComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
          (coefficientModule A (l ^ (r + 1)) hA)) ≅ finiteLine T l A r hA :=
  Classical.choose (coefficientComparison_existsUnique T l A r hA hT)

/-- The actual Kummer boundary, coefficient insertion and canonical site comparison.
This formula gives kappa(v) for every unit, and hence kappa(t) for the coordinate.
Source: blueprint sk-def-purity-conv, displayed definition of kappa(t)
(blueprint: sk-def-purity-conv). -/
def kummer (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0) (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (v : Γ(T, ⊤)ˣ) : Sheaf.H (finiteLine T l A r hA) 1 :=
  Sheaf.H.map (coefficientComparison T l A r hA hT).hom 1
    (ProEtale.comparisonCohomologyMap T _ 1
      (Sheaf.H.map
        (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
          (coefficientModule A (l ^ (r + 1)) hA) (1 : A)) 1
        (T.kummerδ₀ (l ^ (r + 1)) hT (Additive.ofMul v))))

/-- The canonical pullback identification of constant abelian sheaves.
Source: blueprint sk-def-purity-conv, pullback convention
(blueprint: sk-def-purity-conv). -/
def constantPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
      ProEtale.upperStar AddCommGrpCat.{u + 1} f ≅
        constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft
    (constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.proEtaleBaseChange f)
      AddCommGrpCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm ≪≫
    (Scheme.proEtaleBaseChange f).constantSheafsheafPullbackIso AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (terminalIsTerminal : IsTerminal (⊤_ Y.ProEt))
      (terminalIsTerminal.isTerminalObj (Scheme.proEtaleBaseChange f))

/-- The finite line pullback is characterized by restriction of roots and constants.
Source: blueprint sk-def-purity-conv, naturality paragraph
(blueprint: sk-def-purity-conv).
Proof: pullback of roots is the canonical root-restriction isomorphism; pullback of
constant A is the constant-sheaf isomorphism. The universal property of the sheafified
tensor gives this map. After an etale root trivialization it is the identity on A,
so it is an isomorphism. Local sums of pure tensors prove uniqueness. -/
theorem finiteLinePullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) :
    ∃! e : (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
        (finiteLine Y l A r hA) ≅ finiteLine X l A r hA,
      ∀ (V : Y.ProEt) (a : A)
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (r + 1))).obj.obj (op V)),
        (((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
          e.hom).hom.app (op V)
            (Scheme.tateFiniteTensor Y l A r (Scheme.finiteEtaleTwistScalar _ A hA)
              V (coefficientSection Y A (op V) a) z) =
          Scheme.tateFiniteTensor X l A r (Scheme.finiteEtaleTwistScalar _ A hA)
            ((Scheme.proEtaleBaseChange f).obj V)
            (coefficientSection X A (op ((Scheme.proEtaleBaseChange f).obj V)) a)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (r + 1))).hom.app
              (op V) z) := by
  sorry

/-- The unique root-normalized pullback isomorphism.
Source: blueprint sk-def-purity-conv, pullback convention
(blueprint: sk-def-purity-conv). -/
def finiteLinePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
      (finiteLine Y l A r hA) ≅ finiteLine X l A r hA :=
  Classical.choose (finiteLinePullback_existsUnique f l A r hA hY)

/-- Cohomology pullback uses exact inverse image and the constant-integer identification.
Source: blueprint sk-def-purity-conv, base-change compatibility
(blueprint: sk-def-purity-conv). -/
def finiteLineCohomologyPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) (q : ℕ) :
    Sheaf.H (finiteLine Y l A r hA) q →+ Sheaf.H (finiteLine X l A r hA) q :=
  (Sheaf.H.map (finiteLinePullback f l A r hA hY).hom q).comp
    (Sheaf.H.mapFunctor (ProEtale.upperStar AddCommGrpCat.{u + 1} f)
      ((constantPullbackIso f).symm.app (AddCommGrpCat.of (ULift ℤ)))
      (finiteLine Y l A r hA) q)

/-- The constructed class commutes with arbitrary scheme pullback.
Source: blueprint sk-def-purity-conv, naturality paragraph
(blueprint: sk-def-purity-conv).
Proof: pullback of the Kummer exact sequence is the Kummer sequence; its connecting
map is natural. Coefficient insertion commutes with restriction on every root.
Comparison inverse images commute with base change by the site functor square.
Both resulting coefficient identifications have the pure-tensor normalization,
so uniqueness identifies them. Compose these three commuting squares. -/
theorem kummer_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (hX : IsUnit ((l ^ (r + 1) : ℕ) : Γ(X, ⊤))) (v : Γ(Y, ⊤)ˣ) :
    finiteLineCohomologyPullback f l A r hA hY 1 (kummer Y l A r hA hY v) =
      kummer X l A r hA hX (Units.map f.appTop.hom v) := by
  sorry

private theorem finiteLine_hom_ext (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    {F : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (f g : finiteLine T l A n hA ⟶ F)
    (h : ∀ (V : T.ProEt) (b : (Scheme.tateFiniteCoefficient T A).obj.obj (op V))
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op V)),
      f.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hA) V b z) =
        g.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hA) V b z)) :
    f = g := by
  let α := Scheme.tateFiniteScalar T l A n (Scheme.finiteEtaleTwistScalar _ A hA)
  let M := Scheme.purTwistRootsModule T l n
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M
  apply ((sheafificationAdjunction (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}).homEquiv P.presheaf F).injective
  ext U x
  change f.hom.app U ((toSheafify (Scheme.ProEt.topology T) P.presheaf).app U x) =
    g.hom.app U ((toSheafify (Scheme.ProEt.topology T) P.presheaf).app U x)
  let := (α.hom.app U).hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b z => exact h U.unop b z

/-- The canonical exponent comparison is the existing finite Kummer identification,
expressed with the unique quotient scalar maps and fixed on every pure tensor.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv).
Proof: the two unital quotient maps to A agree by the universal property of ZMod.
Transport spFiniteKummer along that equality. Its specified power formula gives
the displayed formula, including r=n. Pure tensors locally generate the scalar
extension, so this formula determines the isomorphism uniquely. -/
theorem finiteLineTransition_existsUnique (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    ∃! e : finiteLine T l A n hn ≅ finiteLine T l A r hr,
      ∀ (V : T.ProEt) (b : (Scheme.tateFiniteCoefficient T A).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op V)),
        e.hom.hom.app (op V)
          (Scheme.tateFiniteTensor T l A n (Scheme.finiteEtaleTwistScalar _ A hn) V b z) =
          Scheme.tateFiniteTensor T l A r (Scheme.finiteEtaleTwistScalar _ A hr) V b
            ((Scheme.proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.succ_le_succ hrn))).hom.app (op V) z) := by
  have hl : IsUnit (l : Γ(T, ⊤)) :=
    (isUnit_pow_iff (Nat.succ_ne_zero r)).mp (by
      simpa only [Nat.cast_pow] using hT)
  let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      simpa only [map_natCast] using hl.map (T.Γevaluation x).hom).invertible
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hf⟩ := Scheme.tateTwist_finite_locallyFree T l
  obtain ⟨a, ha, _⟩ := hf A r (fun b ↦ by
    rw [nsmul_eq_mul, hr, zero_mul])
  have har : a = Scheme.finiteEtaleTwistScalar _ A hr := Subsingleton.elim _ _
  subst a
  have han : (Scheme.finiteEtaleTwistScalar _ A hr).comp
      (ZMod.castHom (pow_dvd_pow l (Nat.succ_le_succ hrn))
        (ZMod (l ^ (r + 1)))) = Scheme.finiteEtaleTwistScalar _ A hn :=
    Subsingleton.elim _ _
  have hmap := ha n hrn
  rw [han] at hmap
  obtain ⟨k, hk, hformula⟩ := hmap
  let := hk
  let e := (SheafOfModules.toSheaf _).mapIso (asIso k)
  refine ⟨e, hformula, ?_⟩
  intro d hd
  apply Iso.ext
  apply finiteLine_hom_ext T l A n hn
  intro V b z
  exact (hd V b z).trans (hformula V b z).symm

/-- The unique canonical power-transition identification at admissible exponents.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv). -/
def finiteLineTransition (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) :
    finiteLine T l A n hn ≅ finiteLine T l A r hr :=
  Classical.choose (finiteLineTransition_existsUnique T l A r n hrn hr hn hT)

/-- Power transitions identify the Kummer classes at any two admissible levels.
Source: blueprint sk-def-purity-conv, independence of N
(blueprint: sk-def-purity-conv).
Proof: for r<=n map the exponent-l^(n+1) Kummer sequence to the smaller one by
the l^(n-r) power on the middle units, identity on the right units, and the power
transition on roots. Naturality of boundaries identifies the two root classes.
The coefficient and site comparisons commute with these root powers by their
pure-tensor normalizations. This proves the equality. For any two indices choose
the larger; their comparison is this isomorphism or its inverse. -/
theorem kummer_exponent_independent (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (hr : ((l ^ (r + 1) : ℕ) : A) = 0) (hn : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hTr : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hTn : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    Sheaf.H.map (finiteLineTransition T l A r n hrn hr hn hTr).hom 1
      (kummer T l A n hn hTn v) = kummer T l A r hr hTr v := by
  sorry

/-- The concrete root torsor is the torsor of lifts of the unit in the Kummer sequence.
Its underlying sections are exactly local units whose l^(r+1)-th power is v.
Source: blueprint sk-def-purity-conv, torsor interpretation
(blueprint: sk-def-purity-conv). -/
def rootTorsor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    Sheaf.Torsor (T.rootsOfUnitySheaf (l ^ (r + 1))) :=
  Sheaf.Torsor.lifts (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
    (T.kummerSequence_shortExact (l ^ (r + 1)) hT) (ULift.up (Additive.ofMul v))

/-- The actual relative root cover, constructed by the existing monic quotient algebra.
Source: blueprint sk-def-purity-conv, relative spectrum T_t
(blueprint: sk-def-purity-conv). -/
abbrev rootCover (T : Scheme.{u}) (l r : ℕ) (v : Γ(T, ⊤)ˣ) : Scheme.{u} :=
  T.kummerCover (l ^ (r + 1)) (v : Γ(T, ⊤))

private theorem homSpecEquiv_precomp {V W : Scheme.{u}} (f : V ⟶ W)
    (R : CommRingCat.{u}) (g : W ⟶ Spec R) :
    Scheme.homSpecEquiv V R (f ≫ g) = Scheme.homSpecEquiv W R g ≫ f.appTop := by
  change ((ΓSpec.adjunction.homEquiv V (op R)).symm (f ≫ g)).unop = _
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

private theorem kummerCoverHomEquiv_precomp {T V W : Scheme.{u}} (n : ℕ)
    (v : Γ(T, ⊤)) (h : W ⟶ T) (f : V ⟶ W)
    (hV : V ⟶ T) (hw : f ≫ h = hV)
    (a : {a : W ⟶ T.kummerCover n v // a ≫ T.kummerCoverπ n v = h}) :
    ((Scheme.kummerCoverHomEquiv n v hV)
      ⟨f ≫ a.val, by rw [Category.assoc, a.property, hw]⟩).val =
      f.appTop ((Scheme.kummerCoverHomEquiv n v h a).val) := by
  change (Scheme.homSpecEquiv V _ ((f ≫ a.val) ≫ pullback.snd _ _))
      (AdjoinRoot.root _) = _
  rw [Category.assoc, homSpecEquiv_precomp]
  rfl

private def rootTorsorUnitsEquiv (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) (W : T.Etale) :
    (rootTorsor T l r hT v).sheaf.obj.obj (op W) ≃
      {w : Γ(W.left, ⊤)ˣ // w ^ (l ^ (r + 1)) = Units.map W.hom.appTop.hom.toMonoidHom v} :=
  Equiv.subtypeEquiv (Scheme.gmSheafSectionsEquiv W) fun x ↦ by
    change (l ^ (r + 1)) • x =
        T.gmSheaf.obj.map
          ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from W).op
          (ULift.up (Additive.ofMul v)) ↔ _
    have hw :
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from W =
          MorphismProperty.Over.homMk W.hom := by
      apply Subsingleton.elim
    rw [hw]
    change (l ^ (r + 1)) • x =
      ULift.up (Additive.ofMul (Units.map W.hom.appTop.hom.toMonoidHom v)) ↔ _
    exact (Scheme.gmSheafSectionsEquiv W).injective.eq_iff.symm

/-- The root torsor is represented by the specified root cover, naturally on etale objects.
Source: blueprint sk-def-purity-conv, torsor equation
(blueprint: sk-def-purity-conv).
Proof: on an affine open the universal property of R[T0]/(T0^l^(r+1)-v) identifies
maps into its spectrum with roots of v. A root is a unit because its positive power
is the unit v. These local identifications commute with ring restriction and hence
glue to the displayed natural bijections for every etale object. The lifting torsor
uses precisely the same root equation. The action is multiplication by a root of
unity, which is addition of its image in the additive units sheaf. -/
theorem rootTorsor_represented (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    ∃ e : ∀ W : T.Etale, (rootTorsor T l r hT v).sheaf.obj.obj (op W) ≃
        {a : W.left ⟶ rootCover T l r v //
          a ≫ T.kummerCoverπ (l ^ (r + 1)) (v : Γ(T, ⊤)) = W.hom},
      ∀ (V W : T.Etale) (f : V ⟶ W)
        (x : (rootTorsor T l r hT v).sheaf.obj.obj (op W)),
        (e V ((rootTorsor T l r hT v).sheaf.obj.map f.op x)).val =
          f.left ≫ (e W x).val := by
  let : NeZero (l ^ (r + 1)) := ⟨ne_of_gt (pow_pos (Fact.out : l.Prime).pos _)⟩
  let e (W : T.Etale) :=
    (rootTorsorUnitsEquiv T l r hT v W).trans
      ((Scheme.unitsPowEqEquiv (l ^ (r + 1)) (Units.map W.hom.appTop.hom.toMonoidHom v)).trans
        (Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom).symm)
  refine ⟨e, ?_⟩
  intro V W f x
  suffices heq : e V ((rootTorsor T l r hT v).sheaf.obj.map f.op x) =
      ⟨f.left ≫ (e W x).val, by rw [Category.assoc, (e W x).property,
        MorphismProperty.Over.w f]⟩ from congrArg Subtype.val heq
  apply (Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) V.hom).injective
  apply Subtype.ext
  have hnat := kummerCoverHomEquiv_precomp (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom
    f.left V.hom (MorphismProperty.Over.w f) (e W x)
  have he (W : T.Etale) (x : (rootTorsor T l r hT v).sheaf.obj.obj (op W)) :
      ((Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom)
        (e W x)).val = x.val.down.toMul.val := by
    exact congrArg Subtype.val
      ((Scheme.kummerCoverHomEquiv (l ^ (r + 1)) (v : Γ(T, ⊤)) W.hom).apply_symm_apply _)
  rw [he] at hnat
  rw [he]
  exact hnat.symm

/-- Extending the root torsor by the specified coefficient insertion gives the class kappa.
Source: blueprint sk-def-purity-conv, equivalent torsor description
(blueprint: sk-def-purity-conv).
Proof: the root torsor is the sheaf of lifts in the Kummer exact sequence, so its
canonical class is the boundary of v by classH1_lifts. On every affine chart the
same root equation represents this sheaf by O[T0]/(T0^l^(r+1)-v), hence by the
published kummerCover. Coefficient functoriality of the torsor classification
identifies the contracted-product class with H1 of insertion applied to this
boundary. Applying comparison and the normalized coefficient identification gives
exactly the defining composite of kummer. -/
theorem kummer_torsor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))) (v : Γ(T, ⊤)ˣ) :
    ∃ S : Sheaf.Torsor ((Scheme.kummerAbelianTwist T (l ^ (r + 1))).obj
        (coefficientModule A (l ^ (r + 1)) hA)),
      Nonempty (Sheaf.Torsor.ContractedProductPresentation T
        (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
          (coefficientModule A (l ^ (r + 1)) hA) (1 : A))
        (rootTorsor T l r hT v) S) ∧
      Sheaf.H.map (coefficientComparison T l A r hA hT).hom 1
        (ProEtale.comparisonCohomologyMap T _ 1
          (Sheaf.Torsor.classH1 _ terminalIsTerminal ⟦S⟧)) =
        kummer T l A r hA hT v := by
  obtain ⟨S, hS, hclass⟩ := Sheaf.Torsor.etale_torsor_h1_functoriality.2 T _ _
    (Scheme.kummerCoefficientInsertion T (l ^ (r + 1))
      (coefficientModule A (l ^ (r + 1)) hA) (1 : A)) (rootTorsor T l r hT v)
  refine ⟨S, hS, ?_⟩
  have hroot : Sheaf.Torsor.classH1 _ terminalIsTerminal ⟦rootTorsor T l r hT v⟧ =
      T.kummerδ₀ (l ^ (r + 1)) hT (Additive.ofMul v) := by
    exact (Sheaf.Torsor.classH1_congr
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
      terminalIsTerminal _).trans (Sheaf.Torsor.classH1_lifts _ _ _)
  rw [← hclass, hroot]
  rfl

/-- Every positive power of the coefficient prime is a unit on a k-scheme.
Source: blueprint sk-def-purity-conv, invertibility convention
(blueprint: sk-def-purity-conv).
Proof: ell differs from the characteristic of the fixed field k, hence is a unit
in k. Take its r+1 power and map along the structure morphism on global sections.
The argument includes the empty scheme. -/
theorem coefficientPower_isUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
  have hl : IsUnit ((P.coefficients.l : Γ(T, ⊤)) ^ P.level) := by
    simpa only [PurityFiniteSetting.diagonalExponent, Nat.cast_pow] using
      P.diagonalExponent_isUnit a
  simpa only [Nat.cast_pow] using
    ((isUnit_pow_iff (Nat.ne_of_gt P.level_pos)).mp hl).pow (r + 1)

/-- N=n is always an admissible annihilator, even when e does not divide n.
The predecessor index represents exactly n because level_pos gives n>=1.
Source: blueprint sk-def-purity-conv, default Kummer level
(blueprint: sk-def-purity-conv).
Proof: diagonalExponent_annihilates gives ell^n=0 in the quotient and its lift.
Use (n-1)+1=n, following from level_pos. In the DVR the underlying containment
is (ell^n) subset (varpi^n), since the ramification index is at least one. -/
theorem defaultAnnihilator (P : PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ (P.level - 1 + 1) : ℕ) : P.Coefficient) = 0 := by
  simpa only [Nat.sub_add_cancel P.level_pos, PurityFiniteSetting.diagonalExponent] using
    P.diagonalExponent_annihilates

/-- The rank-one datum kappa(t) of the actual affine coordinate, at N=n.
No ramification-divisibility hypothesis is imposed. The affine line, its zero
section, complement, and coordinate unit are the recorded constructions.
Source: blueprint sk-def-purity-conv, rank-one datum
(blueprint: sk-def-purity-conv). -/
def coordinateKummer (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    Sheaf.H (finiteLine (PurityFiniteSetting.Punctured Y) P.coefficients.l P.Coefficient
      (P.level - 1) (defaultAnnihilator P)) 1 :=
  kummer (PurityFiniteSetting.Punctured Y) P.coefficients.l P.Coefficient (P.level - 1)
    (defaultAnnihilator P)
    (coefficientPower_isUnit P (PurityFiniteSetting.Punctured Y)
      (PurityFiniteSetting.puncturedProjection Y ≫ aY) (P.level - 1))
    (PurityFiniteSetting.coordinateUnit Y)

/-- The affine-local pure-codimension convention, including the empty sequence at c=0.
Only neighbourhoods of points of Z are required, so a codimension-zero clopen component
is allowed. Source: blueprint sk-def-purity-conv, normal-cone paragraph
(blueprint: sk-def-purity-conv). -/
def IsRegularOfPureCodimension {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) : Prop :=
  ∀ z : Z, ∃ U : X.affineOpens, i z ∈ U.1 ∧
    ∃ f : List Γ(X, U.1), f.length = c ∧
      RingTheory.Sequence.IsRegular Γ(X, U.1) f ∧ Ideal.ofList f = i.ker.ideal U

/-- The canonical conormal comparison is an isomorphism and the conormal has rank c.
The normal cone is the recorded relative spectrum, with its recorded augmentation
zero section; this identifies it with the symmetric-algebra rank-c normal bundle.
Source: blueprint sk-def-purity-conv, normal-cone paragraph; Stacks Tags 0637 and 00LN
(blueprint: sk-def-purity-conv).
Proof: on each affine neighbourhood in the definition, the regular generators give
a basis of I/I^2 of length c. Lem-pur-regular-sequence-graded-polynomial identifies
the associated graded algebra with the polynomial algebra on this basis, and its
map is precisely the canonical symmetric comparison of lem-pur-conormal-graded-algebra.
These local isomorphisms and bases descend. The relative spectrum is contravariant,
so this identifies its cone with the vector bundle. The comparison preserves degree
zero and the positive-degree augmentation ideal, so also identifies the zero sections.
For c=0 use the empty regular sequence: the ideal is zero near Z, the conormal is
zero, and both graded algebras are O_Z in degree zero. -/
theorem regularNormalBundle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) (h : IsRegularOfPureCodimension i c) :
    (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison i) := by
  sorry

end WeilConjectures.PurityConventions
