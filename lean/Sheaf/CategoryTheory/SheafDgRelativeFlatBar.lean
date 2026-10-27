module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.StalkTensorComplex
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # The relative flat bar for left sheaf dg modules

Source: Stacks Project, sdga.tex, Tags 0FTF and 0FTR, definition-pullback;
the D-relative bar refinement and signs are the agent-written refinement in
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension).

The specifications below describe actual scalar realizations, coproduct terms,
differentials, actions and normalized comparisons. They choose no data from a
mere existence assertion. The theorem asserts existence of this fully specified
representative together with the universal derived pair.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace CategoryTheory.SheafDg.RelativeFlatBar

variable {X : TopCat.{u}} {D : Type u} [CommRing D]
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (σ : (constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    (CommRingCat.of D) ⟶ S)

/-- Scalar realization of a single D-module, using the existing sheafification and
change-of-rings construction. Source: Stacks 03CY, 03EK and the relative bar refinement
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
abbrev scalar (V : ModuleCat.{u} D) :=
  SheafOfModules.scalarConstantRealization (Opens.grothendieckTopology X) D S σ V

/-- The canonical section s tensor v of scalar realization. Source: Stacks 03EK;
relative bar refinement (blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
abbrev generator (V : ModuleCat.{u} D) (U : (Opens X)ᵒᵖ)
    (s : S.obj.obj U) (v : V) :=
  SheafOfModules.scalarConstantGenerator (Opens.grothendieckTopology X) D S σ V U s v

/-- Multiplication on homogeneous D-algebra elements, with the total tensor inclusion.
Source: Stacks definition-dga; relative bar refinement
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def mul (P : Mon (CochainComplex (ModuleCat.{u} D) ℤ)) (p q : ℤ)
    (a : P.X.X p) (b : P.X.X q) : P.X.X (p + q) :=
  (HomologicalComplex.ιTensorObj P.X P.X p q (p + q) rfl ≫
    (MonObj.mul : P.X ⊗ P.X ⟶ P.X).f (p + q)) (TensorProduct.tmul D a b)

/-- A normalized scalar algebra S tensor_D P. The degree isomorphisms are with the
actual sheafified scalar modules, not arbitrary replacement objects. Differential,
product and unit are fixed on the locally generating pure sections.
Source: Stacks 03EK, definition-dga; relative bar refinement
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
structure ScalarAlgebra (P : Mon (CochainComplex (ModuleCat.{u} D) ℤ))
    (A : Algebra S) where
  term : ∀ i : ℤ, scalar σ (P.X.X i) ≅ A.X.X i
  differential (i j : ℤ) (U : (Opens X)ᵒᵖ) (s : S.obj.obj U) (a : P.X.X i) :
    (A.X.d i j).val.app U ((term i).hom.val.app U (generator σ _ U s a)) =
      (term j).hom.val.app U (generator σ _ U s (P.X.d i j a))
  multiplication (p q : ℤ) (U : (Opens X)ᵒᵖ)
      (s t : S.obj.obj U) (a : P.X.X p) (b : P.X.X q) :
    actionSection A (regular A) p q U
      ((term p).hom.val.app U (generator σ _ U s a))
      ((term q).hom.val.app U (generator σ _ U t b)) =
        (term (p + q)).hom.val.app U (generator σ _ U (s * t) (mul P p q a b))
  unit (U : (Opens X)ᵒᵖ) (s : S.obj.obj U) :
    (term 0).hom.val.app U
      (generator σ _ U s ((MonObj.one : 𝟙_ _ ⟶ P.X).f 0
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} D))).inv
          (1 : D)))) =
    ((MonObj.one : 𝟙_ (Complex S) ⟶ A.X).f 0).val.app U
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (ringedSiteModules.{u} (rings S)))).inv.val.app U s)

variable {σ}

/-- The tail P to the n tensor M with a fixed right association. Tensoring scalar
realizations over S is canonically Q tensor_D P^n tensor_D M by balancing.
Source: relative bar refinement, displayed V_n
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def tail (A : Algebra S) (M : LeftModule A) : ℕ → Complex S
  | 0 => M.X
  | n + 1 => A.X ⊗ tail A M n

/-- The unshifted V_n, as the underlying complex of the free left B-module on its tail.
Source: relative bar refinement, displayed V_n
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
abbrev term {A B : Algebra S} (_φ : A ⟶ B) (M : LeftModule A) (n : ℕ) :=
  (Mod.free B.X).obj (tail A M n)

/-- Iterated tensoring of a module chain map on the last factor.
Source: relative bar refinement, functoriality
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def tailMap (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) :
    ∀ n : ℕ, tail A M n ⟶ tail A N n
  | 0 => f.hom
  | n + 1 => A.X ◁ tailMap A f n

/-- Adjacent multiplication, followed at the last position by the module action.
Source: relative bar refinement, faces
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def tailFace (A : Algebra S) (M : LeftModule A) :
    ∀ n : ℕ, Fin (n + 1) → (tail A M (n + 1) ⟶ tail A M n)
  | 0, _ => ModObj.smul (M := A.X) (X := M.X)
  | n + 1, i => if _h : i.val = 0 then
      (α_ A.X A.X (tail A M n)).inv ≫ MonObj.mul ▷ tail A M n
    else A.X ◁ tailFace A M n ⟨i.val - 1, by omega⟩

/-- All faces: the first multiplies Q by φ(P); the remainder multiply adjacent P's
or act on M. Source: relative bar refinement, faces
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def face {A B : Algebra S} (φ : A ⟶ B) (M : LeftModule A)
    (n : ℕ) (i : Fin (n + 2)) : (term φ M (n + 1)).X ⟶ (term φ M n).X :=
  if _h : i.val = 0 then
    (α_ B.X A.X (tail A M n)).inv ≫
      ((B.X ◁ φ.hom) ≫ MonObj.mul) ▷ tail A M n
  else B.X ◁ tailFace A M n ⟨i.val - 1, by omega⟩

/-- Unit insertion on the tail, including before M.
Source: relative bar refinement, degeneracies
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def tailDegeneracy (A : Algebra S) (M : LeftModule A) :
    ∀ n : ℕ, Fin (n + 1) → (tail A M n ⟶ tail A M (n + 1))
  | 0, _ => (λ_ M.X).inv ≫ MonObj.one ▷ M.X
  | n + 1, i => if _h : i.val = 0 then
      (λ_ (tail A M (n + 1))).inv ≫ MonObj.one ▷ tail A M (n + 1)
    else A.X ◁ tailDegeneracy A M n ⟨i.val - 1, by omega⟩

/-- Degeneracies insert the unit of P, leaving the Q factor fixed.
Source: relative bar refinement, degeneracies
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def degeneracy {A B : Algebra S} (φ : A ⟶ B) (M : LeftModule A)
    (n : ℕ) (i : Fin (n + 1)) : (term φ M n).X ⟶ (term φ M (n + 1)).X :=
  B.X ◁ tailDegeneracy A M n i

/-- A bar representative with its coproduct decomposition and all normalizations.
The colimit field specifies direct sums of sheaves, rather than sectionwise direct
sums. The differential has the internal sign (-1)^n and the alternating face part.
The action equation includes (-1)^(n degree(q)); S-linearity is part of every map.
Source: relative bar refinement, bar formula and augmentation
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
structure Model {A B : Algebra S} (φ : A ⟶ B) where
  bar : LeftModule A ⥤ LeftModule B
  inclusion : ∀ (M : LeftModule A) (n : ℕ) (k : ℤ),
    (term φ M n).X.X (k + (n : ℤ)) ⟶ (bar.obj M).X.X k
  directSum (M : LeftModule A) (k : ℤ) :
    IsColimit (Cofan.mk ((bar.obj M).X.X k) (fun n : ℕ => inclusion M n k))
  differential_zero (M : LeftModule A) (k : ℤ) : HEq
    (inclusion M 0 k ≫ (bar.obj M).X.d k (k + 1))
    ((term φ M 0).X.d (k + (0 : ℕ)) (k + 1 + (0 : ℕ)) ≫ inclusion M 0 (k + 1))
  differential_succ (M : LeftModule A) (n : ℕ) (k : ℤ) :
    inclusion M (n + 1) k ≫ (bar.obj M).X.d k (k + 1) =
      (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) •
        ((term φ M (n + 1)).X.d (k + (n + 1 : ℕ)) (k + 1 + (n + 1 : ℕ)) ≫
          inclusion M (n + 1) (k + 1)) +
      ∑ i : Fin (n + 2), ((i.val : ℤ).negOnePow : ℤ) •
        ((face φ M n i).f (k + (n + 1 : ℕ)) ≫
          eqToHom (congrArg (term φ M n).X.X (by push_cast; omega :
            k + (n + 1 : ℕ) = k + 1 + (n : ℤ))) ≫ inclusion M n (k + 1))
  leftAction (M : LeftModule A) (n : ℕ) (p k : ℤ) :
    B.X.X p ◁ inclusion M n k ≫ action B (bar.obj M) p k =
      (((n : ℤ) * p).negOnePow : ℤ) •
        (action B (term φ M n) p (k + n) ≫
          eqToHom (congrArg (term φ M n).X.X (by omega :
            p + (k + (n : ℤ)) = p + k + (n : ℤ))) ≫ inclusion M n (p + k))
  naturality {M N : LeftModule A} (f : M ⟶ N) (n : ℕ) (k : ℤ) :
    inclusion M n k ≫ (bar.map f).hom.f k =
      ((Mod.free B.X).map (tailMap A f n)).hom.f (k + n) ≫ inclusion N n k
  augmentation : bar ⟶ extension φ
  augmentation_zero (M : LeftModule A) (k : ℤ) : HEq
    (inclusion M 0 k ≫ (augmentation.app M).hom.f k) ((extensionπ φ M).hom.f k)
  augmentation_succ (M : LeftModule A) (n : ℕ) (k : ℤ) :
    inclusion M (n + 1) k ≫ (augmentation.app M).hom.f k = 0

/-- The derived realization of a bar, including its action-normalized adjunction.
The bar isomorphism is natural on the localization, not just on cohomology sheaves.
The comparison equation fixes the universal derived pair. Restriction is identified
with the actual restriction on modules, and the counit is the specified comparison
followed by action, hence is q tensor n maps to qn in length zero and zero above it.
Source: Stacks 0FTF, 0FTR; relative bar refinement
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
structure Computation {A B : Algebra S} (φ : A ⟶ B) (m : Model φ) where
  preserves {M N : LeftModule A} (f : M ⟶ N) :
    QuasiIso f.hom → QuasiIso (m.bar.map f).hom
  derived : DerivedExtension φ
  barDerived : Derived A ⥤ Derived B
  barLocalization : m.bar ⋙ moduleQ B ≅ moduleQ A ⋙ barDerived
  comparisonIso : barDerived ≅ derived.functor
  comparison (M : LeftModule A) :
    barLocalization.hom.app M ≫ comparisonIso.hom.app ((moduleQ A).obj M) ≫
      derived.comparison.app ((q A).obj M) = (moduleQ B).map (m.augmentation.app M)
  restriction : Derived B ⥤ Derived A
  restrictionIso : moduleQ B ⋙ restriction ≅ restrictScalars φ ⋙ moduleQ A
  adjunction : derived.functor ⊣ restriction
  counit (N : LeftModule B) :
    derived.functor.map (restrictionIso.hom.app N) ≫ derivedActionCounit derived N =
      adjunction.counit.app ((moduleQ B).obj N)

/-- The underlying constant coefficient ring, retaining the existing constant sheaf.
Source: Stacks 03CY; relative bar unit case
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
abbrev constantRing (X : TopCat.{u}) (D : Type u) [CommRing D] :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj (CommRingCat.of D)

/-- Forget S-linearity to the constant coefficient ring, termwise on the actual complex.
Source: Stacks 03EK; relative bar unit case
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def underlyingD (σ : constantRing X D ⟶ S) :
    Complex S ⥤ Complex (constantRing X D) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map σ)).mapHomologicalComplex (.up ℤ)

/-- Forget S-linearity and localize over the constant D sheaf. Naming this composite
keeps the natural comparison's category instances shared during elaboration.
Source: Stacks 03EK and 06YU; relative bar unit case
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
def underlyingDLocalization (σ : constantRing X D ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (rings (constantRing X D)))] :
    Complex S ⥤ DerivedCategory (ringedSiteModules.{u} (rings (constantRing X D))) :=
  underlyingD σ ⋙ DerivedCategory.Q

/-- The P=D specialization, natural in M. The ordinary identification is normalized
by the balanced quotient. Its composite with the bar augmentation is a quasi-isomorphism.
Thus the same universal derived pair is the derived functor of B tensor_S -.
The last field identifies its underlying object with the existing D-derived tensor,
using the constant realization of Q, naturally on every module chain map. Combined
with Computation.barLocalization and comparisonIso this is natural on localization.
Source: Stacks 06YU, 0FTF; relative bar refinement, final two proof steps
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension). -/
structure UnitComputation
    (σ : constantRing X D ⟶ S)
    (Q₀ : Mon (CochainComplex (ModuleCat.{u} D) ℤ))
    {A B : Algebra S} (φ : A ⟶ B) (m : Model φ)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (rings (constantRing X D)))] where
  ordinaryIso : extension φ ≅ Mod.forget A.X ⋙ Mod.free B.X
  quotient (M : LeftModule A) :
    extensionπ φ M ≫ ordinaryIso.hom.app M = 𝟙 ((Mod.free B.X).obj M.X)
  augmentation_quasiIso (M : LeftModule A) :
    QuasiIso ((m.augmentation.app M ≫ ordinaryIso.hom.app M).hom)
  constantQ : Algebra (constantRing X D)
  constantQ_normalized : ScalarAlgebra (𝟙 (constantRing X D)) Q₀ constantQ
  underlyingIso :
    m.bar ⋙ Mod.forget B.X ⋙ underlyingDLocalization σ ≅
      ((Functor.const (LeftModule A)).obj (DerivedCategory.Q.obj constantQ.X)).prod'
        (Mod.forget A.X ⋙ underlyingDLocalization σ) ⋙
        SheafOfModules.siteDerivedTensorIndependentCoefficients
          (Opens.grothendieckTopology X) (constantRing X D)

/-- The D-relative flat bar represents the specified universal derived extension,
with the actual action counit and the P=D specialization. No boundedness or flatness
of S or M is assumed; K-flatness concerns only the underlying D-complexes P and Q.

Source: Stacks Project, sdga.tex, Tags 0FTF, 0FTR, definition-pullback;
the bar is the agent-written computational refinement recorded in the node.
(blueprint: lem-sfb-sheaf-dg-relative-flat-bar-extension).

Proof plan, following the node:
1. Apply lem-sfb-ringed-dg-scalar-adjunction on the open site, using opposite
algebras for left modules. Keep its universal pair and action-normalized counit.
2. Form the sheafified scalar algebras by their locally generating pure tensors.
The face identities cancel the square of the alternating differential. Internal
chain-map identities cancel the mixed terms, giving D squared zero. The shifted
Q-action has sign (-1)^(n degree(q)); all operations retain the S-action on M.
3. The length-zero balanced quotient kills the two length-one faces. Tensor module
maps on the last factor. A degree -1 homotopy induces (-1)^n times its tensor on
length n, with the internal Koszul sign. The horizontal terms cancel, so the bar
and its augmentation descend through the homotopy quotient.
4. Constant P and Q have stalks P and Q. Use lem-pc-kflat-stalk-criterion and
lem-pc-stalk-tensor-complex to obtain K-flatness over the constant D sheaf.
Finite tensor products preserve it by successive tensoring with an acyclic complex.
5. Filter the cone of the bar of a quasi-isomorphism by finite bar lengths. Each
successive quotient is a shifted acyclic tensor cone. The long exact cohomology
sequence proves each finite stage acyclic; exact filtered colimits of abelian
sheaves prove the full cone acyclic. This works for unbounded M.
6. The augmented bimodule R=B(Q,P,C) retracts S-linearly onto C'. Its section is
q tensor (s tensor 1); its homotopy appends the last P factor and inserts 1,
with sign (-1)^(n+1). The last face gives 1-iu and the other faces cancel.
The contraction need not be right C-linear.
7. By lem-sfb-sheaf-dg-hflat-computation resolve M by a graded-flat homotopically
flat H. Balance R tensor_C H with B(Q,P,H), inserting 1 for the inverse.
The augmentation u tensor H is a quasi-isomorphism, hence so is alpha_H.
8. Universality gives the bar comparison to the specified derived pair. It is an
isomorphism on H, then on M by naturality along H to M. Its comparison is alpha,
so its counit is alpha followed by action: q tensor n maps to qn in length zero,
zero above. This is S-linear, including when S is not D-flat.
9. For P=D every face is the identity after balancing the D factors. The alternating
face differential is identity in positive even lengths and zero in odd lengths.
The odd-to-even identity contracts the positive-length kernel. The resulting
natural quasi-isomorphism to Q tensor_D M is the ordinary quotient followed by
ordinaryIso, which also identifies this universal pair with B tensor_S^L -.
10. Resolve the constant Q by a flat-term K-flat complex. Its acyclic K-flat cone
tensored with arbitrary M is acyclic by lem-pur-acyclic-kflat-tensor-arbitrary.
Apply lem-trf-site-one-sided-tensor-normalization to identify the result with
Q tensor_D^L M. This is natural; no flatness of M or flat terms of Q are needed. -/
theorem relative_flat_bar_extension
    (σ : constantRing X D ⟶ S)
    (P Q₀ : Mon (CochainComplex (ModuleCat.{u} D) ℤ)) (φ₀ : P ⟶ Q₀)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} D) (.up ℤ)).kFlat P.X)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} D) (.up ℤ)).kFlat Q₀.X)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (rings (constantRing X D)))] :
    ∃ (A B : Algebra S) (a : ScalarAlgebra σ P A) (b : ScalarAlgebra σ Q₀ B)
      (φ : A ⟶ B),
      (∀ (i : ℤ) (U : (Opens X)ᵒᵖ) (s : S.obj.obj U) (p : P.X.X i),
        (φ.hom.f i).val.app U ((a.term i).hom.val.app U (generator σ _ U s p)) =
          (b.term i).hom.val.app U (generator σ _ U s (φ₀.hom.f i p))) ∧
      ∃ m : Model φ, Nonempty (Computation φ m) ∧
        (Nonempty (P ≅ Mon.trivial (CochainComplex (ModuleCat.{u} D) ℤ)) →
          Nonempty (UnitComputation σ Q₀ φ m)) := by
  sorry

end CategoryTheory.SheafDg.RelativeFlatBar


