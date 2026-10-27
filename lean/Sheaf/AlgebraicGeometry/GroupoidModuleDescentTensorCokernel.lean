module

public import Sheaf.AlgebraicGeometry.StackModuleRestriction
public import Sheaf.AlgebraicGeometry.SchemeGroupoidModule
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

/-! # Module descent on an arbitrary scheme-groupoid quotient

Source: Stacks Project, stacks-sheaves.tex, Tags 06WT, 06WN(1),(2), 0GQD;
spaces-groupoids.tex, Tag 077X.
(blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel)

`GroupoidModule.beta` is the inverse of the source-to-target datum in the node.
The section identifications below normalize the equivalence on all charts and on
its universal arrow, so the assertion concerns restriction, not an arbitrary equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

/-- The inclusion into all module sheaves.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentInclusion {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    ModuliSmallQCoh F hF ⥤ ringedSiteModules.{u} (moduliSmallRings F hF) :=
  ObjectProperty.ι (moduliSmallIsQuasicoherent F hF)

/-- Actual restriction to the atlas, retaining every linear map.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentAtlas {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    ModuliSmallQCoh F hF ⥤ U.left.Modules :=
  groupoidDescentInclusion F hF ⋙ moduliChartModuleRestriction hF a

/-- The canonical tensor comparison is uniquely normalized by pullback of pure tensors.
Source: Stacks 03EL (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Y.Modules) :
    (Scheme.groupoidModulePullback f).obj (M ⊗ N) ≅
      (Scheme.groupoidModulePullback f).obj M ⊗
        (Scheme.groupoidModulePullback f).obj N := by
  unfold Scheme.groupoidModulePullback
  exact Classical.choose (Scheme.Modules.module_pullback_tensor f) M N

/-- The tensor-product descent datum, in the inverse orientation beta.
Source: Stacks 06WN(2), 06WT
(blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentTensorBeta {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R}
    {i : R ⟶ R} {c : pullback s t ⟶ R} {hG : Scheme.IsGroupoid s t e i c}
    (M N : Scheme.GroupoidModule s t e i c hG) :
    (Scheme.groupoidModulePullback t).obj (M.moduleObj ⊗ N.moduleObj) ≅
      (Scheme.groupoidModulePullback s).obj (M.moduleObj ⊗ N.moduleObj) :=
  groupoidDescentPullbackTensor t M.moduleObj N.moduleObj ≪≫
    (M.beta ⊗ᵢ N.beta) ≪≫ (groupoidDescentPullbackTensor s M.moduleObj N.moduleObj).symm

/-- Canonical descent of the structure module.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentUnitBeta {U R : Scheme.{u}} (s t : R ⟶ U) :
    (Scheme.groupoidModulePullback t).obj (SheafOfModules.unit U.ringCatSheaf) ≅
      (Scheme.groupoidModulePullback s).obj (SheafOfModules.unit U.ringCatSheaf) := by
  unfold Scheme.groupoidModulePullback
  exact stackModulePullbackUnit t ≪≫ (stackModulePullbackUnit s).symm

/-- Descent pulled back along an arbitrary test arrow, with canonical composition casts.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentBetaOnTest {S : Scheme.{u}} {U R T : Over S}
    {s t : R ⟶ U} {e : U.left ⟶ R.left} {i : R.left ⟶ R.left}
    {c : pullback s.left t.left ⟶ R.left}
    {hG : Scheme.IsGroupoid s.left t.left e i c}
    (M : Scheme.GroupoidModule s.left t.left e i c hG) (r : T ⟶ R) :
    (Scheme.Modules.tensorPullback (r ≫ t).left).obj M.moduleObj ≅
      (Scheme.Modules.tensorPullback (r ≫ s).left).obj M.moduleObj := by
  exact (Scheme.Modules.tensorPullbackSectionComp r.left t.left).app M.moduleObj ≪≫
    (Scheme.Modules.tensorPullback r.left).mapIso
      (by simpa only [Scheme.groupoidModulePullback] using M.beta) ≪≫
      ((Scheme.Modules.tensorPullbackSectionComp r.left s.left).app M.moduleObj).symm

/-- The image in the quotient of a test arrow of the presenting groupoid.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentTestArrow {S : Scheme.{u}} {U R T : Over S}
    {s t : R ⟶ U} {e : U.left ⟶ R.left} {i : R.left ⟶ R.left}
    {c : pullback s.left t.left ⟶ R.left} {F : BasedCategory.{v, w} (Over S)}
    {a : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    (P : SchemeGroupoidQuotientPresentation s t e i c F a) (r : T ⟶ R) :
    a.obj (CostructuredArrow.mk (yoneda.map (r ≫ s))) ⟶
      a.obj (CostructuredArrow.mk (yoneda.map (r ≫ t))) :=
  schemeGroupoidPresentationArrow s t a P.arrows (yoneda.map (r ≫ s))
    (yoneda.map (r ≫ t)) ⟨yoneda.map r, by simp, by simp⟩

/-- Scalar identification at a chart point, using only the based-functor equality.
Source: Stacks 06TV, 06WT
(blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentChartScalars {S : Scheme.{u}} {U T : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) (x : T ⟶ U) :
    Scheme.Γ.obj (op T.left) ⟶
      (moduliSmallStructurePresheaf F).obj
        (op (a.obj (CostructuredArrow.mk (yoneda.map x)))) :=
  eqToHom (congrArg (fun Q : Over S ↦ Scheme.Γ.obj (op Q.left))
    (Functor.congr_obj a.w (CostructuredArrow.mk (yoneda.map x))).symm)

/-- Restriction along a special arrow of the quotient prestack.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentSpecialArrow {S : Scheme.{u}} {U T T' : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (x : T ⟶ U) (f : T' ⟶ T) :
    a.obj (CostructuredArrow.mk (yoneda.map (f ≫ x))) ⟶
      a.obj (CostructuredArrow.mk (yoneda.map x)) :=
  a.map (CostructuredArrow.homMk f (by simp))

/-- The canonical comparison on sections at a composed test map.
Source: Stacks 06WT (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentSectionPullback {S : Scheme.{u}} {U T T' : Over S}
    (x : T ⟶ U) (f : T' ⟶ T) (M : U.left.Modules) :
    Γ((Scheme.Modules.tensorPullback x.left).obj M, ⊤) ⟶
      Γ((Scheme.Modules.tensorPullback (f ≫ x).left).obj M, ⊤) :=
  stackModuleSectionPullback f.left ((Scheme.Modules.tensorPullback x.left).obj M) ≫
    (((Scheme.Modules.tensorPullbackSectionComp f.left x.left).inv.app M).app ⊤)

/-- The canonical pure tensor in the localization tensor, through its sheafification unit.
Source: Stacks 03EK (blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel). -/
def groupoidDescentPureTensor {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (M N : ringedSiteModules.{u} (moduliSmallRings F hF)) (x : F.objᵒᵖ)
    (m : M.val.obj x) (n : N.val.obj x) : (M ⊗ N).val.obj x :=
  letI := moduliSmallHasWeakSheafify F hF
  letI := moduliSmallWEqualsLocallyBijective F hF
  letI := moduliSmallTensorLocalization F hF
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app x
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (moduliSmallRings F hF).obj)).unit.app (M.val ⊗ N.val)).app x
        (m ⊗ₜ[(moduliSmallStructureSheaf F hF).obj.obj x] n))

/-- Restriction is a symmetric tensor equivalence and identifies ambient cokernels.
The groupoid beta is delta inverse. The test-section formulas fix the forward functor
and its datum; all arrows of the quasi-coherent categories are retained.
Source: Stacks 06WT, 06WN(1),(2), 0GQD, 077X
(blueprint: lem-sfb-groupoid-module-descent-tensor-cokernel).

Proof:
1. Form the quotient prestack with arrows (f,r), composite (gf,c(qf,r)), and
identity (1,e u). Apply lem-sfb-stackification-module-equivalence to pass to its
fppf stackification, preserving modules and local-free presentations.
2. Cartesian lifting identifies each slice at x over T with Sch/T as a ringed
site. Apply lem-sfb-scheme-big-fppf-quasicoherent-equivalence there. The canonical
base-change comparisons identify its module with pullback of the atlas module.
3. The universal vertical arrow gives beta:t*M -> s*M. Identity and composition
give the unit and inverse cocycle, exactly Scheme.GroupoidModule; delta=beta inverse.
4. Conversely assign Gamma(T,u*M) to (T,u); an arrow (f,r) pulls sections back
along f and then transports them by r*beta. The unit and cocycle prove the
presheaf laws using lem-pc-module-pullback-identity-composition and adjunction.
5. On each slice this is the quasi-coherent big-fppf module of u*M; scheme
pullback preserves quasi-coherence. Thus it is a quasi-coherent module sheaf.
6. Identity pullback recovers M and its beta. The canonical slice comparisons
recover any original module, since every arrow factors into a special and a
vertical arrow. All natural module maps are exactly the maps intertwining beta.
This proves both quasi-inverse identities and full faithfulness, including the
section, scalar, arrow, and map normalization displayed below.
7. Localized tensor restriction and the scheme big-fppf tensor comparisons
identify tensor products and units. Pure tensors determine the pullback tensor
comparison. Associators reassociate three factors, unitors multiply scalars,
and symmetry interchanges factors, proving every monoidal coherence equation.
8. Ambient cokernels exist by module-sheaf colimits. Exact slice restriction
identifies them with scheme cokernels, which are quasi-coherent by
lem-weil-pbc-quasi-coherent-module-cokernel-image. Pullbacks, being left adjoints,
preserve cokernels, so beta induces their unique datum. The cofork maps and
universal properties agree on U, and faithfulness identifies them globally.
No flatness, smoothness, DM condition, or finite generation is used. -/
theorem groupoid_module_descent_tensor_cokernel
    {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U)
    (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
    (c : pullback s.left t.left ⟶ R.left)
    (F : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (P : SchemeGroupoidQuotientPresentation s t e i c F a) :
    ∃ E : ModuliSmallQCoh F P.stack.1 ≌
        Scheme.GroupoidModule s.left t.left e i c P.groupoid,
      ∃ j : E.functor ⋙ Scheme.GroupoidModule.forgetToModules ≅
          groupoidDescentAtlas P.stack.1 a,
      ∃ b : ∀ (M : ModuliSmallQCoh F P.stack.1) (T : Over S) (x : T ⟶ U),
          Γ((Scheme.Modules.tensorPullback x.left).obj (E.functor.obj M).moduleObj, ⊤) ≃+
            M.obj.val.obj (op (a.obj (CostructuredArrow.mk (yoneda.map x)))),
      (∀ (M : ModuliSmallQCoh F P.stack.1) (W : U.left.Opens)
          (z : Γ((E.functor.obj M).moduleObj, W)),
        b M (Over.mk (W.ι ≫ U.hom)) (Over.homMk W.ι)
            (stackModuleOpenSection U.left (E.functor.obj M).moduleObj W z) =
          (j.app M).hom.app W z) ∧
      (∀ (M : ModuliSmallQCoh F P.stack.1) (T : Over S) (x : T ⟶ U)
          (r : Γ(T.left, ⊤))
          (z : Γ((Scheme.Modules.tensorPullback x.left).obj (E.functor.obj M).moduleObj, ⊤)),
        b M T x (r • z) = groupoidDescentChartScalars a x r • b M T x z) ∧
      (∀ (M N : ModuliSmallQCoh F P.stack.1) (f : M ⟶ N) (T : Over S) (x : T ⟶ U)
          (z : Γ((Scheme.Modules.tensorPullback x.left).obj (E.functor.obj M).moduleObj, ⊤)),
        b N T x (((Scheme.Modules.tensorPullback x.left).map (E.functor.map f).val).app ⊤ z) =
          f.hom.val.app _ (b M T x z)) ∧
      (∀ (M : ModuliSmallQCoh F P.stack.1) (T T' : Over S) (x : T ⟶ U) (f : T' ⟶ T)
          (z : Γ((Scheme.Modules.tensorPullback x.left).obj (E.functor.obj M).moduleObj, ⊤)),
        b M T' (f ≫ x) (groupoidDescentSectionPullback x f (E.functor.obj M).moduleObj z) =
          M.obj.val.map (groupoidDescentSpecialArrow a x f).op (b M T x z)) ∧
      (∀ (M : ModuliSmallQCoh F P.stack.1) (T : Over S) (r : T ⟶ R)
          (z : Γ((Scheme.Modules.tensorPullback (r ≫ t).left).obj
            (E.functor.obj M).moduleObj, ⊤)),
        b M T (r ≫ s) ((groupoidDescentBetaOnTest (E.functor.obj M) r).hom.app ⊤ z) =
          M.obj.val.map (groupoidDescentTestArrow P r).op (b M T (r ≫ t) z)) ∧
      (∃ hQ : ObjectProperty.IsMonoidal (moduliSmallIsQuasicoherent F P.stack.1),
        ∃ mD : MonoidalCategory (Scheme.GroupoidModule s.left t.left e i c P.groupoid),
        ∃ sD : SymmetricCategory (Scheme.GroupoidModule s.left t.left e i c P.groupoid),
        ∃ hV : (Scheme.GroupoidModule.forgetToModules
          (s := s.left) (t := t.left) (e := e) (i := i) (c := c)
          (hG := P.groupoid)).Braided,
        ∃ hA : (groupoidDescentAtlas P.stack.1 a).Braided,
        ∃ hE : E.functor.Braided,
        NatTrans.IsMonoidal j.hom ∧
        (∀ (W : U.left.Opens) (r : Γ(U.left, W)),
          (Functor.LaxMonoidal.ε (groupoidDescentAtlas P.stack.1 a)).app W r =
            (moduliOpenChartRingMap P.stack.1 a).app (op W) r) ∧
        (∀ (M N : ModuliSmallQCoh F P.stack.1) (W : U.left.Opens)
            (x : Γ((groupoidDescentAtlas P.stack.1 a).obj M, W))
            (y : Γ((groupoidDescentAtlas P.stack.1 a).obj N, W)),
          (Functor.LaxMonoidal.μ (groupoidDescentAtlas P.stack.1 a) M N).app W
              (Scheme.Modules.tmulSection x y) =
            groupoidDescentPureTensor M.obj N.obj (op ((moduliOpenChart a).obj W)) x y) ∧
        (∃ h0 : (𝟙_ (Scheme.GroupoidModule s.left t.left e i c P.groupoid)).moduleObj =
            SheafOfModules.unit U.left.ringCatSheaf,
          Functor.LaxMonoidal.ε Scheme.GroupoidModule.forgetToModules = eqToHom h0.symm ∧
          (eqToIso (congrArg (fun M ↦ (Scheme.groupoidModulePullback t.left).obj M) h0)).symm ≪≫
            (𝟙_ (Scheme.GroupoidModule s.left t.left e i c P.groupoid)).beta ≪≫
            eqToIso (congrArg (fun M ↦ (Scheme.groupoidModulePullback s.left).obj M) h0) =
              groupoidDescentUnitBeta s.left t.left) ∧
        (∀ M N : Scheme.GroupoidModule s.left t.left e i c P.groupoid,
          ∃ hMN : (M ⊗ N).moduleObj = M.moduleObj ⊗ N.moduleObj,
            Functor.LaxMonoidal.μ Scheme.GroupoidModule.forgetToModules M N =
              eqToHom hMN.symm ∧
            (eqToIso (congrArg (fun K ↦ (Scheme.groupoidModulePullback t.left).obj K) hMN)).symm ≪≫
              (M ⊗ N).beta ≪≫
              eqToIso (congrArg (fun K ↦ (Scheme.groupoidModulePullback s.left).obj K) hMN) =
                groupoidDescentTensorBeta M N)) ∧
      (∀ (M N : ModuliSmallQCoh F P.stack.1) (f : M ⟶ N),
        ∃ hK : moduliSmallIsQuasicoherent F P.stack.1 (cokernel f.hom),
        ∃ k : (E.functor.obj ⟨cokernel f.hom, hK⟩).moduleObj ≅
            cokernel (E.functor.map f).val,
          (E.functor.map (ObjectProperty.homMk (cokernel.π f.hom))).val ≫ k.hom =
            cokernel.π (E.functor.map f).val) := by
  sorry

end CategoryTheory
