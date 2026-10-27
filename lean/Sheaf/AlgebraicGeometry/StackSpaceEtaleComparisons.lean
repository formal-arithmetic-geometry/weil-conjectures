/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.SpaceAmbientModuleOperations
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange


/-! # Canonical small étale restrictions and tensor comparisons on space tests

Source: Stacks Project, stacks-sheaves.tex, Tags 075D, 076R and 0GQC;
stacks-cohomology.tex, Tag 0762
(blueprint: def-sfb-stack-space-etale-comparisons).

Restrictions are actual precomposition, with the canonical regular-function transport.
The tensor-section normalization characterizes comparisons and the pullback unitors and
compositors, so none of the coherence assertions concerns an arbitrary map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- The inclusion of small étale charts followed by the specified algebraic-space test.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceEtaleLift {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {V : AlgebraicSpace S} (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    V.EtaleSite ⥤ C.obj :=
  ObjectProperty.ι _ ⋙ z.toFunctor

/-- Étale chart coverings become fppf coverings under a test over Sch/S.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: the test preserves the underlying scheme maps. A jointly surjective étale
cover is fppf. Its overlap diagrams and their images are the same scheme diagrams;
apply the sheaf gluing condition on the total category to the resulting matching family. -/
theorem stackSpaceEtaleLift_isContinuous {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    {V : AlgebraicSpace S} (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    (stackSpaceEtaleLift z).IsContinuous V.etaleTopology (moduliFppfTopology C) := by
  sorry

/-- The test's equality over the base identifies the two underlying chart schemes.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceTestSchemeIso {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {V : AlgebraicSpace S} (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (T : V.EtaleSite) :
    (moduliSchemeForget C).obj ((stackSpaceEtaleLift z).obj T) ≅
      (V.etaleForget).obj T :=
  eqToIso (congrArg (fun Q : Over S ↦ Q.left) (z.w_obj T.obj))

/-- The actual pullback of functions in canonical ULift coordinates.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceRingApp {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {V : AlgebraicSpace S} (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (T : V.EtaleSite) :
    (AmbientCoefficients.structureSheaf.{u, max v w} V).obj.obj (op T) ⟶
      (moduliStructurePresheaf C ⋙ forget₂ CommRingCat RingCat).obj
        (op ((stackSpaceEtaleLift z).obj T)) :=
  RingCat.ofHom (Scheme.Γ.map (stackSpaceTestSchemeIso z T).hom.op).hom.ulift

/-- Pullback of functions is natural in a chart arrow.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: the equality z.w identifies the scheme maps of both functors. Apply the
contravariant regular-functions functor and its composition law; ULift is functorial. -/
theorem stackSpaceRingApp_naturality {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    {T U : V.EtaleSiteᵒᵖ} (f : T ⟶ U) :
    (AmbientCoefficients.structureSheaf.{u, max v w} V).obj.map f ≫
        stackSpaceRingApp z U.unop =
      stackSpaceRingApp z T.unop ≫
        (moduliStructurePresheaf C ⋙ forget₂ CommRingCat RingCat).map
          ((stackSpaceEtaleLift z).op.map f) := by
  sorry

/-- The structural ring map for literal small-site restriction.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceRingMap {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    (hC : IsFibredInGroupoids C) {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    (AmbientCoefficients.structureSheaf.{u, max v w} V).obj ⟶
      (stackSpaceEtaleLift z).op ⋙ (moduliModuleRings C hC).obj where
  app T := stackSpaceRingApp z T.unop
  naturality {_ _} f := stackSpaceRingApp_naturality z f

/-- Restriction H_z has exactly H(z(T)) as its section carrier and H's restriction maps.
Only scalars are transported along the canonical identification of chart schemes.
Source: Stacks 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceRestriction {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    (hC : IsFibredInGroupoids C) {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      AmbientCoefficients.Modules.{u, max v w} V :=
  letI := stackSpaceEtaleLift_isContinuous hC z
  SheafOfModules.pushforward (F := stackSpaceEtaleLift z)
    (⟨stackSpaceRingMap hC z⟩ : AmbientCoefficients.structureSheaf V ⟶ _)

/-- The arrow whose restriction map defines c_(a,theta) on a compatible pair of charts.
It is theta followed by the target test applied to the actual scheme-chart arrow.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceComparisonArrow {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (T : W.EtaleSite) (q : ModuleChart a T) :
    (stackSpaceEtaleLift z).obj q.left ⟶ (stackSpaceEtaleLift t).obj T :=
  theta.val.hom.app q.left.obj ≫ t.map q.hom

/-- The tensor identity is uniquely normalized by multiplication on every chart.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: multiplication sends b tensor m to b times the restricted section. Inserting
1 gives the inverse. Balancing, restriction and sheafification preserve these formulas;
local tensor generators prove uniqueness and naturality. -/
theorem stackSpaceTensorId_existsUnique {S : Scheme.{u}} (V : AlgebraicSpace S) :
    ∃! e : AmbientCoefficients.moduleTensorPullback.{u, m} (𝟙 V) ≅
        𝟭 (AmbientCoefficients.Modules.{u, m} V),
      ∀ (M : AmbientCoefficients.Modules.{u, m} V) (T : V.EtaleSite)
        (q : ModuleChart (𝟙 V) T)
        (b : (AmbientCoefficients.structureSheaf.{u, m} V).obj.obj (op q.left))
        (m : M.val.obj (op T)),
        (e.hom.app M).val.app (op q.left)
            (AmbientCoefficients.moduleTensorSection.{u, m} (𝟙 V) M T q b m) =
          b • M.val.map (ObjectProperty.homMk q.hom : q.left ⟶ T).op m := by
  sorry

/-- The canonical tensor unitor, fixed by its unique multiplication normalization.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceTensorId {S : Scheme.{u}} (V : AlgebraicSpace S) :
    AmbientCoefficients.moduleTensorPullback.{u, m} (𝟙 V) ≅
      𝟭 (AmbientCoefficients.Modules.{u, m} V) :=
  Classical.choose (stackSpaceTensorId_existsUnique.{u, m} V)

/-- Tensor associativity fixes the pullback compositor on all iterated local tensors.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: send c tensor (d tensor m) to c times a-sharp(d) tensor m. The inverse inserts
1. Tensor balancing proves the inverse equations; the formulas commute with chart
restrictions, hence sheafify. Local tensor generators prove uniqueness and naturality. -/
theorem stackSpaceTensorComp_existsUnique {S : Scheme.{u}} {V W B : AlgebraicSpace S}
    (a : V ⟶ W) (b : W ⟶ B) :
    ∃! e : AmbientCoefficients.moduleTensorPullback.{u, m} b ⋙
        AmbientCoefficients.moduleTensorPullback.{u, m} a ≅
          AmbientCoefficients.moduleTensorPullback.{u, m} (a ≫ b),
      ∀ (M : AmbientCoefficients.Modules.{u, m} B) (T : B.EtaleSite)
        (q : ModuleChart b T) (r : ModuleChart a q.left)
        (c : (AmbientCoefficients.structureSheaf.{u, m} V).obj.obj (op r.left))
        (d : (AmbientCoefficients.structureSheaf.{u, m} W).obj.obj (op q.left))
        (m : M.val.obj (op T)),
        (e.hom.app M).val.app (op r.left)
            (AmbientCoefficients.moduleTensorSection.{u, m} a
              ((AmbientCoefficients.moduleTensorPullback.{u, m} b).obj M) q.left r c
                (AmbientCoefficients.moduleTensorSection.{u, m} b M T q d m)) =
          AmbientCoefficients.moduleTensorSection.{u, m} (a ≫ b) M T
            (moduleCompositeChart a b T q r)
            (c * AmbientCoefficients.moduleChartScalar.{u, m} a q.left r d) m := by
  sorry

/-- The tensor compositor selected by its unique local tensor normalization.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceTensorComp {S : Scheme.{u}} {V W B : AlgebraicSpace S}
    (a : V ⟶ W) (b : W ⟶ B) :
    AmbientCoefficients.moduleTensorPullback.{u, m} b ⋙
      AmbientCoefficients.moduleTensorPullback.{u, m} a ≅
        AmbientCoefficients.moduleTensorPullback.{u, m} (a ≫ b) :=
  Classical.choose (stackSpaceTensorComp_existsUnique.{u, m} a b)

/-- Restriction-induced tensor comparisons are uniquely characterized on local tensors.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: use H's restriction along theta followed by the target chart arrow. This is
semilinear for the corresponding regular-function pullback, and is compatible with
all chart restrictions. The compatible-section universal property gives the map
H_w to a_*H_z. Take its adjoint under the recorded tensor adjunction. The unit
normalization gives the displayed formula; local tensor generators give uniqueness. -/
theorem stackSpaceComparison_existsUnique {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t)) :
    ∃! c : stackSpaceRestriction hC t ⋙ AmbientCoefficients.moduleTensorPullback.{u, max v w} a ⟶
        stackSpaceRestriction hC z,
      ∀ (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (T : W.EtaleSite) (q : ModuleChart a T)
        (b : (AmbientCoefficients.structureSheaf.{u, max v w} V).obj.obj (op q.left))
        (m : ((stackSpaceRestriction hC t).obj H).val.obj (op T)),
        (c.app H).val.app (op q.left)
            (AmbientCoefficients.moduleTensorSection.{u, max v w} a
              ((stackSpaceRestriction hC t).obj H) T q b m) =
          b • (@id (((stackSpaceRestriction hC z).obj H).val.obj (op q.left))
            (H.val.map (stackSpaceComparisonArrow a z t theta T q).op m)) := by
  sorry

/-- The canonical comparison, selected using the complete restriction normalization.
Source: Stacks 075D, 076R (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceComparison {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} (hC : IsFibredInGroupoids C)
    {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t)) :
    stackSpaceRestriction hC t ⋙ AmbientCoefficients.moduleTensorPullback.{u, max v w} a ⟶
      stackSpaceRestriction hC z :=
  Classical.choose (stackSpaceComparison_existsUnique hC a z t theta)

/-- A scheme arrow regarded as the corresponding Yoneda arrow of algebraic spaces.
Source: Stacks 076R, 0762 (blueprint: def-sfb-stack-space-etale-comparisons). -/
def stackSpaceSchemeMap {S : Scheme.{u}} {U T : Over S} (a : U ⟶ T) :
    schemeSpace U ⟶ schemeSpace T :=
  ObjectProperty.homMk ⟨yoneda.map a⟩

/-- Additive sheafification on each small étale slice in the ambient coefficient universe.
Source: Stacks 03DL, 0GQC (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: the slice has objects in universe u+1 and arrows in u. Both lie in the
ambient universe. Two plus constructions on additive presheaves give sheafification
there and its left adjunction to the inclusion of sheaves. -/
@[instance] theorem stackSpaceSliceHasWeakSheafify {S : Scheme.{u}}
    (V : AlgebraicSpace S) (T : V.EtaleSite) [UnivLE.{u + 1, m}] :
    HasWeakSheafify (V.etaleTopology.over T) AddCommGrpCat.{m} := by
  sorry

/-- Additive sheafification inverts exactly locally bijective maps on these slices.
Source: Stacks 03DL, 0GQC (blueprint: def-sfb-stack-space-etale-comparisons).
Proof: the plus unit is locally bijective. Local lifting and local equality prove
that locally bijective maps sheafify to isomorphisms. Conversely use the locally
bijective units and an inverse on sheafifications to obtain the same two local tests. -/
@[instance] theorem stackSpaceSliceWEqualsLocallyBijective {S : Scheme.{u}}
    (V : AlgebraicSpace S) (T : V.EtaleSite) [UnivLE.{u + 1, m}] :
    (V.etaleTopology.over T).WEqualsLocallyBijective AddCommGrpCat.{m} := by
  sorry

end CategoryTheory
