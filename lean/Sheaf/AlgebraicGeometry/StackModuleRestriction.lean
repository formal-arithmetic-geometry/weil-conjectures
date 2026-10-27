module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-! # Unlifted structure coefficients and restriction to scheme charts

Source: Stacks Project, stacks-sheaves.tex, Tags 06TV, 06WG, 06WT.
(blueprint: def-sfb-stack-module-restriction)

The ambient-universe algebra interface remains publicly available. For scheme modules
in the project's section universe, use the canonically equivalent unlifted regular rings.
No equality between the site object, site arrow and scheme universes is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace CategoryTheory

/-- Forgetting commutativity preserves sheaves in the section universe.
Source: Stacks 06TV (blueprint: def-sfb-stack-module-restriction).
Proof: glue sections as a ring-valued matching family; the same amalgamation
preserves the retained operations and is unique. -/
@[instance] theorem moduliSmallCommRingCompose {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    (moduliFppfTopology F).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- Forgetting multiplication preserves sheaves, also on every slice.
Source: Stacks 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: the sheaf equalizer is computed on underlying sets, so forgetting
operations retains its unique sectionwise amalgamations. -/
@[instance] theorem moduliSmallSliceRingCompose {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (x : F.obj) :
    ((moduliFppfTopology F).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  sorry

/-- Regular functions without the ambient-universe ULift.
Source: Stacks 06TV (blueprint: def-sfb-stack-module-restriction). -/
def moduliSmallStructurePresheaf {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : F.objᵒᵖ ⥤ CommRingCat.{u} :=
  (moduliSchemeForget F).op ⋙ Scheme.Γ

/-- Unlifted regular functions satisfy precisely the same sheaf equalizer.
Source: Stacks 06TV (blueprint: def-sfb-stack-module-restriction).
Proof: identify every value and restriction with the ambient structure presheaf
using ULift.ringEquiv. Matching families and their unique amalgamations correspond
under these equivalences; apply moduliStructurePresheaf_isSheaf. -/
theorem moduliSmallStructure_isSheaf {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Presheaf.IsSheaf (moduliFppfTopology F) (moduliSmallStructurePresheaf F) := by
  sorry

/-- The same structure sheaf in the scheme section universe.
Source: Stacks 06TV (blueprint: def-sfb-stack-module-restriction). -/
def moduliSmallStructureSheaf {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Sheaf (moduliFppfTopology F) CommRingCat.{u} :=
  ⟨moduliSmallStructurePresheaf F, moduliSmallStructure_isSheaf F hF⟩

/-- Forgetting commutativity in the unlifted structure sheaf.
Source: Stacks 06WG (blueprint: def-sfb-stack-module-restriction). -/
abbrev moduliSmallRings {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :=
  (sheafCompose (moduliFppfTopology F) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (moduliSmallStructureSheaf F hF)

/-- Additive sheafification in the scheme section universe on the fibred fppf site.
Source: Stacks 06TP, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: the slice at an object over T is equivalent to Sch/T, by cartesian lifting.
Choose the small cofinal fppf refinement by affine, finitely presented covering
pieces in the scheme universe. Use additive sheafification on this refinement,
and its uniqueness on overlapping slices to glue the functors and their units.
The universal property is local and therefore gives the global adjunction. -/
theorem moduliSmallHasWeakSheafify {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    HasWeakSheafify (moduliFppfTopology F) AddCommGrpCat.{u} := by
  sorry

/-- Local bijectivity detects the unlifted additive sheafification equivalences.
Source: Stacks 06TP, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: on each scheme slice choose the small cofinal fppf refinement by affine,
finitely presented covering pieces. Use its locally bijective sheafification
criterion; local lifting and local equality agree on overlaps.
A morphism of sheaves is an isomorphism exactly when its restrictions are. -/
theorem moduliSmallWEqualsLocallyBijective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    (moduliFppfTopology F).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- The same additive sheafification on a localized fibred site.
Source: Stacks 06TP, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: the slice at x is the big fppf scheme site of its underlying T.
Use the small cofinal fppf refinement by affine, finitely presented covering
pieces in the scheme universe, and transfer additive sheafification along this
cover-preserving equivalence. -/
theorem moduliSmallSliceHasWeakSheafify {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    HasWeakSheafify ((moduliFppfTopology F).over x) AddCommGrpCat.{u} := by
  sorry

/-- Local bijectivity on the localized fibred site.
Source: Stacks 06TP, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: transfer the local-injectivity and local-surjectivity criterion from Sch/T
along the slice equivalence and its small cofinal fppf refinement by affine,
finitely presented covering pieces; both conditions are stated by covering sieves. -/
theorem moduliSmallSliceWEqualsLocallyBijective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    ((moduliFppfTopology F).over x).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- The literal open-chart functor into the total category.
Source: Stacks 06WT (blueprint: def-sfb-stack-module-restriction). -/
def moduliOpenChart {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) : U.left.Opens ⥤ F.obj :=
  { obj W := a.obj (CostructuredArrow.mk
      (yoneda.map (Over.homMk W.ι : Over.mk (W.ι ≫ U.hom) ⟶ U)))
    map {W V} j := a.map (CostructuredArrow.homMk
      (Over.homMk (U.left.homOfLE j.le) (by simp)) (by
        change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
        rw [← yoneda.map_comp]
        congr 1
        apply Over.OverMorphism.ext
        simp))
    map_id W := by
      rw [← a.map_id]
      congr 1
      apply CostructuredArrow.hom_ext
      apply Over.OverMorphism.ext
      change U.left.homOfLE (show W ≤ W from le_rfl) = 𝟙 W.toScheme
      exact Scheme.homOfLE_rfl _ _
    map_comp j k := by
      simp only [← Functor.map_comp]
      congr 1
      apply CostructuredArrow.hom_ext
      apply Over.OverMorphism.ext
      change U.left.homOfLE (j.le.trans k.le) =
        U.left.homOfLE j.le ≫ U.left.homOfLE k.le
      exact (Scheme.homOfLE_homOfLE U.left j.le k.le).symm }

/-- A based chart has exactly the underlying open schemes, including restrictions.
Source: Stacks 06TV, 06WT (blueprint: def-sfb-stack-module-restriction).
Proof: apply the equality a.w to each open-chart object and arrow. The
projection of a costructured arrow is its domain, giving the restriction functor. -/
theorem moduliOpenChart_scheme {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    moduliOpenChart a ⋙ moduliSchemeForget F = U.left.restrictFunctor ⋙ Over.forget U.left := by
  sorry

/-- The chart coefficient map is restriction of regular functions, with only canonical casts.
Source: Stacks 06TV, 06WT (blueprint: def-sfb-stack-module-restriction). -/
def moduliOpenChartRingMap {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    U.left.ringCatSheaf.obj ⟶ (moduliOpenChart a).op ⋙ (moduliSmallRings F hF).obj :=
  Functor.whiskerRight U.left.restrictFunctorΓ.inv (forget₂ CommRingCat RingCat) ≫
    eqToHom (congrArg (fun H : U.left.Opens ⥤ Scheme.{u} ↦
      H.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat) (moduliOpenChart_scheme a).symm)

/-- A restricted module is a Zariski sheaf on the chart.
Source: Stacks 06TV, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: an open covering of a chart is an fppf covering in the total site.
The module sheaf equalizer restricts to this same matching-family equalizer;
the regular-function comparisons identify its scalars with the chart's rings. -/
theorem moduliOpenChartModule_isSheaf {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (M : ringedSiteModules.{u} (moduliSmallRings F hF)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology U.left)
      (((PresheafOfModules.pushforward (moduliOpenChartRingMap hF a)).obj M.val).presheaf) := by
  sorry

/-- Restriction to the Zariski opens of a scheme chart, on objects and every module map.
Source: Stacks 06WT (blueprint: def-sfb-stack-module-restriction). -/
def moduliChartModuleRestriction {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    ringedSiteModules.{u} (moduliSmallRings F hF) ⥤ U.left.Modules where
  obj M := ⟨(PresheafOfModules.pushforward (moduliOpenChartRingMap hF a)).obj M.val,
    moduliOpenChartModule_isSheaf hF a M⟩
  map f := ⟨(PresheafOfModules.pushforward (moduliOpenChartRingMap hF a)).map f.val⟩

/-- Quasi-coherence is the existing local-free-presentation predicate.
Source: Stacks 06WG (blueprint: def-sfb-stack-module-restriction). -/
def moduliSmallIsQuasicoherent {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (M : ringedSiteModules.{u} (moduliSmallRings F hF)) : Prop :=
  letI := moduliSmallSliceHasWeakSheafify F hF
  letI := moduliSmallSliceWEqualsLocallyBijective F hF
  SheafOfModules.IsQuasicoherent M

/-- All quasi-coherent modules and all their module-sheaf morphisms.
Source: Stacks 06WG (blueprint: def-sfb-stack-module-restriction). -/
abbrev ModuliSmallQCoh {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :=
  ObjectProperty.FullSubcategory (moduliSmallIsQuasicoherent F hF)

/-- Local equivalences are stable under tensoring in this section universe.
Source: Stacks 03EK, 06WG (blueprint: def-sfb-stack-module-restriction).
Proof: restrict to each scheme slice, where sheafified tensor products invert
locally bijective maps by the local pure-tensor calculation. Being an isomorphism
of sheaves is local on these slices, so tensoring preserves the localization class. -/
theorem moduliSmallTensorLocalization {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    ((moduliFppfTopology F).W.inverseImage (PresheafOfModules.toPresheaf.{u}
      (moduliSmallRings F hF).obj)).IsMonoidal := by
  sorry

/-- The canonical localization tensor on these module sheaves.
Source: Stacks 03EK, 06WG (blueprint: def-sfb-stack-module-restriction). -/
instance moduliSmallMonoidal {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    MonoidalCategory (ringedSiteModules.{u} (moduliSmallRings F hF)) :=
  letI := moduliSmallHasWeakSheafify F hF
  letI := moduliSmallWEqualsLocallyBijective F hF
  letI := moduliSmallTensorLocalization F hF
  SheafOfModules.monoidalCategory (moduliSmallStructureSheaf F hF)

/-- Symmetry is the one descending the interchange of pure tensors.
Source: Stacks 03EK, 06WG (blueprint: def-sfb-stack-module-restriction). -/
instance moduliSmallSymmetric {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    SymmetricCategory (ringedSiteModules.{u} (moduliSmallRings F hF)) :=
  letI := moduliSmallHasWeakSheafify F hF
  letI := moduliSmallWEqualsLocallyBijective F hF
  letI := moduliSmallTensorLocalization F hF
  SheafOfModules.symmetricCategory (moduliSmallStructureSheaf F hF)

/-- Ambient module cokernels exist and are sheafified sectionwise cokernels.
Source: Stacks 06WN(1) (blueprint: def-sfb-stack-module-restriction).
Proof: take the sectionwise cokernel presheaf and apply the additive module
sheafification. Its adjunction identifies maps out with maps killing the input. -/
@[instance] theorem moduliSmallHasCokernels {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    HasCokernels (ringedSiteModules.{u} (moduliSmallRings F hF)) := by
  sorry


/-- Pullback of a global section via the section-normalized adjunction unit.
Source: Stacks 03DR, 03DU (blueprint: def-sfb-stack-module-restriction). -/
def stackModuleSectionPullback {T V : Scheme.{u}} (f : T ⟶ V) (M : V.Modules) :
    Γ(M, ⊤) ⟶ Γ((Scheme.Modules.tensorPullback f).obj M, ⊤) :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction f).unit.app M).app ⊤ ≫
    ((Scheme.Modules.tensorPullback f).obj M).presheaf.map (homOfLE f.preimage_top.ge).op

/-- The canonical section on an open subscheme, via the same adjunction unit.
Source: Stacks 0GN7 (blueprint: def-sfb-stack-module-restriction). -/
def stackModuleOpenSection (V : Scheme.{u}) (M : V.Modules) (W : V.Opens) :
    Γ(M, W) ⟶ Γ((Scheme.Modules.tensorPullback W.ι).obj M, ⊤) :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction W.ι).unit.app M).app W ≫
    ((Scheme.Modules.tensorPullback W.ι).obj M).presheaf.map (homOfLE W.ι_preimage_self.ge).op

/-- The regular-module comparison fixed by the normalized pullback adjunction.
Source: Stacks 0096, 03DU (blueprint: def-sfb-stack-module-restriction). -/
def stackModulePullbackUnit {T V : Scheme.{u}} (f : T ⟶ V) :
    (Scheme.Modules.tensorPullback f).obj (SheafOfModules.unit V.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction f).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app _ ≪≫ Scheme.Modules.pullbackObjUnitIso f

end CategoryTheory
