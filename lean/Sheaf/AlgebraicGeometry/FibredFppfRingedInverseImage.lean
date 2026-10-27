module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.Paper.SequenceSiteCompletionProjection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import Sheaf.CategoryTheory.ContinuousCocontinuousRingedRestriction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Ringed inverse image on fibred fppf sites

Source: Stacks Project, stacks-sheaves.tex, Tags 06TS, 06TW, 06WE and 06TL
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).

The site object and morphism universes remain independent of the scheme universe.
All sites are presented within common bounds `w` and `v`, as in the size convention;
modules and sets take values in the ambient universe `max (u+1) v w`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

variable {S : AlgebraicGeometry.Scheme.{u}}
  {C D E : BasedCategory.{v, w} (Over S)}

/-- Ambient-size additive sheafification exists on the inherited fppf site.
Source: Stacks Modules on Sites 03DA--03DB
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: the site objects and arrows lie in the ambient universe. The usual two
plus constructions give additive sheafification, with its universal property. -/
@[instance] theorem moduliFppfHasWeakSheafify
    (F : BasedCategory.{v, w} (Over S)) :
    HasWeakSheafify (moduliFppfTopology F) AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- Additive sheafification inverts exactly locally bijective maps.
Source: Stacks Modules on Sites 03DA--03DB
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: the sheafification units are locally bijective. Local lifting of sections
and local equality show that a map is inverted precisely when it is locally
surjective and locally injective. This applies to the small inherited site. -/
@[instance] theorem moduliFppfWEqualsLocallyBijective
    (F : BasedCategory.{v, w} (Over S)) :
    (moduliFppfTopology F).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- A functor over schemes is continuous and cocontinuous for the inherited fppf sites.
Source: Stacks 06TS, via 06NW
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: every arrow in each total category is strongly cartesian. A based functor
preserves these arrows. Apply lem-sfb-fibred-site-functor-continuity to the fppf
site of schemes: coverings and covering pullbacks are preserved, and a covering
of the image lifts by cartesian lifting in the source. This proves both assertions. -/
theorem moduliFppfFunctor_continuous_cocontinuous
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D) (a : BasedFunctor D C) :
    a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C) ∧
      a.toFunctor.IsCocontinuous (moduliFppfTopology D) (moduliFppfTopology C) := by
  sorry

/-- Literal precomposition of sheaves of sets, including restrictions and morphisms.
Source: Stacks 06TS (blueprint: lem-sfb-fibred-fppf-ringed-inverse-image). -/
def moduliSetInverseImage (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (a : BasedFunctor D C) :
    Sheaf (moduliFppfTopology C) (Type (max (u + 1) v w)) ⥤
      Sheaf (moduliFppfTopology D) (Type (max (u + 1) v w)) :=
  @Functor.sheafPushforwardContinuous _ _ _ _ a.toFunctor
    (Type (max (u + 1) v w)) _ (moduliFppfTopology D) (moduliFppfTopology C)
    (moduliFppfFunctor_continuous_cocontinuous hC hD a).1

/-- Precomposition identifies the structure rings, not merely their underlying sets.
Source: Stacks 06TW (blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: the based-functor identity a.toFunctor ⋙ C.p = D.p identifies the underlying
schemes and their maps. Both ring presheaves are the same pullback of regular
functions, with the same canonical ULift. Sheaf proof irrelevance gives equality. -/
theorem moduliInverseImage_ring_eq (hC : IsFibredInGroupoids C)
    (hD : IsFibredInGroupoids D) (a : BasedFunctor D C) :
    (@Functor.sheafPushforwardContinuous _ _ _ _ a.toFunctor
      RingCat.{max (u + 1) v w} _ (moduliFppfTopology D) (moduliFppfTopology C)
      (moduliFppfFunctor_continuous_cocontinuous hC hD a).1).obj
        (moduliModuleRings C hC) = moduliModuleRings D hD := by
  sorry

/-- Module inverse image is restriction along the based functor, with its canonical
unchanged-ring action. Source: Stacks 06WE
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image). -/
def moduliModuleInverseImage (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (a : BasedFunctor D C) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      ringedSiteModules.{max (u + 1) v w} (moduliModuleRings D hD) :=
  letI := (moduliFppfFunctor_continuous_cocontinuous hC hD a).1
  SheafOfModules.pushforward (F := a.toFunctor)
    (eqToHom (moduliInverseImage_ring_eq hC hD a).symm)

/-- The sheafified tensor O_D ⊗ Q(M), functorial in M, satisfies functor laws.
Source: Stacks 06WE and Modules on Sites 03EK
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: on the tensor presheaf the map is id ⊗ Q(f). Its identity and composition
laws follow on pure tensors from those of Q; pure tensors generate. Apply the
sheafification functor to these equalities. -/
theorem moduliTensorInverseImage_laws
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D) (a : BasedFunctor D C) :
    (∀ M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC),
      siteSheafTensorSecondMap.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
          (SheafOfModules.unit (moduliModuleRings D hD))
          ((moduliModuleInverseImage hC hD a).map (𝟙 M)) = 𝟙 _) ∧
    (∀ (M N P : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
      (f : M ⟶ N) (g : N ⟶ P),
      siteSheafTensorSecondMap.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
          (SheafOfModules.unit (moduliModuleRings D hD))
          ((moduliModuleInverseImage hC hD a).map (f ≫ g)) =
        siteSheafTensorSecondMap.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
            (SheafOfModules.unit (moduliModuleRings D hD))
            ((moduliModuleInverseImage hC hD a).map f) ≫
          siteSheafTensorSecondMap.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
            (SheafOfModules.unit (moduliModuleRings D hD))
            ((moduliModuleInverseImage hC hD a).map g)) := by
  sorry

/-- The actual tensor pullback: sheafification of O_D ⊗ Q(M), with maps id ⊗ Q(f).
Source: Stacks 06WE (blueprint: lem-sfb-fibred-fppf-ringed-inverse-image). -/
def moduliTensorInverseImage (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (a : BasedFunctor D C) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      ringedSiteModules.{max (u + 1) v w} (moduliModuleRings D hD) where
  obj M := (siteSheafTensorRight.{v, w, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
    ((moduliModuleInverseImage hC hD a).obj M)).obj
      (SheafOfModules.unit (moduliModuleRings D hD))
  map f := siteSheafTensorSecondMap.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
    (SheafOfModules.unit (moduliModuleRings D hD))
    ((moduliModuleInverseImage hC hD a).map f)
  map_id M := (moduliTensorInverseImage_laws hC hD a).1 M
  map_comp f g := (moduliTensorInverseImage_laws hC hD a).2 _ _ _ f g

/-- The canonical tensor comparison is characterized by multiplication on local pure tensors.
Source: Stacks 06WE (blueprint: lem-sfb-fibred-fppf-ringed-inverse-image). -/
def IsModuliTensorComparison
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D) (a : BasedFunctor D C)
    (e : moduliTensorInverseImage hC hD a ≅ moduliModuleInverseImage hC hD a) : Prop :=
  ∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
    (U : D.objᵒᵖ) (r : (moduliModuleRings D hD).obj.obj U)
    (m : ((moduliModuleInverseImage hC hD a).obj M).val.obj U),
    (e.hom.app M).val.app U
      (siteSheafTensorTmul.{w, v, max (u + 1) v w, max (u + 1) v w}
        (A := moduliStructureSheaf D hD)
        (SheafOfModules.unit (moduliModuleRings D hD))
        ((moduliModuleInverseImage hC hD a).obj M) U r m) = r • m

/-- Ringed fppf inverse image is precomposition on all modules, canonically identified
with tensor pullback. It is exact, preserves every ambient-small colimit, and takes
O_C to O_D. The tensor comparison is characterized on local pure tensors.
Source: Stacks 06TS, 06TW, 06WE, 06TX; Modules on Sites 03DA--03DB
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).

Proof (the five steps of the DAG node):
1. The fibred-site continuity theorem applies because every arrow is cartesian.
The continuous-cocontinuous topos adjunction gives precomposition as inverse image.
2. On d over T both rings are Γ(T,O_T), with identical restrictions. The ringed
restriction adjunction has identity structural map and module inverse image Q.
3. Sectionwise r ⊗ m ↦ r • m and m ↦ 1 ⊗ m are inverse, by balancing and 1 • m = m.
They commute with restrictions and module maps, so descend through sheafification
and give a natural tensor comparison. On the structure module they identify O_C
with O_D.
4. The module adjunction and left-adjoint-preserves-colimits give all small colimits,
including empty sums and cokernels. Kernels are sectionwise: both evaluations are
ker(v at a(d)). Q is additive sectionwise. Thus Q preserves finite limits and
colimits and is exact. The same holds for its naturally isomorphic tensor pullback.
5. Identities and compositions are literal precomposition on sections, restrictions
and module maps. The tensor comparisons multiply the scalar factors: r ⊗ (s ⊗ m)
maps to (rs) • m = r • (s • m). Units use 1 • m = m. For three functors both
parenthesizations multiply the three scalars. These formulas give the coherence
assertions in moduliInverseImage_identity_composition below. -/
theorem fibredFppf_ringed_inverseImage
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D) (a : BasedFunctor D C) :
    ∃ (f : RingedToposMorphismOfUniverses
        (moduliModuleRings D hD) (moduliModuleRings C hC))
      (e : moduliTensorInverseImage hC hD a ≅ moduliModuleInverseImage hC hD a),
      f.inverse = moduliSetInverseImage hC hD a ∧
      (∀ (U : D.objᵒᵖ)
        (x : (f.inverse.obj ((sheafCompose (moduliFppfTopology C)
          (forget RingCat.{max (u + 1) v w})).obj (moduliModuleRings C hC))).obj.obj U),
        HEq (f.ringMap.hom.app U x) x) ∧
      Nonempty (moduliModuleInverseImage hC hD a ⊣ f.modules) ∧
      (moduliModuleInverseImage hC hD a).Additive ∧
      PreservesFiniteLimits (moduliModuleInverseImage hC hD a) ∧
      PreservesColimitsOfSize.{max (u + 1) v w, max (u + 1) v w}
        (moduliModuleInverseImage hC hD a) ∧
      (∃ z : (moduliModuleInverseImage hC hD a).obj
          (SheafOfModules.unit (moduliModuleRings C hC)) ≅
            SheafOfModules.unit (moduliModuleRings D hD),
        ∀ (U : D.objᵒᵖ) (r : ((moduliModuleRings C hC).obj.obj (a.toFunctor.op.obj U))),
          HEq (z.hom.val.app U r) r) ∧
      IsModuliTensorComparison hC hD a e := by
  sorry

/-- The module and tensor identifications respect identity and composition.
The comparison maps on precomposition modules are the identity on sections, hence
are unique; the tensor comparisons are induced by them and scalar multiplication.
Source: Stacks 06TL and 06WE
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
Proof: identity and successive restrictions evaluate as M(d) and M(a(b(e))).
Restrictions and maps are the original ones. Under the pure-tensor comparison
both composition maps send r ⊗ (s ⊗ m) to (rs) • m, and both unit maps send
1 ⊗ m to m. The module associativity and unit laws prove coherence, including
three-fold composition, after sheafification. -/
theorem moduliInverseImage_identity_composition
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (hE : IsFibredInGroupoids E) (a : BasedFunctor D C) (b : BasedFunctor E D) :
    (∃ i : moduliModuleInverseImage hC hC (BasedFunctor.id C) ≅ 𝟭 _,
      ∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (U : C.objᵒᵖ) (m : M.val.obj U), HEq ((i.hom.app M).val.app U m) m) ∧
    (∃ c : moduliModuleInverseImage hC hE (b.comp a) ≅
        moduliModuleInverseImage hC hD a ⋙ moduliModuleInverseImage hD hE b,
      ∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (U : E.objᵒᵖ) (m : M.val.obj (a.toFunctor.op.obj (b.toFunctor.op.obj U))),
        HEq ((c.hom.app M).val.app U m) m) := by
  sorry

/-- Canonical tensor comparisons, with their pure-tensor normalizations, commute with
identity and composition. The ordinary precomposition comparisons are normalized
by the identity on every section, so their associativity and unit coherence are fixed.
Source: Stacks 06TL, 06TW and 06WE
(blueprint: lem-sfb-fibred-fppf-ringed-inverse-image).
The tensor composition comparison is the canonical one of the tensor formula: it sends a
local pure tensor `r ⊗ m` to `r ⊗ (1 ⊗ m)`; the last equation is then the compatibility.
Proof: use the identity-on-sections comparisons of precomposition. Tensor comparison
is multiplication r ⊗ m ↦ r • m, with inverse m ↦ 1 ⊗ m. Define the tensor identity
and composition comparisons by these isomorphisms and the precomposition comparisons.
On iterated local tensors the two routes give r • (s • m) = (rs) • m. Thus they are
the canonical tensor comparisons. Pure tensors generate before sheafification, and
the universal property gives the two equations after sheafification. Naturality follows
from linearity. Threefold coherence follows from associativity and the normalized
identity-on-sections comparisons. -/
theorem moduliTensorInverseImage_identity_composition
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (hE : IsFibredInGroupoids E) (a : BasedFunctor D C) (b : BasedFunctor E D)
    (eI : moduliTensorInverseImage hC hC (BasedFunctor.id C) ≅
      moduliModuleInverseImage hC hC (BasedFunctor.id C))
    (eA : moduliTensorInverseImage hC hD a ≅ moduliModuleInverseImage hC hD a)
    (eB : moduliTensorInverseImage hD hE b ≅ moduliModuleInverseImage hD hE b)
    (eAB : moduliTensorInverseImage hC hE (b.comp a) ≅
      moduliModuleInverseImage hC hE (b.comp a))
    (heI : IsModuliTensorComparison hC hC (BasedFunctor.id C) eI)
    (heA : IsModuliTensorComparison hC hD a eA)
    (heB : IsModuliTensorComparison hD hE b eB)
    (heAB : IsModuliTensorComparison hC hE (b.comp a) eAB) :
    ∃ (i : moduliModuleInverseImage hC hC (BasedFunctor.id C) ≅ 𝟭 _)
      (c : moduliModuleInverseImage hC hE (b.comp a) ≅
        moduliModuleInverseImage hC hD a ⋙ moduliModuleInverseImage hD hE b)
      (iT : moduliTensorInverseImage hC hC (BasedFunctor.id C) ≅ 𝟭 _)
      (cT : moduliTensorInverseImage hC hE (b.comp a) ≅
        moduliTensorInverseImage hC hD a ⋙ moduliTensorInverseImage hD hE b),
      (∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (U : C.objᵒᵖ) (m : M.val.obj U), HEq ((i.hom.app M).val.app U m) m) ∧
      (∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (U : E.objᵒᵖ) (m : M.val.obj (a.toFunctor.op.obj (b.toFunctor.op.obj U))),
        HEq ((c.hom.app M).val.app U m) m) ∧
      (∀ (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC))
        (U : E.objᵒᵖ) (r : (moduliModuleRings E hE).obj.obj U)
        (m : M.val.obj (a.toFunctor.op.obj (b.toFunctor.op.obj U))),
        (cT.hom.app M).val.app U
          (siteSheafTensorTmul.{w, v, max (u + 1) v w, max (u + 1) v w}
            (A := moduliStructureSheaf E hE)
            (SheafOfModules.unit (moduliModuleRings E hE))
            ((moduliModuleInverseImage hC hE (b.comp a)).obj M) U r m) =
          siteSheafTensorTmul.{w, v, max (u + 1) v w, max (u + 1) v w}
            (A := moduliStructureSheaf E hE)
            (SheafOfModules.unit (moduliModuleRings E hE))
            ((moduliModuleInverseImage hD hE b).obj ((moduliTensorInverseImage hC hD a).obj M))
            U r
            (siteSheafTensorTmul.{w, v, max (u + 1) v w, max (u + 1) v w}
              (A := moduliStructureSheaf D hD)
              (SheafOfModules.unit (moduliModuleRings D hD))
              ((moduliModuleInverseImage hC hD a).obj M) (b.toFunctor.op.obj U)
              (1 : (moduliModuleRings D hD).obj.obj (b.toFunctor.op.obj U)) m)) ∧
      (∀ M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC),
        iT.hom.app M = eI.hom.app M ≫ i.hom.app M) ∧
      (∀ M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC),
        eAB.hom.app M ≫ c.hom.app M =
          cT.hom.app M ≫
            (moduliTensorInverseImage hD hE b).map (eA.hom.app M) ≫
              eB.hom.app ((moduliModuleInverseImage hC hD a).obj M)) := by
  sorry

end CategoryTheory
