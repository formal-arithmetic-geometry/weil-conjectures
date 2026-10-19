/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule

/-!
# Quasi-coherent modules on the Zariski and small étale sites

Source: Stacks Project, Descent, Tags 03FH, 03DX, 03LC, 05VG and 0GN7
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The ring-valued presheaf of regular functions on the small étale site.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ RingCat.{u} :=
  X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- Regular functions form a ring sheaf on the small étale site.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: the underlying set presheaf is the regular-function sheaf by étale descent
(upstream isSheaf_etaleStructurePresheaf). Compatible ring homomorphisms glue pointwise;
the sheaf separatedness identities show that the glued map preserves every ring operation.
This proves the ring-valued sheaf condition without any enlargement of section rings. -/
theorem smallEtaleModulePresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology (smallEtaleModulePresheaf X) := by
  sorry

/-- The usual structure sheaf on the small étale site, with its actual section rings.
Source: Stacks 03DU (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleRing (X : Scheme.{u}) : Sheaf X.smallEtaleTopology RingCat.{u} :=
  ⟨smallEtaleModulePresheaf X, smallEtaleModulePresheaf_isSheaf X⟩

/-- Modules over the usual small étale structure sheaf.
Source: Stacks 03DX (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
abbrev SmallEtaleModules (X : Scheme.{u}) := SheafOfModules.{u} (smallEtaleModuleRing X)

/-- The structural map identifies functions on an open with functions on its open subscheme.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleOpenRingMap (X : Scheme.{u})
    [hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology] :
    X.ringCatSheaf ⟶ ((AlgebraicGeometry.gabberOpenEtale X).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) X.smallEtaleTopology).obj (smallEtaleModuleRing X) :=
  ⟨Functor.whiskerRight X.restrictFunctorΓ.inv (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-- Restriction to Zariski opens, including restriction of scalars by the canonical ring map.
Source: Stacks 0GN7 (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleRestriction (X : Scheme.{u})
    [hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology] : SmallEtaleModules X ⥤ X.Modules :=
  SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)

/-- The ring map for an arbitrary scheme morphism is pullback of regular functions.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleRingMap {U T : Scheme.{u}} (a : U ⟶ T) :
    smallEtaleModuleRing T ⟶ (a.Etale.sheafPushforwardContinuous RingCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).obj (smallEtaleModuleRing U) :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToPullback a) (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-- Direct image of small étale modules uses the scheme base-change functor on the sites.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePushforward {U T : Scheme.{u}} (a : U ⟶ T) :
    SmallEtaleModules U ⥤ SmallEtaleModules T :=
  SheafOfModules.pushforward (smallEtaleModuleRingMap a)

/-- The canonical ringed-site tensor pullback, left adjoint to restriction.
It represents O_et tensor over epsilon^{-1} O_Zar with epsilon^{-1} M;
Mathlib constructs this functor by module-presheaf pullback and sheafification.
Only the proof that the right adjoint exists is an argument.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleExtension (X : Scheme.{u})
    (hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology)
    (hp : (@zariskiEtaleModuleRestriction X hc).IsRightAdjoint) :
    X.Modules ⥤ SmallEtaleModules X :=
  letI := hc
  letI : (SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)).IsRightAdjoint := hp
  SheafOfModules.pullback (zariskiEtaleOpenRingMap X)

/-- The canonical tensor-extension/restriction adjunction, with its specified unit and counit.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtaleModuleAdjunction (X : Scheme.{u})
    (hc : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
      (Opens.grothendieckTopology X) X.smallEtaleTopology)
    (hp : (@zariskiEtaleModuleRestriction X hc).IsRightAdjoint) :
    zariskiEtaleModuleExtension X hc hp ⊣ @zariskiEtaleModuleRestriction X hc :=
  letI := hc
  letI : (SheafOfModules.pushforward (zariskiEtaleOpenRingMap X)).IsRightAdjoint := hp
  SheafOfModules.pullbackPushforwardAdjunction (zariskiEtaleOpenRingMap X)

/-- Tensor pullback along an arbitrary morphism of small étale ringed topoi.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModulePullback {U T : Scheme.{u}} (a : U ⟶ T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint) :
    SmallEtaleModules T ⥤ SmallEtaleModules U :=
  letI : (SheafOfModules.pushforward (smallEtaleModuleRingMap a)).IsRightAdjoint := hp
  SheafOfModules.pullback (smallEtaleModuleRingMap a)

/-- The tensor-pullback/direct-image adjunction on the small étale ringed topoi.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def smallEtaleModuleAdjunction {U T : Scheme.{u}} (a : U ⟶ T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint) :
    smallEtaleModulePullback a hp ⊣ smallEtaleModulePushforward a :=
  letI : (SheafOfModules.pushforward (smallEtaleModuleRingMap a)).IsRightAdjoint := hp
  SheafOfModules.pullbackPushforwardAdjunction (smallEtaleModuleRingMap a)

/-- Proof data permitting the canonical module pullback on these presented sites.
There is no chosen ring, module, map or functor in this structure.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
structure ZariskiEtaleModuleContext (X : Scheme.{u}) where
  /-- The inclusion of open subschemes is continuous. -/
  continuous : (AlgebraicGeometry.gabberOpenEtale X).IsContinuous
    (Opens.grothendieckTopology X) X.smallEtaleTopology
  /-- Restriction of modules admits its canonical tensor left adjoint. -/
  rightAdjoint : (@zariskiEtaleModuleRestriction X continuous).IsRightAdjoint

/-- Canonical restriction, with the continuity proof supplied by the context.
Source: Stacks 0GN7 (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.restriction {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :=
  @zariskiEtaleModuleRestriction X c.continuous

/-- Canonical tensor extension for the presented sites.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.extension {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :=
  zariskiEtaleModuleExtension X c.continuous c.rightAdjoint

/-- The canonical extension/restriction adjunction.
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def ZariskiEtaleModuleContext.adjunction {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :
    c.extension ⊣ c.restriction :=
  zariskiEtaleModuleAdjunction X c.continuous c.rightAdjoint

/-- The canonical pullback comparison is the left-adjoint mate of the open-restriction
comparison for direct images. Its direction is (a^* F)_et to a_et^*(F_et).
Source: Stacks 03FH (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtalePullbackComparison {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a) :
    tensorPullback a ⋙ cU.extension ≅ cT.extension ⋙ smallEtaleModulePullback a hp :=
  ((conjugateIsoEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction a)).comp cU.adjunction)
    (cT.adjunction.comp (smallEtaleModuleAdjunction a hp))).symm r.symm).symm

/-- The canonical direct-image comparison, defined as the counit mate of the canonical
pullback comparison. No quasi-coherence or quasi-compactness is needed to define this map.
Source: Stacks 03LC (blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). -/
def zariskiEtalePushforwardComparison {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a)
    (H : U.Modules) :
    cT.extension.obj ((pushforward a).obj H) ⟶
      (smallEtaleModulePushforward a).obj (cU.extension.obj H) :=
  (smallEtaleModuleAdjunction a hp).unit.app (cT.extension.obj ((pushforward a).obj H)) ≫
    (smallEtaleModulePushforward a).map
      ((zariskiEtalePullbackComparison a cU cT hp r).inv.app ((pushforward a).obj H) ≫
        cU.extension.map ((Classical.choose (exists_tensorPullbackAdjunction a)).counit.app H))

/-- Additive sheafification on the slices of the original small étale site, retaining
u-small section groups despite the u+1 object universe of the presented site.
Source: Stacks, Sites, sheafification and the affine étale basis; Descent 03DX
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: refine each étale object by its affine opens. Affine étale schemes of finite
presentation over each affine base have a u-small skeleton: they are specified by
finite polynomial presentations over a u-small ring. Their finite jointly surjective
coverings form a basis. Apply the ordinary plus construction twice on this small basis,
then extend by compatible sections on affine covers. All products are indexed by
u-small sets; the result therefore still has u-small additive section groups. Its
usual gluing universal property is precisely the sheafification adjunction on the
slice site. The construction is invariant under changing the affine cover. -/
@[instance] theorem smallEtaleModuleOverHasWeakSheafify (T : Scheme.{u}) (V : T.Etale) :
    HasWeakSheafify (T.smallEtaleTopology.over V) AddCommGrpCat.{u} := by
  sorry

/-- Sheafification inverts exactly the locally bijective additive maps on these slices.
Source: Stacks, Sites, sheafification; Descent 03DX
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).
Proof: on the affine étale basis used by smallEtaleModuleOverHasWeakSheafify, the two
plus constructions identify sections exactly when they agree locally and every section
is locally represented. Hence a locally bijective map sheafifies to an isomorphism.
Conversely the sheafification units are locally bijective, so a sheafified isomorphism
forces local injectivity and surjectivity of the original map by the same local
representatives. Refinement transfers this equivalence to the full slice site. -/
@[instance] theorem smallEtaleModuleOverWEqualsLocallyBijective
    (T : Scheme.{u}) (V : T.Etale) :
    (T.smallEtaleTopology.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- Zariski and small étale quasi-coherent modules agree, with the canonical functors,
open-section normalizations, line modules, and pullback/direct-image comparisons.
Source: Stacks Project, Descent, Tags 03FH, 03DX(2), 03LC(1),(3), 05VG and 0GN7
(blueprint: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence).

The first two clauses say that tensor extension and open restriction preserve the
quasi-coherent full subcategories and that their adjunction unit and counit are
isomorphisms there. This is the adjoint-equivalence formulation, with restriction as
its specified inverse. The family e identifies the extension with the recorded
associated sheaf, including the scalar action and every module map. The next two
equations say the unit and counit are identity maps in the ordinary open-section
coordinates. The local-unit condition is precisely the definition of a line module.
The direct-image comparison r is specified on every open, so its left-adjoint mate
is the canonical tensor-pullback comparison. The final clauses assert that its
counit mate is an isomorphism for quasi-compact separated morphisms, preserves
quasi-coherence on both sides, is natural in the module, and is identity on open sections.

Proof, following the ten steps of the DAG:
1. Use lem-trf-zariski-etale-tensor-sections to identify the canonical tensor
   extension with sheafified tensor sections and restriction with evaluation on opens.
   Quasi-coherent descent removes sheafification. The module adjunction makes extension
   preserve coproducts and cokernels, and identifies its value on the unit ring.
2. Normalized tensor-pullback composition identifies restriction to an étale scheme V
   with extension of the pulled-back Zariski module; pullback preserves quasi-coherence.
3. On affine opens, the tilde/Gamma adjunction presents each module as a cokernel of
   free modules. Extension preserves that presentation, proving site quasi-coherence.
4. Evaluation on opens identifies the unit with identity; the adjunction therefore
   proves full faithfulness on quasi-coherent modules.
5. Present a site quasi-coherent module locally by free modules. Full faithfulness
   lifts its presentation map; the Zariski cokernel is quasi-coherent and extends back.
6. On double overlaps lift the comparison isomorphisms uniquely by full faithfulness.
   Faithfulness gives the cocycle identities on triple overlaps, including repeated
   indices. Étale coverings are fpqc, so fpqc descent makes these modules effective.
7. Glue the local extension isomorphisms by the sheaf equalizer. Restriction is the
   inverse; the triangle identity makes the counit identity on open sections too.
8. The two composites of direct images agree on opens. Take their unit-normalized
   left-adjoint mate to obtain the displayed canonical pullback comparison for every a.
9. Zariski rank-one trivializations extend to étale ones. Conversely a line module is
   quasi-coherent; its local trivializations descend by fpqc descent of rank one.
10. For quasi-compact separated a, quasi-separatedness gives quasi-coherent Zariski
    pushforward. Flat base change along each étale V identifies its tensor sections
    with sections on U times_T V, hence with small étale pushforward. The maps are
    the counit mates above and commute with restrictions and module maps. On an open
    they are the identity. The étale pushforward is consequently quasi-coherent too. -/
theorem scheme_zariski_etale_quasiCoherent_equivalence :
    ∃ c : ∀ T : Scheme.{u}, ZariskiEtaleModuleContext T,
      (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
        ((c T).extension.obj F).IsQuasicoherent ∧
          IsIso ((c T).adjunction.unit.app F)) ∧
      (∀ (T : Scheme.{u}) (G : SmallEtaleModules T) [G.IsQuasicoherent],
        ((c T).restriction.obj G).IsQuasicoherent ∧
          IsIso ((c T).adjunction.counit.app G)) ∧
      ∃ e : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
          (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj ((c T).extension.obj F) ≅
            etaleTensorSectionsSheaf F,
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
            (V : T.Etale) (r : Γ(V.left, ⊤))
            (s : ((c T).extension.obj F).val.obj (op V)),
          (e T F).hom.hom.app (op V) (r • s) =
            r • (@id (Γ((tensorPullback V.hom).obj F, ⊤))
              ((e T F).hom.hom.app (op V) s))) ∧
        (∀ (T : Scheme.{u}) (F H : T.Modules) [F.IsQuasicoherent] [H.IsQuasicoherent]
            (f : F ⟶ H) (V : T.Etale),
          ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
            ((c T).extension.map f)).hom.app (op V) ≫ (e T H).hom.hom.app (op V) =
              (e T F).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map f).app ⊤) ∧
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] (W : T.Opens),
          ((c T).adjunction.unit.app F).app W ≫
              (e T F).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
                (tensorOpenSectionIso T F W).hom = 𝟙 _) ∧
        (∀ (T : Scheme.{u}) (G : SmallEtaleModules T) [G.IsQuasicoherent]
            (h : ((c T).restriction.obj G).IsQuasicoherent) (W : T.Opens),
          (tensorOpenSectionIso T ((c T).restriction.obj G) W).inv ≫
              (@e T ((c T).restriction.obj G) h).inv.hom.app
                (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
              ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
                ((c T).adjunction.counit.app G)).hom.app
                  (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) = 𝟙 _) ∧
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
          F.IsInvertible ↔ ∀ V : T.Etale, ∃ S : Sieve V,
            S ∈ T.smallEtaleTopology V ∧
              ∀ (W : T.Etale) (f : W ⟶ V), S f →
                Nonempty (((c T).extension.obj F).over W ≅
                  SheafOfModules.unit ((smallEtaleModuleRing T).over W))) ∧
        (∀ (T : Scheme.{u}) (G : SmallEtaleModules T),
          (∀ V : T.Etale, ∃ S : Sieve V,
            S ∈ T.smallEtaleTopology V ∧
              ∀ (W : T.Etale) (f : W ⟶ V), S f →
                Nonempty (G.over W ≅ SheafOfModules.unit ((smallEtaleModuleRing T).over W))) →
            G.IsQuasicoherent ∧ ((c T).restriction.obj G).IsInvertible) ∧
        ∀ (U T : Scheme.{u}) (a : U ⟶ T),
          ∃ (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
            (r : smallEtaleModulePushforward a ⋙ (c T).restriction ≅
              (c U).restriction ⋙ pushforward a),
            (∀ (G : SmallEtaleModules U) (W : T.Opens),
              (r.hom.app G).app W =
                G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op) ∧
            ∀ (_ : QuasiCompact a) (_ : IsSeparated a),
              (∀ (H : U.Modules) [H.IsQuasicoherent],
                ((pushforward a).obj H).IsQuasicoherent ∧
                  ((smallEtaleModulePushforward a).obj ((c U).extension.obj H)).IsQuasicoherent ∧
                  IsIso (zariskiEtalePushforwardComparison a (c U) (c T) hp r H)) ∧
              (∀ (H K : U.Modules) [H.IsQuasicoherent] [K.IsQuasicoherent] (f : H ⟶ K),
                (c T).extension.map ((pushforward a).map f) ≫
                    zariskiEtalePushforwardComparison a (c U) (c T) hp r K =
                  zariskiEtalePushforwardComparison a (c U) (c T) hp r H ≫
                    (smallEtaleModulePushforward a).map ((c U).extension.map f)) ∧
              ∀ (H : U.Modules) [H.IsQuasicoherent],
                (c T).adjunction.unit.app ((pushforward a).obj H) ≫
                    (c T).restriction.map
                      (zariskiEtalePushforwardComparison a (c U) (c T) hp r H) ≫
                    r.hom.app ((c U).extension.obj H) =
                  (pushforward a).map ((c U).adjunction.unit.app H) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
