/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.EtalePresentedLocalCokernels

/-! # Descent and gluing after local recovery

Source: Stacks Project, Descent, Tag 03DX, overlap and gluing paragraphs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Overlap lifts and an effective global module for specified local cokernels.
This stops before identifying the global module with open restriction.
Source: Stacks 03DX (blueprint: lem-trf-etale-presented-descent-gluing). -/
structure EtalePresentedDescentRecovery
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T) (I : Type w) (U : I → T.Etale)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G)
    (L : EtalePresentedLocalRecovery c T G I U K J d q) where
  /-- The unique overlap lifts; the two target section groups are canonically the same. -/
  overlap : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (_hf : f ≫ (U i).hom = W.hom) (_hg : g ≫ (U j).hom = W.hom),
    (tensorPullback f).obj (L.localModule i) ≅
      (tensorPullback g).obj (L.localModule j)
  overlap_image : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom) (A : W.left.Etale),
    ∀ s : Γ((tensorPullback A.hom).obj
      ((tensorPullback f).obj (L.localModule i)), ⊤),
      @presentedEtaleLocalMap T c G (U j) (L.localModule j) (L.localQC j)
        (L.localTensor j) (L.localIso j) W g _ hg A
        (((tensorPullback A.hom).map (overlap W i j f g hf hg).hom).app ⊤ s) =
      @presentedEtaleLocalMap T c G (U i) (L.localModule i) (L.localQC i)
        (L.localTensor i) (L.localIso i) W f _ hf A s
  overlap_unique : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom)
    (p : (tensorPullback f).obj (L.localModule i) ≅
      (tensorPullback g).obj (L.localModule j)),
    (∀ (A : W.left.Etale)
      (s : Γ((tensorPullback A.hom).obj ((tensorPullback f).obj (L.localModule i)), ⊤)),
      @presentedEtaleLocalMap T c G (U j) (L.localModule j) (L.localQC j)
        (L.localTensor j) (L.localIso j) W g _ hg A
        (((tensorPullback A.hom).map p.hom).app ⊤ s) =
      @presentedEtaleLocalMap T c G (U i) (L.localModule i) (L.localQC i)
        (L.localTensor i) (L.localIso i) W f _ hf A s) → p = overlap W i j f g hf hg
  cocycle : ∀ (W : T.Etale) (i j k : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) (h : W.left ⟶ (U k).left)
    [Etale f] [Etale g] [Etale h]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom)
    (hh : h ≫ (U k).hom = W.hom),
    overlap W i j f g hf hg ≪≫ overlap W j k g h hg hh = overlap W i k f h hf hh
  /-- The effective Zariski module and its specified descent identifications. -/
  globalModule : T.Modules
  globalQC : globalModule.IsQuasicoherent
  chartIso : ∀ i, (tensorPullback (U i).hom).obj globalModule ≅ L.localModule i
  effective : ∀ (W : T.Etale) (i j : I)
    (f : W.left ⟶ (U i).left) (g : W.left ⟶ (U j).left) [Etale f] [Etale g]
    (hf : f ≫ (U i).hom = W.hom) (hg : g ≫ (U j).hom = W.hom),
    (tensorPullback f).mapIso (chartIso i) ≪≫ overlap W i j f g hf hg =
      presentedTensorOverlap globalModule (U i) (U j) W f g hf hg ≪≫
        (tensorPullback g).mapIso (chartIso j)
  /-- Tensor coordinates for the global module. -/
  globalTensor : (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj
    ((c T).extension.obj globalModule) ≅ @etaleTensorSectionsSheaf T globalModule globalQC
  global_linear : ∀ (A : T.Etale) (r : Γ(A.left, ⊤))
    (s : ((c T).extension.obj globalModule).val.obj (op A)),
    globalTensor.hom.hom.app (op A) (r • s) =
      r • (@id (Γ((tensorPullback A.hom).obj globalModule, ⊤))
        (globalTensor.hom.hom.app (op A) s))
  global_unit : ∀ W : T.Opens,
    ((c T).adjunction.unit.app globalModule).app W ≫
      globalTensor.hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        (tensorOpenSectionIso T globalModule W).hom = 𝟙 _
  /-- The uniquely glued isomorphism, specified at every object over a cover member. -/
  gluedIso : (c T).extension.obj globalModule ≅ G
  glued_local : ∀ (i : I) (A : (U i).left.Etale),
    globalTensor.inv.hom.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) ≫
      ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map gluedIso.hom).hom.app
        (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) =
      ((tensorSectionsComp A.hom (U i).hom).inv.app globalModule).app ⊤ ≫
        ((tensorPullback A.hom).map (chartIso i).hom).app ⊤ ≫
          (L.localTensor i).inv.hom.app (op A) ≫
            ((SheafOfModules.toSheaf (smallEtaleModuleRing (U i).left)).map
              (L.localIso i).hom).hom.app (op A)
  glued_unique : ∀ b : (c T).extension.obj globalModule ⟶ G,
    (∀ (i : I) (A : (U i).left.Etale),
      b.val.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom))) =
        gluedIso.hom.val.app (op (Scheme.Etale.mk (A.hom ≫ (U i).hom)))) → b = gluedIso.hom

/-- Lift the overlap identifications, descend the local modules, and glue the
local extension comparisons. Source: Stacks Project, Descent, Tag 03DX,
overlap and gluing paragraphs (blueprint: lem-trf-etale-presented-descent-gluing).

Proof: Pullback preserves quasi-coherence. On every test overlap W, use the
normalized tensor-composition and localization comparisons to identify the two
extensions with G restricted to W. Full faithfulness lifts their comparison
uniquely. Lifting the reverse comparison and applying faithfulness proves the
inverse equations. The same faithfulness gives the cocycle because the three
comparisons with G cancel. Its repeated-index specialization normalizes the
diagonal. The jointly surjective étale family is an fpqc family, even when
individual members are not quasi-compact. Apply effective fpqc descent to the
resulting quasi-coherent descent datum. Its chart identifications satisfy the
specified overlap equation on every test overlap, by full faithfulness.
Give the descended global module its normalized tensor coordinates. The local
maps obtained from chartIso and localIso agree on overlaps by effectivity and
the overlap-image equation. The sheaf Hom gluing theorem gives a unique global
map. Glue the inverse local maps too; uniqueness makes both composites
identities. The local equation in tensor coordinates is precisely this gluing
condition, and separatedness proves glued_unique. Neither identification with
open restriction nor invertibility or normalization of the counit is used. -/
theorem etalePresented_descentGluing
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T)
    (I : Type w) (U : I → T.Etale)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G)
    (cover : ∀ x : T, ∃ (i : I) (y : (U i).left), (U i).hom.base y = x)
    (L : EtalePresentedLocalRecovery c T G I U K J d q) :
    Nonempty (EtalePresentedDescentRecovery c T G I U K J d q L) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
