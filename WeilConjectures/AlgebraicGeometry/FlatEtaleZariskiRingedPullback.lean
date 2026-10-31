/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZariskiEtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!
# Flat pullback from the small Zariski to the small étale ringed site

Source: Stacks Project, Descent, Tag 0GNA (lemma-compare-etale-zariski-flat),
Tag 070S (lemma-compare-sites, small étale case), and sites-modules.tex Tag 04JC
(blueprint: lem-fd-etale-zariski-ringed-pullback-flat).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Proofs enabling the canonical inverse image of commutative ring sheaves.
No ring, morphism, module or functor is chosen in this structure.
Source: Stacks 0GNA and 03FH (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
structure ZariskiEtaleCommRingContext (T : Scheme.{u}) where
  /-- Continuity of the canonical open-subscheme inclusion. -/
  continuous : (AlgebraicGeometry.gabberOpenEtale T).IsContinuous
    (Opens.grothendieckTopology T) T.smallEtaleTopology
  /-- Forgetting commutativity preserves sheaves on the small étale site. -/
  ringForget : T.smallEtaleTopology.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})
  /-- The commutative-ring direct image admits its inverse-image left adjoint. -/
  rightAdjoint : letI := continuous
    ((AlgebraicGeometry.gabberOpenEtale T).sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology T) T.smallEtaleTopology).IsRightAdjoint

/-- The inverse-image Zariski ring `epsilon_T⁻¹ O_T` on the small étale site.
Source: Stacks 0GNA (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
noncomputable def ZariskiEtaleCommRingContext.inverseRing {T : Scheme.{u}}
    (r : ZariskiEtaleCommRingContext T) : Sheaf T.smallEtaleTopology CommRingCat.{u} :=
  letI := r.continuous
  letI := r.rightAdjoint
  ((AlgebraicGeometry.gabberOpenEtale T).sheafPullback CommRingCat.{u}
    (Opens.grothendieckTopology T) T.smallEtaleTopology).obj T.sheaf

/-- The canonical structural map from the inverse-image Zariski ring. It is the adjoint
transpose of `T.restrictFunctorΓ.inv`, the commutative-ring form of
`zariskiEtaleOpenRingMap`; thus its data is fixed by the scheme restriction maps.
Source: Stacks 0GNA and 03FH (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
noncomputable def ZariskiEtaleCommRingContext.structureMap {T : Scheme.{u}}
    (r : ZariskiEtaleCommRingContext T) : r.inverseRing ⟶
      (⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩ :
        Sheaf T.smallEtaleTopology CommRingCat.{u}) :=
  letI := r.continuous
  letI := r.rightAdjoint
  (((AlgebraicGeometry.gabberOpenEtale T).sheafAdjunctionContinuous CommRingCat.{u}
    (Opens.grothendieckTopology T) T.smallEtaleTopology).homEquiv
      T.sheaf ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩).symm
        ⟨T.restrictFunctorΓ.inv⟩

/-- The inverse-image ring with commutativity forgotten.
Source: Stacks 0GNA (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
noncomputable def ZariskiEtaleCommRingContext.moduleRing {T : Scheme.{u}}
    (r : ZariskiEtaleCommRingContext T) : Sheaf T.smallEtaleTopology RingCat.{u} :=
  letI := r.ringForget
  (sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
    r.inverseRing

/-- The canonical structural map with commutativity forgotten.
Source: Stacks 0GNA (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
noncomputable def ZariskiEtaleCommRingContext.structureRingMap {T : Scheme.{u}}
    (r : ZariskiEtaleCommRingContext T) : r.moduleRing ⟶ smallEtaleModuleRing T :=
  letI := r.ringForget
  (sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).map r.structureMap

/-- The étale structure sheaf as a module over the inverse-image Zariski ring, obtained
by restricting its unit module along the canonical structural map.
Source: Stacks 0GNA (blueprint: lem-fd-etale-zariski-ringed-pullback-flat). -/
noncomputable def ZariskiEtaleCommRingContext.structureModule {T : Scheme.{u}}
    (r : ZariskiEtaleCommRingContext T) : SheafOfModules.{u} r.moduleRing :=
  (SheafOfModules.restrictScalars r.structureRingMap).obj
    (SheafOfModules.unit (smallEtaleModuleRing T))

/-- The canonical small étale inverse image of modules from the Zariski site is flat,
exact, additive, and computed by sheafified étale tensor sections.

Source: Stacks Project, Descent, Tag 0GNA (lemma-compare-etale-zariski-flat),
Tag 070S (lemma-compare-sites, small étale case), and sites-modules.tex Tag 04JC
(blueprint: lem-fd-etale-zariski-ringed-pullback-flat).

Proof, following the eight steps of the node:
1. The continuous open-subscheme inclusion and its finite-limit-preserving inverse image
   give the canonical ringed-topos morphism and the module extension `c.extension`.
2. On affine étale refinements the ring maps are étale, hence flat. Coverwise-flat
   sheafification proves `IsFlatOnSite` for `r.structureModule` over `r.inverseRing`.
   This is exactness of tensoring on all inverse-image-ring modules on the étale site.
   Composing with exact inverse image gives the separate exactness of `c.extension`.
3. The inverse image and sheaf tensor constructions preserve sums, so the extension is
   additive as recorded by `c.extension.Additive`.
4. For a Zariski module `M`, the presheaf `P.obj M` has sections
   `Γ(V,v^*M)` and the displayed restriction maps; `p` identifies it with the canonical
   tensor-section presheaf.
5. The sheafification isomorphism `e` identifies the canonical tensor extension with the
   sheafification of `P`, and its component equation is the tensor/open-section unit.
6. Naturality in module morphisms is the displayed equation for `p`; the scalar equation
   gives the prescribed tensor action on every étale object.
7. The construction applies to every module, including zero modules and the empty scheme;
   no quasi-coherence, separatedness, or finiteness hypothesis is used.
8. When `M` is quasi-coherent, the tensor-section presheaf is already a sheaf by étale
   descent, so the same identification is its associated étale module.
-/
theorem etale_zariski_ringed_pullback_flat (T : Scheme.{u}) :
    ∃ c : ZariskiEtaleModuleContext T,
      ∃ r : ZariskiEtaleCommRingContext T,
      @SheafOfModules.IsFlatOnSite.{u + 1, u, u, u} T.Etale inferInstance
        T.smallEtaleTopology r.ringForget inferInstance inferInstance
        r.inverseRing r.structureModule ∧
      exactFunctor T.Modules (SmallEtaleModules T) c.extension ∧
      c.extension.Additive ∧
      ∃ P : T.Modules ⥤
          _root_.PresheafOfModules.{u} (smallEtaleModuleRing T).obj,
        ∃ p : ∀ M : T.Modules,
            (P.obj M).presheaf ≅ etaleTensorSectionsPresheaf M,
          (∀ (M : T.Modules) (V : T.Etale)
              (r : Γ(V.left, ⊤)) (s : (P.obj M).obj (op V)),
            (p M).hom.app (op V) (r • s) =
              r • (@id (Γ((tensorPullback V.hom).obj M, ⊤))
                ((p M).hom.app (op V) s))) ∧
          (∀ (M N : T.Modules) (h : M ⟶ N) (V : T.Etale),
            ((_root_.PresheafOfModules.toPresheaf _).map (P.map h)).app (op V) ≫
                (p N).hom.app (op V) =
              (p M).hom.app (op V) ≫
                ((tensorPullback V.hom).map h).app ⊤) ∧
          ∃ e : c.extension ≅
              P ⋙ _root_.PresheafOfModules.sheafification
                (𝟙 (smallEtaleModuleRing T).obj),
            ∀ (M : T.Modules) (W : T.Opens) (s : Γ(M, W)),
              (e.hom.app M).val.app
                  (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                  (((c.adjunction.unit.app M).app W) s) =
                ((_root_.PresheafOfModules.sheafificationAdjunction
                    (𝟙 (smallEtaleModuleRing T).obj)).unit.app (P.obj M)).app
                  (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                  ((p M).inv.app
                    (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                    ((tensorOpenSectionIso T M W).inv s)) ∧
          (∀ (M : T.Modules) [M.IsQuasicoherent],
            IsIso ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (smallEtaleModuleRing T).obj)).unit.app (P.obj M))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
