module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import WeilConjectures.AlgebraicGeometry.CompletionInternalHom
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Internal Hom and coherent completion on algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tags 08B6 and 08B9
(blueprint: lem-sfb-space-completion-internal-hom).

Internal Hom is the existing local-linear-map sheaf on the equivalent small affine
site, transported back by the existing ringed-site equivalence. This retains the
original section universe. Positive level n+1 is indexed by op n.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The existing internal Hom, transported from the equivalent small affine site.
Source: Stacks 08B6 and the affine-basis comparison 039Z
(blueprint: lem-sfb-space-completion-internal-hom). -/
def completionInternalHom (F G : X.Modules) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj
    (SheafOfModules.homObj (R := X.smallStructureSheaf)
      (X.smallModuleRestriction.obj F) (X.smallModuleRestriction.obj G))

/-- Precomposition and postcomposition on that same internal Hom.
Source: Stacks 08B6, naturality of local module maps
(blueprint: lem-sfb-space-completion-internal-hom). -/
def completionInternalHomMap {F F' G G' : X.Modules} (a : F' ⟶ F) (b : G ⟶ G') :
    completionInternalHom F G ⟶ completionInternalHom F' G' :=
  X.smallModuleEquivalence.inverse.map
    (SheafOfModules.homObjMap (R := X.smallStructureSheaf)
      (X.smallModuleRestriction.map a) (X.smallModuleRestriction.map b))

/-- A global internal-Hom section gives the corresponding global module morphism.
Restriction and the equivalence counit identify it with the existing Hom section.
Source: Stacks 08B6, the identification of global Hom sections
(blueprint: lem-sfb-space-completion-internal-hom). -/
def completionInternalHomSection (F G : X.Modules)
    (s : (completionInternalHom F G).sections) : F ⟶ G :=
  X.smallModuleRestriction.preimage
    (SheafOfModules.homObjSectionsEquiv (R := X.smallStructureSheaf)
      (X.smallModuleRestriction.obj F) (X.smallModuleRestriction.obj G)
      (SheafOfModules.sectionsMap
        (X.smallModuleEquivalence.counitIso.hom.app
          (SheafOfModules.homObj (R := X.smallStructureSheaf)
            (X.smallModuleRestriction.obj F) (X.smallModuleRestriction.obj G)))
        (PresheafOfModules.sectionsMk
          (fun T ↦ s.val (X.smallEtaleInclusion.op.obj T))
          (fun _ _ f ↦ s.property (X.smallEtaleInclusion.op.map f)))))

/-- The inverse limit of the global sections of the ordinary sheaf quotients.
This uses compatible families on all objects, without a terminal scheme chart.
Source: Stacks 08B6 (blueprint: lem-sfb-space-completion-internal-hom). -/
abbrev completedModuleSections (J : QuasiCoherentIdeal X) (M : X.Modules) :
    Type (u + 1) :=
  (((coherentAdicCompletionDiagram J).obj M) ⋙
    SheafOfModules.sectionsFunctor (R := X.structureSheaf)).sections

/-- Functoriality of that limit, from the already fixed quotient functor.
Source: Stacks 08B6, naturality
(blueprint: lem-sfb-space-completion-internal-hom). -/
def completedModuleSectionsMap (J : QuasiCoherentIdeal X) {M N : X.Modules}
    (f : M ⟶ N) : completedModuleSections J M → completedModuleSections J N :=
  (Functor.sectionsFunctor ℕᵒᵖ).map
    (Functor.whiskerRight ((coherentAdicCompletionDiagram J).map f)
      (SheafOfModules.sectionsFunctor (R := X.structureSheaf)))

/-- Internal Hom is coherent with the asserted geometric support, and its completed
sections canonically compute compatible morphisms between coherent completions.
The factorization equation specifies reduction of local linear maps through both
quotients. The component equation specifies the bijection; the final equations express
naturality in both inputs and compatibility with reduction of global morphisms.

Source: Stacks Project, More on Morphisms of Spaces, Tags 08B6 and 08B9
(blueprint: lem-sfb-space-completion-internal-hom).

Proof (the node's seven steps):
1. On an etale scheme chart use the Zariski/etale quasi-coherent equivalence
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). Coherent source modules
   are locally finitely presented (lem-weil-pbc-coherent-local-finite-presentation).
   The scheme internal Hom is coherent (lem-weil-pbc-coherent-sheaf-hom-coherent).
   The local Hom comparison (lem-sfb-scheme-etale-tensor-hom-comparison) identifies
   it with the restriction of the same local-linear-map sheaf. These presentations
   prove quasi-coherence, and coherence on every chart, of the transported Hom.
2. Finitely presented stalk Hom is Hom of the stalks
   (lem-weil-pbc-stalk-internal-hom-finite-presentation). It vanishes if either input
   stalk vanishes. Apply lem-sfb-space-etale-chart-support and a surjective affine
   refinement of an etale atlas to get the geometric-support containment.
3. Postcompose local maps with G to G/J^n G. This kills J^n Hom(F,G), and every map
   F to G/J^n G kills J^n F. The two cokernel properties uniquely give e_n, satisfying
   the factorization equation. Uniqueness makes these maps commute with restriction
   and reduction. Thus their global sections define Phi on compatible families.
4. On each affine etale chart the exact comparison
   (lem-sfb-scheme-etale-module-exact-finiteness-comparison) and tensor/Hom comparison
   identify powers, products and quotients with the scheme ones. Products are images
   of tensor multiplication, and the quasi-coherent tensor/image/cokernel lemmas
   (lem-weil-pbc-quasi-coherent-tensor-product-affine-sections and
   lem-weil-pbc-quasi-coherent-module-cokernel-image) ensure comparison applies.
   The chart is Noetherian since it is affine and locally Noetherian. Full faithfulness
   identifies the local map with lem-weil-pbc-completion-internal-hom, exchanging its
   two arguments. Thus the local map is bijective.
5. If two families have the same image, local injectivity on every affine chart
   makes their sections equal there. The sheaf condition makes them globally equal.
6. Given a system morphism, take its unique inverse family on every affine chart.
   The overlap of two charts is a scheme
   (lem-trf-space-representable-etale-scheme-tests). Cover it by affine opens; these
   are locally Noetherian and affine, hence Noetherian. Uniqueness of the local inverse
   makes the families agree on these opens. Glue each level by the sheaf condition.
   Transition compatibility and equality with the given system morphism hold locally,
   hence globally. This proves surjectivity without a terminal scheme chart.
7. A reduced section representing u acts by xbar to u(x)bar, proving normalization.
   Precomposition by a and postcomposition by b act by xbar to b(v(a(x)))bar.
   Thus the naturality square commutes on local lifts, hence as sheaf maps because
   quotient projections are epimorphisms. It commutes on global compatible families.
   The small affine-site equivalence preserves all these constructions and equations. -/
theorem space_completion_internal_hom
    (J : QuasiCoherentIdeal X)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X) :
    (∀ (F G : X.Modules),
      (F.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj F)) →
      (G.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj G)) →
      (completionInternalHom F G).IsQuasicoherent ∧
      (∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj (completionInternalHom F G))) ∧
      moduleSupport (completionInternalHom F G) ⊆ moduleSupport F ∩ moduleSupport G) ∧
    ∃ e : ∀ (F G : X.Modules) (n : ℕ),
      ((adicQuotientModel J).diagram.obj (completionInternalHom F G)).obj (op n) ⟶
        completionInternalHom (((adicQuotientModel J).diagram.obj F).obj (op n))
          (((adicQuotientModel J).diagram.obj G).obj (op n)),
      (∀ (F G : X.Modules) (n : ℕ),
        (adicQuotientModel J).projection (completionInternalHom F G) n ≫ e F G n ≫
          completionInternalHomMap ((adicQuotientModel J).projection F n)
            (𝟙 (((adicQuotientModel J).diagram.obj G).obj (op n))) =
        completionInternalHomMap (𝟙 F) ((adicQuotientModel J).projection G n)) ∧
      ∃ Φ : ∀ F G : ObjectProperty.FullSubcategory (C := X.Modules)
          (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
            RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
              ((X.schemeRestriction T).obj M)),
        completedModuleSections J (completionInternalHom F.obj G.obj) ≃
          ((coherentAdicCompletion J hln hqc hqs).obj F ⟶
            (coherentAdicCompletion J hln hqc hqs).obj G),
        (∀ F G s n, (Φ F G s).hom.app n =
          completionInternalHomSection _ _
            (SheafOfModules.sectionsMap (e F.obj G.obj n.unop) (s.val n))) ∧
        (∀ (F F' G G' : ObjectProperty.FullSubcategory (C := X.Modules)
            (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
              RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
                ((X.schemeRestriction T).obj M)))
          (a : F' ⟶ F) (b : G ⟶ G') s,
          Φ F' G' (completedModuleSectionsMap J
            (completionInternalHomMap a.hom b.hom) s) =
          (coherentAdicCompletion J hln hqc hqs).map a ≫ Φ F G s ≫
            (coherentAdicCompletion J hln hqc hqs).map b) ∧
        (∀ (F G : ObjectProperty.FullSubcategory (C := X.Modules)
            (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
              RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
                ((X.schemeRestriction T).obj M)))
          (s : (completionInternalHom F.obj G.obj).sections)
          (t : completedModuleSections J (completionInternalHom F.obj G.obj)),
          (∀ n : ℕᵒᵖ, t.val n = SheafOfModules.sectionsMap
            ((adicQuotientModel J).projection (completionInternalHom F.obj G.obj) n.unop) s) →
          Φ F G t =
            (coherentAdicCompletion J hln hqc hqs).map
              (ObjectProperty.homMk (completionInternalHomSection F.obj G.obj s))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
