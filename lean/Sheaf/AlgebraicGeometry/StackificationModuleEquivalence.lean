module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.CategoryTheory.SiteStackification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Sheaf.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings

/-! # Module sheaves and quasi-coherence under stackification

Source: Stacks Project, stacks-sheaves.tex, Tags 06WQ (lemma-stackification) and
06WR (lemma-stackification-quasi-coherent)
(blueprint: lem-sfb-stackification-module-equivalence).

Both total categories are taken in the common bound of the small-site convention.
The ring universes are the ambient universes already used by `moduliModuleRings`.
Restriction is specified on presheaves of modules, so its objects, restriction maps,
scalar actions and all module morphisms are fixed, rather than merely its equivalence class.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory

/-- Precomposition on module presheaves, using the identical regular-function rings.
The equality `q.w` identifies the underlying scheme functors; `eqToHom` therefore
uses the identity of regular functions on each corresponding scheme, including the
canonical ULift already built into the recorded structure sheaf.

Source: Stacks Project, stacks-sheaves.tex, Tag 06WR, equality of structure sheaves
(blueprint: lem-sfb-stackification-module-equivalence). -/
noncomputable def moduliModuleRestrictionPresheaf
    {S : AlgebraicGeometry.Scheme.{u}}
    {P A : BasedCategory.{v, w} (Over S)}
    (q : BasedFunctor P A) (hP : IsFibredInGroupoids P) (hA : IsFibredInGroupoids A) :
    PresheafOfModules.{max (u + 1) v w} (moduliModuleRings A hA).obj ⥤
      PresheafOfModules.{max (u + 1) v w} (moduliModuleRings P hP).obj :=
  PresheafOfModules.pushforward (F := q.toFunctor)
    (eqToHom (congrArg (β := P.objᵒᵖ ⥤ RingCat.{max (u + 1) v w})
      (fun p : P.obj ⥤ Over S ↦
      (moduliStructurePresheaf.{u, v, w}
        (BasedCategory.ofFunctor p : BasedCategory.{v, w} (Over S)) :
          P.objᵒᵖ ⥤ CommRingCat.{max (u + 1) v w}) ⋙
        forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})
      q.w.symm))

/-- Stackification preserves the entire category of module sheaves and detects
quasi-coherence. Both equivalences have the same precomposition functor, as specified
by the equalities after the faithful forgetful functor and the full inclusions.
In particular the section over `x` is the original section over `q.obj x`, with the
identity identification of regular-function rings. No algebraicity is assumed.

Source: Stacks Project, stacks-sheaves.tex, Tags 06WQ and 06WR
(blueprint: lem-sfb-stackification-module-equivalence).

Proof:
1. Use lem-sfb-fibred-site-functor-continuity for continuity, cocontinuity and lifting
   coverings of qx to coverings of x on the inherited fppf sites.
2. Use lem-sfb-groupoid-stackification-local-description: arrow presheaves sheafify,
   and every target object is locally in the image. Cartesian lifting reduces arrows
   over a fixed base arrow to fibre isomorphisms. The sheafification unit is locally
   bijective by lem-cbc-set-presheaf-sheafification-local-bijection, giving local
   fullness and faithfulness. These are the remaining special-cocontinuity conditions
   of def-weil-pbc-special-cocontinuous-functor; use def-weil-pbc-sheafification.
3. Apply lem-weil-pbc-special-cocontinuous-sheaf-equivalence to set sheaves. Lift the
   group-object structure by full faithfulness, using
   lem-weil-pbc-sheaf-algebraic-structures-abelian-component and preservation of finite
   products by lem-galois-equivalence-preserves-limits. The group laws and maps are
   detected by faithfulness, giving the abelian-sheaf equivalence by
   lem-trf-fully-faithful-ess-surj-equivalence.
4. The regular-function rings and pullbacks coincide by
   def-sfb-stack-quasi-coherent-algebra. Apply
   lem-weil-pbc-dense-subsite-module-restriction to obtain the module equivalence
   with precisely the precomposition functor displayed below.
5. Cartesian lifting identifies each slice P/x and A/qx with the scheme slice over
   the scheme underlying x; the unique cartesian factorization gives full
   faithfulness, and lifting gives essential surjectivity. Thus q on slices is an
   equivalence preserving and reflecting the fppf coverings and restricted rings.
6. Use lem-weil-pbc-site-equivalence-sheaf-transport and
   lem-weil-pbc-dense-subsite-module-restriction on these slices. Restriction commutes
   with the global module functor. These additive equivalences carry the structure
   sheaf to itself and preserve coproducts, kernels and cokernels by
   lem-galois-equivalence-preserves-limits, hence preserve and reflect arbitrary
   small free presentations, in def-trf-space-quasi-coherent-module.
7. A local free presentation of a target module pulls back to one on the source:
   lift its covering by step 1 and transfer the presentation by step 6.
8. Conversely cover a target object by images using the local essential-image
   property, and then cover each source object by its presentation charts. Step 6
   transfers those presentations to the target slices. Transitivity gives a cover
   of the target object, proving quasi-coherence. Full faithfulness and essential
   surjectivity now restrict to the full quasi-coherent subcategories. All module
   morphisms are retained, as in def-weil-sheaf-of-modules-category. -/
theorem stackification_module_equivalence
    {S : AlgebraicGeometry.Scheme.{u}}
    {P A : BasedCategory.{v, w} (Over S)}
    (q : BasedFunctor P A) (hq : IsFppfStackification q) :
    ∃ e : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings A hq.2.1.1) ≌
        ringedSiteModules.{max (u + 1) v w} (moduliModuleRings P hq.1),
      e.functor ⋙ SheafOfModules.forget (moduliModuleRings P hq.1) =
        SheafOfModules.forget (moduliModuleRings A hq.2.1.1) ⋙
          moduliModuleRestrictionPresheaf q hq.1 hq.2.1.1 ∧
      (∀ M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings A hq.2.1.1),
        SheafOfModules.IsQuasicoherent M ↔ SheafOfModules.IsQuasicoherent (e.functor.obj M)) ∧
      ∃ eQC : (SheafOfModules.isQuasicoherent (moduliModuleRings A hq.2.1.1)).FullSubcategory ≌
          (SheafOfModules.isQuasicoherent (moduliModuleRings P hq.1)).FullSubcategory,
        eQC.functor ⋙ (SheafOfModules.isQuasicoherent (moduliModuleRings P hq.1)).ι =
          (SheafOfModules.isQuasicoherent (moduliModuleRings A hq.2.1.1)).ι ⋙ e.functor := by
  sorry

end CategoryTheory
