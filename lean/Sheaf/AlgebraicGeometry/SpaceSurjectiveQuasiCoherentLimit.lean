module

public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.RightDerived

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Limits.HasLimits

import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.SmallEtaleQuasiCoherentKernel
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-! # Surjective inverse limits of quasi-coherent algebraic-space modules

Source: Stacks Project, spaces-perfect.tex, Tag 0D3E (2),(3), its affine-etale proof
and preceding warning; sites-cohomology.tex, Tag 0BKY
(blueprint: lem-sfb-space-surjective-qcoh-limit).

The original modules and their sectionwise limit are retained. The fixed small-model
restriction equivalence realizes the size convention for derived module categories.
Cohomology below is exactly right-derived evaluation, transported through that equivalence.
The comparison is the ordinary-limit comparison followed by the derived functor's unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wA wT

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Evaluation of an original-site module, expressed on the fixed small ringed model.
Source: Stacks, Cohomology on Sites, Section 01FT; Tag 039Z
(blueprint: lem-sfb-space-surjective-qcoh-limit).
This is the existing section functor composed with the inverse restriction equivalence. -/
abbrev smallEtaleModuleSections {S : Scheme.{u}} (X : AlgebraicSpace S) (U : X.EtaleSite) :
    X.SmallModules ⥤ AddCommGrpCat.{u} :=
  X.smallModuleEquivalence.inverse ⋙ SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.etaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.EtaleSiteᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The existing right-derived evaluation convention, on the equivalent small module category.
Source: Stacks, Cohomology on Sites, Section 01FT; Tags 03FD and 03F3
(blueprint: lem-sfb-space-surjective-qcoh-limit).
It computes H^p on the slice over U, including for a limit which is not quasi-coherent.
The named Grothendieck theorem supplies enough injectives; no extra assumption is made. -/
noncomputable def smallEtaleModuleCohomology {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (p : ℕ) : X.SmallModules ⥤ AddCommGrpCat.{u} :=
  letI : X.smallModuleEquivalence.functor.Additive := smallModuleRestriction_additive X
  letI := SheafOfModules.isGrothendieckAbelian X.smallStructureRings
  (smallEtaleModuleSections X U).rightDerived p

/-- The canonical ordinary-to-derived inverse-limit comparison for a strict module tower.
Source: Stacks, Cohomology on Sites, Tag 0BKY
(blueprint: lem-sfb-space-surjective-qcoh-limit).
First restrict the actual ordinary limit and use its specified projections to compare it
with the limit of the restricted tower. Place it in degree zero and apply the inverse
single/termwise-limit comparison. Finally apply the given derived unit. When RF and eta
are a right-derived pair this is precisely M[0] to R lim M_n[0], not an arbitrary map. -/
def surjectiveQCohLimitComparison {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{wA} X.SmallModules]
    [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ X.SmallModules)]
    (RF : DerivedCategory.{wT} (ℕᵒᵖ ⥤ X.SmallModules) ⥤ DerivedCategory.{wA} X.SmallModules)
    (η : (lim : (ℕᵒᵖ ⥤ X.SmallModules) ⥤ X.SmallModules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (M : ℕᵒᵖ ⥤ X.Modules) :
    (DerivedCategory.singleFunctor X.SmallModules 0).obj
      (X.smallModuleRestriction.obj (limit M)) ⟶
        RF.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ X.SmallModules) 0).obj
            (M ⋙ X.smallModuleRestriction))) :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor X.SmallModules 0).map
      (limit.post M X.smallModuleRestriction) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ X.SmallModules) ⥤ X.SmallModules) (.up ℤ) 0).inv.app
            (M ⋙ X.smallModuleRestriction)) ≫
    η.app ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ X.SmallModules) 0).obj
      (M ⋙ X.smallModuleRestriction))

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

/-- Source: Stacks Tag 0D3E (2),(3) and its proof, via Tag 0BKY
(blueprint: lem-sfb-space-surjective-qcoh-limit).
Proof:
1. Affine etale objects form a covering basis. Restriction preserves local free
presentations (lem-pur-site-restriction-module-adjunction-exact).
2. Grothendieck abelianness gives enough injectives (lem-pur-ringed-site-grothendieck-abelian,
lem-sp-grothendieck-enough-injectives). Module/abelian and slice evaluation agree
(lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison,
lem-pe-ringed-site-derived-evaluation-slice).
3. Etale/Zariski comparison and affine vanishing give stage acyclicity
(lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
lem-sc-etale-zariski-qcoh-comparison, pqf-lem-affine-vanishing).
4. The quasi-coherent kernel of each transition is affine-acyclic, so the long exact
sequence gives surjectivity on affine sections (lem-trf-scheme-etale-quasi-coherent-kernel,
lem-weil-pbc-derived-functor-long-exact).
5. The Roos cokernel computation gives vanishing R^1 lim there
(lem-pc-derived-limit-roos-abelian-groups): solve x_n-f_n(x_(n+1))=y_n recursively,
starting with x_0=0 and lifting along each surjection.
6. Apply Tag 0BKY (lem-sfb-site-basis-inverse-limit-acyclic) to obtain the canonical
comparison isomorphism and limit acyclicity. The small-model equivalence preserves
limits and sections (def-pur-sheaf-inverse-limit). -/
theorem surjective_quasiCoherent_limit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{wA} X.SmallModules]
    [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ X.SmallModules)]
    (RF : DerivedCategory.{wT} (ℕᵒᵖ ⥤ X.SmallModules) ⥤ DerivedCategory.{wA} X.SmallModules)
    (η : (lim : (ℕᵒᵖ ⥤ X.SmallModules) ⥤ X.SmallModules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ X.SmallModules) (.up ℤ)))
    (M : ℕᵒᵖ ⥤ X.Modules)
    (_hqc : ∀ n : ℕ, (M.obj (op n)).IsQuasicoherent)
    (_hepi : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (surjectiveQCohLimitComparison X RF η M) ∧
      ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
        (∀ n : ℕ, Function.Surjective
          ((M.map (homOfLE (Nat.le_succ n)).op).val.app (op U))) ∧
        (∀ (n p : ℕ), 0 < p →
          Subsingleton ((smallEtaleModuleCohomology X U p).obj
            (X.smallModuleRestriction.obj (M.obj (op n))))) ∧
        (∀ p : ℕ, 0 < p →
          Subsingleton ((smallEtaleModuleCohomology X U p).obj
            (X.smallModuleRestriction.obj (limit M)))) := by
  sorry

/-- The inverse limit in the preceding theorem need not be quasi-coherent.
Source: warning before Stacks Tag 0D3E
(blueprint: lem-sfb-space-surjective-qcoh-limit).
Proof: on Spec k[t] take the etale modules associated to k[t]/(t^(n+1)). Their
quotient transitions are epic and the modules are quasi-coherent. The sectionwise
limit has global sections k[[t]] and zero sections on D(t). Quasi-coherence would
identify the latter with k[[t]][1/t], which is nonzero since no power of t kills 1.
Thus the limit is not quasi-coherent. The representable scheme is an algebraic
space over itself, in every scheme universe, and its etale module comparison
preserves sections and exactness. This is step 7 of the node, using
lem-weil-pbc-spec-module-tilde-sections, lem-weil-pbc-affine-tilde-gamma-adjunction,
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
lem-sfb-scheme-etale-module-exact-finiteness-comparison and
lem-weil-pbc-quasi-coherent-affine-section-base-change. -/
theorem exists_not_quasiCoherent_surjective_limit :
    ∃ (S : Scheme.{u}) (X : AlgebraicSpace S) (M : ℕᵒᵖ ⥤ X.Modules),
      (∀ n : ℕ, (M.obj (op n)).IsQuasicoherent) ∧
      (∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) ∧
      ¬ (limit M).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
