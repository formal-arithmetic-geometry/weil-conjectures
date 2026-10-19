## Worker report

The module `lean/Sheaf/SixFunctors/IntegralTensorQuotientEpimorphism.lean` states
`SheafOfModules.integral_tensor_quotient_epimorphism`. It uses the existing
sectionwise change-of-rings construction and its sheafification. The auxiliary
`integralTensorQuotientPresheafUnit_naturality` theorem and
`integralTensorQuotientPresheafUnit` definition expose the canonical sectionwise map
whose component is the extension--restriction unit, and `integralTensorQuotientUnit`
is the corresponding sheaf morphism.

The item statement is rendered as follows. `C : Type u` with `[Category.{u} C]` and
`J : GrothendieckTopology C`, together with the three sheafification instances, render
the site and its common coefficient universe. The binders `R₀ R : Sheaf J CommRingCat.{u}`
and `q : R₀ ⟶ R` render the sheaves of commutative rings and their morphism. The binder
`hq : Presheaf.IsLocallySurjective J ((sheafCompose J (forget₂ CommRingCat.{u}
RingCat.{u})).map q).hom` renders the hypothesis that every coefficient section lifts
locally. The binder `F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat
RingCat)).obj R₀)` renders the sheaf of `R₀`-modules. The first conclusion,
`Presheaf.IsLocallySurjective J (...)`, is local surjectivity of the canonical unit after
viewing its sheaf morphism on underlying abelian presheaves. The second conclusion,
`Epi (integralTensorQuotientUnit q F)`, is categorical epimorphy in sheaves of modules
with scalars restricted along `q`. The canonical map is the existing sheafified
change-of-rings unit, whose sections are `1 ⊗ m` via the extension--restriction unit.

The statement and proof plan use these dependency declarations:

* `def-weil-pbc-sites-and-cohomology`: `CategoryTheory.Precoverage.IsSiteForCoverings`
  from `Sheaf.CategoryTheory.SiteCoveringAxioms` (site/topology conventions).
* `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` from
  `Sheaf.CategoryTheory.RingedSiteModules`, specialized here through the existing
  `SheafOfModules` category.
* `def-pur-sheaf-tensor-product`: the current recorded module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, whose public imports
  retain `SheafOfModules.changeOfRingsPresheaf` and `SheafOfModules.changeOfRings` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`. No dependency record is changed.

The edge cases checked were the zero module and zero tensor (the unit is the zero map
there), identity coefficient maps (the ordinary unit is `1 ⊗ m`), empty covering
families (the sheaf uniqueness condition supplies the unique section), and a one-object
site (local surjectivity reduces to ordinary sectionwise lifting). No enough-points
hypothesis or sectionwise global surjectivity was added.

Searches made before writing:

* `msearch.py ... leanfinder` for a canonical module-to-tensor-extension epimorphism:
  hits only presheaf epi criteria, generating sections, and restriction-Hom results;
  no scalar-extension unit theorem.
* `msearch.py ... loogle` for tensor surjectivity and extend-scalars names: no hit
  matching a sheaf scalar-extension unit.
* `msearch.py ... grep` for tensor/surjectivity in Mathlib Algebra: no matching theorem.
* `msearch.py ... leansearch` for module tensor extension along a surjective ring map:
  only ordinary module tensor lemmas, not sheaf local surjectivity.
* `rg` over `WeilConjectures` and `lean/Sheaf` for this item and scalar-extension
  epi/unit names: no existing declaration of this theorem.
* Direct source inspection of Mathlib `CategoryTheory.Sites.LocallySurjective`,
  `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and the project's TensorProduct
  module confirmed that the existing APIs provide the notions but not this theorem.


Self-check of the saved packet against the current sources: the tensor dependency's
current `SiteTensorFunctoriality` module already publicly imports the general tensor
interface and the change-of-rings construction. The saved dependency repair was therefore
removed, and the item now imports that recorded module. The helper naturality theorem and
both canonical-map definitions carry source/blueprint docstrings and appear in
`lean.declarations`. Their data are the actual extension--restriction unit and the actual
sheafification unit, not choices of arbitrary maps. The naturality theorem is the
well-definedness part of this node's first proof step, not a separate mathematical notion.
All variables and universes are explicitly bound. The sheafification instances are the
standard available structures on a site small in the coefficient universe.

The first dry run compiled the packet but rejected an `existing: true` dependency record
with `lean.file` and the trailing `:=` in the item's recorded signature. Removing the
unnecessary dependency delta and extracting the signature before `:=` repairs those
findings. No mathematical statement or proof plan is changed.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
