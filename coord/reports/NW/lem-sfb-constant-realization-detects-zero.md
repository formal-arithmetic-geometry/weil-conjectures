## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero` states
`AlgebraicGeometry.ProEtale.constantRealization_detects_zero`, with its proof left as
`sorry`. Its auxiliary `constantRealizationUnit` is the component at `U` of the existing
module-sheafification adjunction unit. It contains real data, without a choice of an
arbitrary map or a postponed construction. Both declarations are recorded in `lean.declarations`.
The node's statement, dependencies, and proof remain unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme is `(X : Scheme.{u})`; its small pro-etale site is `X.ProEt` equipped with
  `Scheme.ProEt.topology X`. The structure map to `X` is part of `(U : X.ProEt)`.
- The underlying scheme is nonempty exactly when `[Nonempty U.left]` holds. There is
  no nonemptiness assumption on the coefficient ring or its nonzero elements.
- A commutative ring and an arbitrary module are `(R : Type (u + 1)) [CommRing R]`
  and `(T : ModuleCat.{u + 1} R)`. No finiteness, flatness, torsion, perfectness,
  connectedness, or weak contractibility condition is imposed.
- The constant module sheaf over the constant ring sheaf is precisely
  `(siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R).obj T`.
  The functor first constructs the constant module presheaf and then performs module
  sheafification along `toSheafify` for the constant ring presheaf. Its target is the
  intrinsic Mathlib `SheafOfModules` over `(constantSheaf _ RingCat).obj (RingCat.of R)`.
- The canonical map `T -> underline T(U)` is `constantRealizationUnit X R T U`.
  Its definition evaluates `PresheafOfModules.sheafificationAdjunction ... |>.unit.app`
  on `siteConstantModulePresheafGeneral ... |>.obj T`, at `Opposite.op U`, and takes
  its underlying function. The adjunction restricts scalars along the ring unit, so
  this is exactly the linear sheafification unit in the node, not an arbitrary function.
- Injectivity is the first conjunct, `Function.Injective (constantRealizationUnit X R T U)`.
- Zero sections imply a zero module is the second conjunct: `IsZero` of the actual
  section `ModuleCat` object at `Opposite.op U` implies `IsZero T`.
- The final conjunct states `IsZero (F.over U) -> IsZero T` for that same constant
  module sheaf `F`. Mathlib's `SheafOfModules.over` is restriction to the localized
  site with sectionwise unchanged values, including the terminal object `id_U`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` names the intrinsic ring-sheaf
  module-derived category on this very small site. The present theorem only needs its
  site, `Scheme.ProEt` and `Scheme.ProEt.topology`, and does not use a derived object.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`:
  `CategoryTheory.siteConstantModulePresheafGeneral` and
  `CategoryTheory.siteConstantModuleFunctorGeneral`, used directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, the exact `mathlib_match` of `def-pur-localized-ringed-site`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  transparent abbreviation of `SheafOfModules`; the functor already returns exactly
  that category. No replacement category is defined here.
- `Sheaf.CategoryTheory.SiteConstantModuleUnit` is imported for the proof dependency
  `lem-sf-constant-module-unit-locally-bijective`. Its published source was read using
  `scompile.py --source` because it is absent from the older local snapshot. Its named
  theorem and unit have equal site universes; they are proof inputs on a small model,
  not used to restrict the current statement's site universes. The present canonical
  unit directly uses Mathlib's general module-sheafification adjunction, whose object
  and morphism universes are independent.

Universe check: `X.ProEt` has object universe `u+1` and arrow universe `u`.
The dependency's generalized constant functor retains those two universes and uses
coefficients and modules in `u+1`; no equality of site universes is imposed. All variables
and universes are explicitly bound, with `autoImplicit false`.

Edge cases checked against the natural-language proof and source:

- For empty `U`, the empty covering kills constant-sheaf sections even for nonzero `T`;
  the theorem correctly excludes that case through the essential nonempty hypothesis.
  If `X` is empty there is no nonempty site object, so no contradictory assertion results.
- For `T = 0` and for the zero ring, injectivity and both zero-detection conclusions
  remain valid; no nontriviality hypothesis was introduced.
- A nonempty disconnected `U` is allowed: constant sections embed as diagonal locally
  constant sections; surjectivity of the unit is neither stated nor required.
- A nonempty point is the basic detection case. Nothing requires affine, connected,
  quasi-compact, or weakly contractible `U`.

Sources read: Stacks `sites.tex`, theorem-plus (00WB) and lemma-sections-sheafification
(00WK); `sites-modules.tex`, lemma-sheafification-presheaf-modules (03CY), and
Definition definition-localize-ringed-site (04IX), item (4); `proetale.tex`,
definition-fpqc-covering (0989) and its explicit joint-surjectivity consequence.
The theorem docstring records the node's three-step proof: local equality under the
unit, nonempty-cover detection with identity presheaf restrictions, then the two
zero consequences by section evaluation.

Searches for existing declarations (the interrupted session's `searches.jsonl` was
preserved and read):

- LeanSearch: "constant sheaf unit injective on a nonempty scheme object detects zero
  modules" returned eight hits on constant sheaves, scheme zero covers, generating
  sections and structure sheaf constants. None states this assertion for arbitrary
  modules on the pro-etale site.
- LeanFinder: "On the small pro-etale site of a scheme the constant module sheaf unit
  is injective at nonempty scheme objects and detects zero modules" returned germ,
  locally injective and sheafification results. None is the nonempty-object detection
  theorem. Those general sheafification inputs are already represented by the proof node.
- Loogle: `"constantSheaf", "injective"` returned no hits.
- Mathlib grep: `constant.*(injective|detects|reflects)|constantRealizationUnit|`
  `constantRealization_detects_zero` in `CategoryTheory/Sites` returned no hits.
  The broader grep with `faithful` returned 25 hits on condensed, profinite, and
  unrelated constant constructions, not this theorem.
- Direct `rg` of the slopmaster2 `WeilConjectures` tree, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the unit/theorem names and the exact node id
  found no pre-existing declaration. The existing generalized constant-module functor
  was reused rather than redefined.

Validation: `scompile.py NW lem-sfb-constant-realization-detects-zero` compiled this
module cleanly, separately as a sandbox file and with its intended module path,
under the normal per-file 60-second limit. No warnings, extra nodes, dependency
repairs, or statement corrections were needed. The only postponed proof is the
named theorem matching this DAG node.

## Second reading by NW

No second reading by a worker: the dispatched direct-delivery brief delegates the
independent review to the maintainer. The clause correspondence above is the author's
self-check, not an independent review.
