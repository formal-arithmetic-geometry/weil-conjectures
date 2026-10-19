## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence` states
`AlgebraicGeometry.ProEtale.exact_openClosedSequence`, with its only proof `sorry`.
It introduces no definition. Source read: `literature/stacks-project/proetale.tex`,
`lemma-ses-associated-to-open` (Tag 09AH), including the full proof. That lemma
assumes precisely a scheme, a closed subscheme, and a quasi-compact complementary
open immersion. The finite commutative coefficient specialization is the DAG's
statement. The module docstring and theorem docstring identify the source and node;
the latter records the node's three-step coefficient, ringed-sequence and actual-arrow
identification proof.

Hypothesis and clause correspondence:

- A scheme X and schemes Z, U: `{X Z U : Scheme.{u}}`.
- Closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`.
- Complementary open inclusion j: `(j : U ⟶ X) [IsOpenImmersion j]` and
  `hU : Set.range j = (Set.range i)ᶜ`. Using an arbitrary isomorphic open subscheme
  rather than a chosen open does not change the assertion.
- Quasi-compactness of j: `[QuasiCompact j]`. There is no qcqs hypothesis on X.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The value universe is the standard one above the schemes; every finite ring has
  a copy in it. Module sections remain arbitrary types in this universe, not finite
  modules, so there is no finiteness or constructibility hypothesis on F.
- Small pro-etale sites: `Scheme.ProEt.topology X` (and the same construction at U,Z).
- Every constant-ring module sheaf F:
  `F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`.
  This is the fixed-coefficient presentation already selected by the recorded
  extension-by-zero dependency. A sectionwise Λ action extends uniquely to the
  constant ring sheaf action: on a covering where a ring section is represented
  by constants, multiply by those constants and glue. Conversely restrict the
  ring-sheaf action to constant sections. These inverse constructions retain the
  same underlying abelian sheaf and linear maps. Thus this is precisely sheaves
  of Λ_X-modules, not modules over the scheme structure sheaf.
- Inverse and direct image: `Scheme.proEtaleSheafAdjunction i (ModuleCat Λ)` uses
  `proEtaleSheafInverseImage` and `proEtaleSheafDirectImage` from the recorded
  inverse-image dependency, whose latter functor is sectionwise base change.
  With fixed coefficients inverse image is the same Kan extension and sheafification
  as `ProEtale.upperStar`; their definitions and adjunctions are identical. This
  is the constant-coefficient presentation of the tensor pullback in the node.
- Extension by zero and its specified counit: the first arrow is
  `(openImmersionLowerShriekUpperStarAdjunction (ModuleCat Λ) j).counit.app F`.
  This adjunction has left adjoint the recorded `openImmersionLowerShriek` and
  right adjoint `upperStar`, hence its source is exactly j_!j^*F.
- The specified unit: the second arrow is
  `(Scheme.proEtaleSheafAdjunction i (ModuleCat Λ)).unit.app F`, with codomain
  i_*i^*F. No arbitrary maps or adjunctions are quantified over.
- Exactness at the first and last nonzero terms is respectively `Mono` of the
  counit and `Epi` of the unit. The remaining conjunct is
  `(ComposableArrows.mk₂ counit unit).Exact`, which includes zero composite and
  equality of image with kernel at F. These three conjuncts are exactly the
  stated short exact sequence, without requiring an additional zero-composite
  helper theorem or choosing its proof. This is categorical epimorphy, not
  surjectivity of sections on every site object.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is explicitly a convention node, whose
  recorded note directs citers to Mathlib `IsClosedImmersion`, `IsOpenImmersion`
  and `QuasiCompact`. Those properties are the actual binders here.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `Scheme.proEtaleDerivedCategory`; its docstring and expansion use
  `Scheme.ProEt`, `Scheme.ProEt.topology` and the constant ring sheaf. No derived
  object is required by the present statement.
- `def-weil-proetale-inverse-image`:
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses` publicly retains
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`; the actual declarations used are
  `Scheme.proEtaleSheafAdjunction`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`. Their complete source signatures and docstrings
  were read. The fixed-coefficient `upperStar` and `lowerStar` definitions and
  `upperStarLowerStarAdjunction` were also read and are definitionally identical.
- `def-weil-extension-by-zero`: relocated upstream module
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`,
  `ProEtale.openImmersionLowerShriek`, `localizationLowerShriek_eq`,
  `openImmersionLowerShriekAdjunction`, and
  `openImmersionLowerShriekUpperStarAdjunction`; see the dependency-record repair below.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, read with docstring. Its module is inherited
  through the inverse-image import. The fixed-coefficient presentation above
  explains its role rather than defining another constant sheaf.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, and its Mathlib match `SheafOfModules`.
  Source and docstring were read; the module is publicly inherited through the
  inverse-image import. The exact fixed-coefficient presentation is explained above.
- `def-weil-pbc-exact-sequence`: `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ComposableArrows.Exact`. Its structure includes `IsComplex` and
  every consecutive short complex's `Exact`. `ShortComplex.ShortExact` was read
  to check the equivalent Mono/Exact/Epi formulation.
- Stated proof dependency `lem-weil-pbc-proetale-ringed-open-closed`:
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
  `Scheme.proEtale_ringed_open_closed`, imported non-publicly for the recorded proof.
  Its complete theorem and docstring were read. The other proof dependency
  `prop-weil-pbc-proetale-constant-ring-map` has no recorded Lean statement and
  is not imported; it is not needed to type the present statement.

Edge cases checked against the source and signatures: empty X; empty U (first
term zero, identity closed restriction); empty Z (unit to zero and counit an
isomorphism); zero F; the zero finite ring (allowed because no `Nontrivial`
hypothesis); arbitrary finite ring characteristic; non-qcqs X and nonconstructible
F. None is excluded. The complement condition is equality of underlying point
ranges, as in the source; Z need not be reduced. No claim uses ordinary geometric
stalk detection.

Searches for an existing statement:

- `msearch.py ... leansearch "The canonical open closed sequence for pro etale
  sheaves is short exact"`: service unavailable, Internal Server Error.
- `msearch.py ... leanfinder "For a sheaf of modules on the pro etale site the
  counit of open extension by zero and closed restriction unit form a short exact
  sequence"`: eight hits, including MayerVietorisSquare short complexes,
  Profinite.NobelingProof, module-sheaf abelian structure and Zariski restriction;
  none is this pro-etale localization sequence.
- `msearch.py ... loogle '"ProEtale", "ShortExact"'`: zero hits.
- `msearch.py ... grep "openClosedShortComplex|shortExact_openClosed|open_closed"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in upstream `WeilConjectures`, the published framework, and `lean/Sheaf`
  for `openClosedShortComplex|shortExact_openClosed|lem-sf-proetale-open-closed-sequence`:
  upstream matches concern the etale site, not the pro-etale site; the side
  matches include a docstring citing this node. No exact reusable statement.
- Full source inspection of the published finite-coefficient upper/lower-star and
  open lower-shriek files confirmed that these define the required functors and
  adjunctions but do not state the requested open-closed sequence.

No statement correction, new notion, hollow definition or disputed mathematical
statement is involved. All edits are in the item sandbox.

## Dependency modules

`def-weil-extension-by-zero` receives a lean-only existing-declaration repair under
§1(B). Its old module imports the legacy `UpperLowerStar.Defs`, which duplicates
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»` from the relocated finite-coefficient
module imported by the current inverse-image interface. The compiler reported
that collision on the first attempt. The published
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
contains the same extension-by-zero construction, signatures and adjunctions,
with compatible relocated imports. The record now points to that module and
also lists `openImmersionLowerShriekUpperStarAdjunction`, the canonical adjunction
whose counit occurs in this statement. The prior primary statement and all
non-lean fields stay unchanged. There is no new dependency source file.

## Second reading by NX

I read the node statement, its Stacks source, every recorded statement dependency,
and the module independently. The correspondence is as follows.

- The node's scheme `X`, closed subscheme `Z`, open complement `U`, and inclusion
  morphisms `i : Z ⟶ X`, `j : U ⟶ X` are the binders `{X Z U : Scheme.{u}}`,
  `i`, and `j`. The classes `IsClosedImmersion i` and `IsOpenImmersion j`
  render the two immersion hypotheses from the node and Stacks Tag 09AH.
- The complement condition is rendered by
  `hU : Set.range j = (Set.range i)ᶜ`, and quasi-compactness by the exact
  instance `[QuasiCompact j]`. No qcqs, Noetherian, separated, reduced, or
  constructibility hypothesis was added.
- The finite commutative coefficient ring is exactly
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. The coefficient sheaf category
  is `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`, the fixed-
  coefficient presentation of sheaves of `Λ_X`-modules supplied by the
  inverse-image and extension-by-zero dependencies.
- The first displayed arrow is precisely
  `(openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F`,
  hence the specified counit of `j_! ⊣ j^*`; the second is
  `(Scheme.proEtaleSheafAdjunction i (ModuleCat.{u + 1} Λ)).unit.app F`,
  hence the specified unit of `i^* ⊣ i_*`.
- The sequence conclusion is rendered by `Mono` for the first arrow, `Epi` for
  the second, and `ComposableArrows.mk₂ ... .Exact` for zero composite and
  exactness at the middle term. Together these are exactly the categorical
  short exact sequence `0 → j_!j^*F → F → i_*i^*F → 0`; no sectionwise
  surjectivity or extra clause is asserted.

I checked the empty scheme, empty open, empty closed subscheme, zero sheaf,
zero finite ring, arbitrary finite characteristic, and `n = 0` (which does not
occur in this node). The binders do not exclude any of these cases. I also
checked that the distinct site object and morphism universes are retained.

For existing notions I repeated searches with `msearch.py` LeanSearch,
LeanFinder, Loogle, and grep over Mathlib, `WeilConjectures`, and `lean/Sheaf`.
The hits were the unrelated étale open-closed theorem, Mayer-Vietoris and
generic sheaf exactness, and pro-etale site definitions; no exact pro-etale
constant-coefficient statement exists. I inspected the source declarations
`Scheme.proEtaleSheafAdjunction`, `openImmersionLowerShriekUpperStarAdjunction`,
and `AlgebraicGeometry.Scheme.proEtale_ringed_open_closed` and their
docstrings. The latter's hypotheses and Mono/Exact/Epi clause agree with the
specialization used here.

The only repair in this delivery is the dependency record for
`def-weil-extension-by-zero`: its old legacy module collided with the current
finite-coefficient upper/lower-star declarations, so its `lean` record now
uses `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
and records the canonical upper-star adjunction. The item statement and module
signature required no change, and no new definition node or statement
correction is needed. The repaired module and all sibling imports compile via
`scompile.py` without errors or warnings.
