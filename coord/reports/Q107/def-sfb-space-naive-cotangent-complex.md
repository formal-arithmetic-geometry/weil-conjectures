## Worker report

Repair of the independently returned immutable head 76e2f67c67e7 (H4/H3/H13).
The saved packet was inspected and its required initial dry run passed as
6282a97341c. It still contained the returned larger-module-universe construction,
so it was repaired substantively before redelivery. The node records were refreshed
from the current shared read clone, preserving all base fields except the authorized
item correction and Lean records. No repository source or tool was edited.

`Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex` now defines
`AlgebraicGeometry.AlgebraicSpace.naiveCotangentComplex` as a
`CochainComplex X.SmallModules ℤ`, using `X.SmallEtaleModel`,
`X.smallEtaleModelTopology` and `X.smallStructureSheaf` from
`def-sfb-space-small-ringed-model`. Its derived image is in the already defined
`X.DerivedModules` from `def-sfb-space-derived-module-calculus`, with arbitrary
`[HasDerivedCategory.{w} X.SmallModules]`. There is no new abelian structure.
The ULiftHom site, lifted regular functions, lifted module category and fixed
u+2 localization have been removed. The generic construction accepted in the return
is retained unchanged.

Hypothesis-by-hypothesis and clause-by-clause reading:

- `{S : Scheme.{u}}`, `{X Y : AlgebraicSpace S}` and `(f : X ⟶ Y)` allow
  every base scheme, algebraic space and morphism in the node. There is no
  flatness, finiteness, separatedness, nonemptiness or characteristic assumption.
- The original scheme-chart site/topology remain those of `AlgebraicSpace`.
  The actual computation uses their already specified equivalent affine basis,
  `X.SmallEtaleModel` and `X.smallEtaleModelTopology`. No charts are lost as
  a topos: this is the existing restriction equivalence in the original section
  universe, not a new site or larger coefficient category.
- `cotangentRingInverse f` transports the existing enlarged-site inverse image
  through the scheme restriction and the existing small affine inclusion.
  `cotangentRingMap f` has source
  `(cotangentRingInverse f).obj Y.smallStructureSheaf` (A) and target
  `X.smallStructureSheaf` (B), both in `CommRingCat.{u}`.
  The full-site map is the adjoint mate of the uniquely chart-normalized map.
  Its small-site transport explicitly uses the inverse comparison unit at
  `Y.commStructureSheaf` followed by that mate and restriction to X.
  Thus it pulls back regular functions, including on every commuting pair of
  scheme charts, and is never an arbitrary ring map supplied as a hypothesis.
- `commStructureSheaf` on the full chart site has literally the existing
  regular-functions presheaf `X.etaleForget.op ⋙ Scheme.Γ`, retaining only
  commutativity data. After forgetting commutativity it is the existing
  `X.structureSheaf` (proof irrelevance identifies the sheaf-condition proofs).
  Its restriction along `X.smallEtaleInclusion` is definitionally
  `X.smallStructureSheaf`; there is no coefficient ULift or extra sheafification.
- `polynomialPresheaf A.obj B.obj` has exactly `MvPolynomial (B(U)) (A(U))`
  at U. `polynomialMap` sends C(a) to C(a restricted) and X(b) to
  X(b restricted). `polynomialSheaf` is its ring sheafification, not a
  sectionwise polynomial presheaf incorrectly assumed to be a sheaf.
- `coefficients` is the coefficient inclusion. `evaluationApp` sends [b] to b,
  and `evaluation` is its unique sheafification extension.
  `evaluation_properties` states both sectionwise surjectivity and the
  coefficient triangle, so the surjection is not an added assumption.
- `kernelIdeal` is the recorded `RingedSiteIdeal` with section ideal the actual
  kernel of evaluation. Its restriction and local-membership obligations are
  separately named theorems. `sectionExtension` uses the actual evaluation
  surjection as `Algebra.Extension.ofSurjective`.
- `conormalObj` is Mathlib's `Algebra.Extension.Cotangent`, i.e. I(U)/I(U)^2.
  Its B(U)-action is Mathlib's quotient action by a lift of b. Independence
  of that lift is built into that existing module structure. Restrictions
  send a kernel class to the class of the restricted kernel section, fixed
  by `conormalMap_existsUnique`. `conormal` sheafifies this quotient module
  presheaf. Sheafification of the algebraic ideal square is precisely the
  ideal whose sections locally are finite sums of products; its quotient is
  therefore the stated sheaf quotient I/I².
- `SheafDifferentials.omega (coefficients A B)` is the existing sheafification
  of sectionwise Kähler differentials, with restriction p dq mapped to the
  restricted p times d of restricted q. `differentials` applies the existing
  `SheafOfModules.changeOfRings` along evaluation. This is exactly the sheaf
  tensor product with B; Mathlib writes B tensor Ω instead of Ω tensor B,
  canonically the same tensor in commutative modules.
- `differentialSection` is the actual universal differential followed by the
  change-of-rings tensor and module sheafification unit: 1 tensor dg.
  `differential_existsUnique` characterizes the unique B-linear sheaf map
  on every local kernel class. Its proof docstring includes the Leibniz
  calculation killing I², B-linearity and compatibility with restrictions.
  `differential` chooses this uniquely specified morphism, not unspecified
  data from a mere existence assertion.
- `term` has the conormal in degree -1, differentials in degree 0, and the
  actual zero object in all other degrees. `boundary` has the conormal map
  at -1 and zero elsewhere. `complex` uses `CochainComplex.of`; its named
  square-zero obligation is `boundary_comp`.
- `naiveCotangentComplex f` applies that generic complex directly to
  `cotangentRingMap f`. Its coefficient ring sheaf is definitionally
  `siteModuleRings X.smallStructureSheaf = X.smallStructureRings`, so the
  module category is exactly `X.SmallModules`, with the existing equivalence
  `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules`.
- `naiveCotangentDerived f` is `DerivedCategory.Q.obj` of this same complex
  in `X.DerivedModules`. The localization morphism universe w is arbitrary,
  exactly as in the existing derived-module calculus.
- `naiveCotangentExt X E F n` is `E ⟶ F⟦n⟧` for every pair
  `E F : X.DerivedModules` and every integer n.
- `naiveCotangentModuleObject X M` places every `M : X.SmallModules` in
  degree zero using `DerivedCategory.singleFunctor X.SmallModules 0`.

Dependency declarations used (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.Γ`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `etaleTopology`, `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallEtaleModel`, `smallEtaleInclusion`, `smallEtaleModelTopology`,
  `smallStructureSheaf`, `smallStructureRings`, `SmallModules`,
  `smallModuleEquivalence`. The item now explicitly cites this node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`.
  The item now explicitly cites this node, retaining its arbitrary localization
  universe and its canonical module category rather than choosing another one.
- `Sheaf.AlgebraicGeometry.AtlasEtaleRestriction` and its public predecessors:
  the whole recorded dependency interface, in particular `enlargedRestriction`,
  `enlargedSchemeInclusion`, `enlargedDirectImage`, `enlargedChartLift` and
  the normalization in `IsEnlargedStructuralMap`. The dependency repair publicly
  imports every original declaration and lists it in the record.
- `Sheaf.CategoryTheory.RingedToposMorphism`: its full signature was inspected;
  its geometric inverse image and ring object describe the same canonical
  ringed-topos morphism used here through the recorded enlarged-site dependency.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, exactly
  Mathlib's `SheafOfModules` and abelian structure.
- `Sheaf.Paper.RingedSiteIdeal`: `siteModuleRings`, `RingedSiteIdeal`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`.
- `Mathlib.Algebra.MvPolynomial.Basic` and Eval: `MvPolynomial`, `C`, `X`,
  `eval₂Hom`; arbitrary sets of variables, no finiteness assumption.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`, its
  universal property, used through `SheafDifferentials.omega` and `.derivation`
  in the landed `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`.
- `Mathlib.RingTheory.Extension.Cotangent.Basic`: the base-independent
  `Algebra.Extension.Cotangent` quotient and its canonical target-ring action.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  existing tensor/change-of-rings interfaces, `changeOfRingsPresheaf` and
  `changeOfRings`, with the original coefficient and section universe u.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `singleFunctor`, and integer shifts.
- `def-weil-size-convention` is metatheoretic and has no declaration;
  explicit u and w and the already supplied SmallModel implement it here.

Edge cases: empty spaces/charts require no selected point and retain zero rings;
zero module sheaves are admitted; arbitrary infinite sets of ring sections are
allowed as polynomial variables. Identity maps still use the full polynomial
presentation rather than replacing its terms by zero. Mixed characteristic maps
such as Z → F₂ have the same evaluation/conormal/differential formulas. Integer
Ext includes zero and negative degrees. Every original-universe module sheaf,
including non-quasi-coherent coefficients, is covered by the existing module
restriction equivalence, and no larger universe of section modules is substituted.

Searches (2026-10-24; exact wrapper logs in sandbox searches.jsonl):

- msearch LeanFinder: `Naive cotangent complex of sheaves of commutative rings
  on a site` → 8 results, principally `relativeDifferentials'`, derivation,
  its universal property and ring-level `Algebra.H1Cotangent`; no site complex.
- msearch Loogle: `"cotangentComplex"` → 12 ring-presentation/base-change
  results; none has algebraic spaces or a sheaf-ring polynomial presentation.
- msearch grep: `naive.*cotangent|NaiveCotangent|cotangentComplex` → 25 ring-level
  Mathlib matches, no same definition.
- msearch LeanSearch: `Naive cotangent complex on the small etale site of an
  algebraic space` → 8 hits, small scheme étale topologies and ring cotangent
  maps/kernels; no algebraic-space naive cotangent complex.
- rg of the same patterns in both `lean/WeilConjectures` and `lean/Sheaf`:
  ring-level naive models and the full unbounded topological-space cotangent
  resolution exist, but do not define the present two-term small-étale object.
  `SheafDifferentials.omega` and existing sheaf tensor/change-of-rings are
  reused. rg of the exact item identifier in WeilConjectures found no match.
- rg of all proposed namespace/space declaration names in both libraries and
  `dag/lean_names_upstream.json` found no collision.

Repair searches: `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
`dag/lean_names_upstream.json` for the new cotangent helper names found no
collision. The current `AlgebraicSpaceSmallRingedModel` and
`AlgebraicSpaceDerivedModules` were read and reused, including their actual
commutative structure sheaf, module categories and localization universes.
Searching the algebraic-space ring interfaces found the existing RingCat map
but no exposed CommRingCat inverse-image structure map on this small model.
No new definition nodes are needed. There is no STATEMENT-DISPUTED flag.

## Dependency modules

`lem-trf-space-enlarged-etale-ringed-site-model` receives a lean-only interface
completion in `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`. The base
`AtlasEtaleRestriction` and every one of its recorded declarations are retained
by public import and in `lean.declarations`. Its RingCat structural map and
set-sheaf geometric morphism do not expose the required CommRingCat inverse-image
structure map on the existing small affine ringed model. The repair uses
CommRingCat.{u} everywhere, extends the existing scheme restriction equivalence,
and forms the adjoint mate of the ∃!-specified pullback-of-functions map.
It then transports this inverse image and its ring map through the affine-basis
restriction along the existing `smallEtaleInclusion`, with the inverse unit
identifying the extended target structure sheaf before applying the mate.
The resulting codomain is literally `X.smallStructureSheaf`. The existential
adjunction specifies its left adjoint up to the canonical adjunction isomorphism;
the structural map itself is pinned uniquely by its chart formula. No arbitrary
Nonempty ring map or extra hypothesis replaces the canonical construction.
Every postponed proof has a named theorem with its source, blueprint id and
natural-language proof; every definition has real data.

## Statement corrected

The correction is the requested §1(C) citation/presentation clarification, following
Stacks 0D0V, 08TW and 08U0. The previous wording failed to cite the existing small
ringed model and derived-module calculus, leaving the implementation of O_X,
Mod(O_X) and D(O_X) unspecified; the returned implementation enlarged module
sections from u to u+1. The revised text explicitly uses the existing affine-basis
model, its actual regular functions and original module universe, and its existing
D(O_X), with arbitrary localization morphism universe. This changes no mathematical
hypothesis, polynomial/conormal/differential formula, degree or Ext convention.
Only `statement`, `stmt_deps`, `statement_change` and `lean` change on the item;
only `lean` changes on the dependency. `proof` and `proof_deps` stay empty.
`statement_change.old_statement` below is verbatim from the current base node:

> Let $S$ be a scheme [def-pc-scheme] and $f:X\to Y$ a morphism of algebraic spaces over $S$ [def-trf-algebraic-space], in the size convention [def-weil-size-convention]. Work with sheaves of modules [def-weil-sheaf-of-modules-category] on the small etale site $X_{\mathrm{et}}$, whose objects are etale scheme charts and whose coverings are jointly surjective etale families. Use the canonical morphism of ringed topoi for $f$ supplied by [lem-trf-space-enlarged-etale-ringed-site-model], in the sense of [def-weil-pbc-ringed-topos-morphism]. Let $f_{\mathrm{small}}^{-1}$ be its inverse-image functor, put $\mathcal A=f_{\mathrm{small}}^{-1}\mathcal O_Y$ and $\mathcal B=\mathcal O_X$, and use the structure map $\mathcal A\to\mathcal B$. Form $\mathcal P=\mathcal A[\mathcal B]$, the sheafification [def-weil-pbc-sheafification] of the presheaf $U\mapsto\mathcal A(U)[\mathcal B(U)]$, the polynomial algebra [def-weil-pbc-mv-polynomial-ring] with one variable $[b]$ for every section $b\in\mathcal B(U)$. For a chart map $V\to U$, restriction sends coefficients by $\mathcal A(U)\to\mathcal A(V)$ and sends $[b]$ to $[b|_V]$. Let $\mathcal I$ be the ideal subsheaf [def-weil-pbc-ringed-site-ideal] given by the kernel of evaluation $\mathcal P\to\mathcal B$, $[b]\mapsto b$. Evaluation is surjective as a sheaf map: every section $b$ is the image of the section represented by the variable $[b]$. Let $\mathcal I^2$ be the ideal subsheaf whose sections locally are finite sums of products of two sections of $\mathcal I$, and let $\mathcal I/\mathcal I^2$ be the sheaf quotient. Its $\mathcal B$-module structure is the one induced by evaluation $\mathcal P/\mathcal I\cong\mathcal B$. Explicitly, for a local section $b$ of $\mathcal B$ choose a lift $p$ in $\mathcal P$ and set $b\cdot\overline g=\overline{pg}$; changing $p$ to another lift $p'$ changes $pg$ by $(p-p')g\in\mathcal I^2$, and changing $g$ by a section of $\mathcal I^2$ also leaves this class unchanged because $\mathcal I^2$ is an ideal subsheaf. Define $\Omega_{\mathcal P/\mathcal A}$ by sheafifying [def-weil-presheaf-modules-sheafification] the sectionwise modules of Kahler differentials [def-weil-pbc-kahler-differentials], with restriction $p\,\mathrm dq\mapsto p|_V\,\mathrm d(q|_V)$. The naive cotangent complex is
> $$\mathrm{NL}_{X/Y}=\bigl[\mathcal I/\mathcal I^2\xrightarrow{\,g\mapsto\mathrm dg\otimes1\,}\Omega_{\mathcal P/\mathcal A}\otimes_{\mathcal P}\mathcal B\bigr],$$
> in degrees $-1,0$, with zero terms in all other degrees and zero other differentials. Tensor products are sheaf tensor products [def-pur-sheaf-tensor-product], and quotients are taken in module sheaves [def-weil-sheaf-of-modules-category]. The displayed differential sends the class of a local section $g$ of $\mathcal I$ to $\mathrm dg\otimes1$; it is well-defined since $\mathrm d(gh)\otimes1=\mathrm dg\otimes h+\mathrm dh\otimes g=0$ for $g,h\in\mathcal I$, and is $\mathcal B$-linear: for $p\in\mathcal P$ and $g\in\mathcal I$, $\mathrm d(pg)\otimes1=p\,\mathrm dg\otimes1+\mathrm dp\otimes g=p\,\mathrm dg\otimes1$, with the $p$-action factoring through $\mathcal P/\mathcal I=\mathcal B$. These formulas commute with restrictions because restriction preserves multiplication and the displayed rule for differentials. We use the same notation for its image in $D(\mathcal O_X)=D(\operatorname{Mod}(\mathcal O_X))$ [def-weil-abstract-derived-category]. For any $E,F\in D(\mathcal O_X)$, write $\operatorname{Ext}^n_{\mathcal O_X}(E,F)=\operatorname{Hom}_{D(\mathcal O_X)}(E,F[n])$; a sheaf used as $F$ is placed in degree zero.

The only added statement dependencies are `def-sfb-space-small-ringed-model` and
`def-sfb-space-derived-module-calculus`. The complete citer audit (nine nodes,
all hold; none edited) is:

- `lem-sfb-affine-etale-naive-cotangent-presentation`: holds; The affine polynomial presentation and its derived comparison use the same rings, conormal and differentials under affine-basis restriction.
- `lem-sfb-etale-algebra-extension-ext`: holds; Square-zero extensions and derived Ext are transported by the same ringed-site equivalence, including arbitrary module coefficients and degrees zero and one.
- `lem-sfb-flat-space-split-deformation-ext`: holds; The deformation Ext groups retain the original module coefficients and canonical structural map under the restriction equivalence.
- `lem-sfb-scheme-naive-cotangent-etale-comparison`: holds; The canonical comparison still uses the same regular-functions ring map and polynomial complex, now represented in the existing small-model derived category.
- `lem-sfb-space-naive-cotangent-coherent`: holds; Coherence, boundedness and degree-zero structure sheaves are preserved by the specified restriction equivalence in the original module universe.
- `lem-sfb-space-naive-cotangent-etale-localization`: holds; The canonical inverse image and ring map are transported through the basis equivalences, so etale localization has the same meaning.
- `lem-sfb-space-naive-cotangent-finite-local-model`: holds; Affine-chart restriction, quasi-coherence and local finite presentations are unchanged by the specified small-model equivalence.
- `lem-sfb-space-naive-cotangent-quasicoherent`: holds; The cohomology is tested by the existing module equivalence, exactly as in the cited derived-module calculus; vanishing degrees are unchanged.
- `lem-sfb-space-square-zero-extension-transfer`: holds; The Hom tests and extension classification are in the existing original-universe derived category, with the same unrestricted coefficient modules.

## Worker verification

I reread the corrected node and both modules against the return and Stacks 0D0V,
08TW and 08U0. The unchanged generic construction still sheafifies A[B] before
forming the kernel; sheafifies I/I²; uses Ω tensor B via the existing change of
rings; and specifies dg tensor 1 uniquely on local kernel classes in degrees
-1 and 0. The space instance now uses the already established SmallEtaleModel,
smallStructureSheaf and SmallModules with no ULift. The inverse comparison unit
has the correct direction from extension of the small O_Y to the full O_Y before
applying the canonical full inverse image and structural mate. Restriction to X
then has target its existing smallStructureSheaf definitionally. Localization,
Ext and degree-zero sheaves all use X.DerivedModules and arbitrary w.

Both delivered modules compiled separately through scompile.py, in dependency
order, against the live published build: the ring map took 7.4 s (5.4 s in the
sandbox namespace); the main complex took 10.8 s (7.1 s in the sandbox namespace).
No errors or unexpected warnings occurred. The reporter's verification is a
self-check; the maintainer supplies the independent immutable-head review.


## Return L repaired: immutable head 1eb7f9978439

The retained packet's initial dry run passed at 531294b6e18. I then checked the
specific independent-review finding against the saved module and current source.
The two theorems have exactly the same binders: `universe u`,
`variable {S : Scheme.{u}}`, and `(X : AlgebraicSpace S)`, in the same namespace
with `CategoryTheory` and `Opposite` open. Their types are both
`Presheaf.IsSheaf X.etaleTopology (X.etaleForget.op ⋙ Scheme.Γ)`.
There is no difference hidden by section variables or opened namespaces.

Removed `cotangentStructurePresheaf_isSheaf` completely. Also removed the duplicate
`cotangentStructureSheaf` construction, since the same existing module already
constructs it as `commStructureSheaf`. The ring-map module now publicly imports
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra` and uses
`AlgebraicGeometry.AlgebraicSpace.commStructureSheaf` at every occurrence. That
definition uses the existing `commStructurePresheaf_isSheaf` theorem directly.
Both removed names are removed from the dependency's `lean.declarations`.
No new theorem, alias or parallel construction replaces them.

The existing source's full signatures and docstrings were read at lines 35–49.
The source is Stacks 03G7. `rg` in that module and in the saved ring-map module
confirmed the identical regular-functions presheaf and all replacement uses.
The polynomial presentation, conormal quotient, differential, small affine model,
original coefficient universe and derived conventions are unchanged. Empty charts,
zero rings and identity morphisms therefore retain precisely the same behavior.

This is the worker's self-check. The maintainer supplies the independent review.

Repair validation (2026-10-24): scompile.py compiled both delivered modules
separately against the live published build, including the private overlay and
sandbox namespace checks, with no errors or unexpected warnings. The ring-map
library check took 6.5 seconds and the complex library check took 4.5 seconds.
Both files have explicit universes and `autoImplicit false`; no line exceeds
100 characters. The item differs from the current read-clone node only in its
previously authorized `statement`, `stmt_deps`, `statement_change` and `lean`;
the dependency differs only in `lean`. The repaired ring-map signature and main
complex signature still match their node Lean records verbatim.

## Second reading by Q107

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
