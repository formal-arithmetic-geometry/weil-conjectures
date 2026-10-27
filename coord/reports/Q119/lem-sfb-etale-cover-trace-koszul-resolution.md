## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCoverTraceKoszulResolution` states
`AlgebraicGeometry.AlgebraicSpace.etaleCover_traceKoszul_resolution`, with its proof
postponed. All its helper abbreviations/definitions contain actual data from the existing
free-presheaf, sheafification, constant-sheaf and exterior-power constructions.
There is no statement correction and no disputed assertion.

Clause-by-clause correspondence:

* The base scheme is `{S : Scheme.{u}}`, and `X : AlgebraicSpace S` uses the recorded
  fppf-sheaf algebraic-space definition. `X.EtaleSite` and `X.etaleTopology` are precisely
  that dependency's small site and its topology.
* `U : X.EtaleSite` packages a scheme over S and its representable étale map to X;
  `U.obj.hom` is that map, and `hf : IsSurjective U.obj.hom` is the required additional
  surjectivity. No separatedness, quasi-compactness, or finite-fibre hypothesis occurs.
* The site has objects in `Type (u+1)` and morphisms in `Type u`. Coefficients and Hom
  presheaves are lifted into `u+1`; `ULift ℤ` and `uliftYoneda` are universe transports,
  not a restriction of test schemes or generators. No independent undersized universe
  or equality between object and morphism universes is imposed.
* `traceKoszulAbelian U` is literally `presheafToSheaf` of
  `uliftYoneda.obj U ⋙ AddCommGrpCat.free`, i.e. the sheafification of the free abelian
  presheaf on maps V → U over X. Yoneda restrictions precompose maps, hence send each
  basis vector to the basis vector of the restriction.
* `traceKoszulRing` is the constant integer commutative-ring sheaf;
  `traceKoszulCoefficients` only forgets commutativity. To use the existing module-valued
  exterior-sheaf API, `traceKoszulFree` module-sheafifies the free R(V)-module presheaf
  on the same maps, with R the constant integer sheaf. The existential isomorphism `i`
  identifies its underlying abelian sheaf with `traceKoszulAbelian U`, and the FIRST
  conjunct pins that isomorphism on every canonical generator. This is an equivalent
  presentation of the node's E, not an arbitrary module substituted for E. Indeed every
  R(V) coefficient is locally an integer, so sheafification identifies the two free
  presentations. This is also the construction of the canonical R-module action
  explained in the node's first proof step. The generator-pinned isomorphism identifies
  the object up to exactly the equality used by the statement; no object is chosen
  from a mere nonunique existence theorem.
* `ε` is an actual R-linear sheaf morphism from that E to the unit module R, and the
  SECOND conjunct sends every generator to the actual section `1 : R(V)`. Under i it is
  exactly the trace/augmentation specified by the node. Underlying R is the constant
  abelian integer sheaf by the canonical sheafification/forgetful comparison.
* `traceKoszulTerm U p` is the existing `siteExteriorPower E (p+1)`, sheafification of
  sectionwise exterior powers over R(V), with no copied exterior-power definition.
  `traceKoszulWedge` is the existing `siteExteriorWedge`, including its sheafification
  unit. Thus K_p is precisely wedge^(p+1) E over the constant integer sheaf.
* `a : K_0 ⟶ R` is epsilon after the canonical degree-one exterior identification.
  The THIRD conjunct, on every one-vector wedge, specifies this identification and
  augmentation; it does not treat wedge^1 E as definitionally E.
* `d p : K_(p+1) ⟶ K_p` is partial_(p+1). The FOURTH conjunct gives the full contraction
  on arbitrary local sections v, not only free basis sections. Its index is
  `j : Fin (p+1+1)`, sign is `(-1 : ℤ)^j.val`, scalar is `ε(v j)`, and
  `fun k ↦ v (j.succAbove k)` deletes position j preserving the remaining order.
  Scalar action is the module action over R(V).
* The FIFTH conjunct provides the zero composite K_1 → K_0 → R and exactness at K_0;
  the SIXTH provides every zero composite K_(p+2) → K_(p+1) → K_p and exactness at
  K_(p+1). These are `ShortComplex.mk ... h` and `ShortComplex.Exact` in the category
  `Sheaf X.etaleTopology AddCommGrpCat.{u+1}`, after `SheafOfModules.toSheaf`.
  Together they say that the displayed augmented sequence is a chain complex exact at
  every K_p. The final `Epi` of the underlying a is exactness at R in R → 0, and the
  terminal zero is automatically exact. No sectionwise surjectivity or exactness is
  substituted for sheaf exactness.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `etalePrecoverage`, `etaleTopology`.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; the
  category of abelian sheaves is Mathlib's `Sheaf`, as this dependency record says.
* `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `constantSheaf`; `Mathlib.Algebra.Category.Grp.Adjunctions`: `AddCommGrpCat.free`.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Free`: `PresheafOfModules.freeObj`;
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.
* `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`, `ι`,
  `exteriorPower`, `ιMulti`. The existing general-site specialization is
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteExteriorPower`:
  `SheafOfModules.siteExteriorPower`, `siteExteriorWedge`, themselves using upstream
  `PresheafOfModules.exteriorPower`. Added the already landed node
  `def-sfb-site-exterior-sheaf` to stmt_deps to record this use. No dependency record
  is repaired and no new node is needed.
* The tensor dependency's recorded `CochainTensorUniverses` module was inspected:
  its monoidal tensor is the existing sheafified sectionwise tensor. This statement
  uses the exterior construction directly; it introduces no second tensor or powers.
* Proof imports: `CliffordAlgebra.contractLeft`, `contractLeft_one`,
  `contractLeft_ι_mul` from Mathlib's `Contraction`; the three statements in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`; the underlying-set
  comparison `sheafifyComposeIso` and `sheafComposeIso_hom_fac` in Mathlib's
  `PreservesSheafification`; `largeSetSheafification_locallyBijective` in
  `Sheaf.CategoryTheory.LargeSetSheafification`; functor-category abelianity,
  evaluation preservation, left exact sheafification and `ShortComplex.mapHomologyIso`
  from the recorded Mathlib leaves of the exact-sheafification dependency.

Source checked: `literature/stacks-project/spaces-cohomology.tex`, lines 578–760,
including the trace, the contraction formula and equation-quasi-isomorphism (0723),
before Definition 0724. Zero-based signs agree with the source's one-based
`(-1)^(i+1)`. Also read the contraction recurrence in Mathlib and the source places
0622/0626 named by the node; the theorem docstring retains all five proof steps.

Edge cases checked: empty X and its empty cover are included; all resulting sheaves
are zero on the empty topos, so an epi to the constant integer sheaf is consistent.
Identity cover gives the rank-one Koszul resolution; a two-sheet cover has the usual
signed difference differential. Infinitely many sheets and non-separated covers
remain allowed. At p=0 the formula is the two-vector contraction with target K_0;
the separate one-vector clause is the augmentation. No degree or finite index family
from the node is lost. The coefficient ring is integers in all characteristics of
S, not its structure sheaf or a coefficient field.

Searches performed with the required msearch wrapper (2026-10-24):

* LeanFinder: “The augmented exterior Koszul complex of the free abelian sheaf on a
  surjective etale cover is exact” — 8 hits, concerning Mayer–Vietoris, cotangent
  complexes and Profinite.Nobeling; no étale-cover trace resolution.
* Loogle: `"KoszulComplex", "exact"` — 0 hits.
* Mathlib grep: `trace.*[Kk]oszul|[Kk]oszul.*trace|[Ee]xterior.*[Ss]heaf` — 0 hits.
* LeanSearch: “The augmented exterior Koszul complex associated to a surjective etale
  covering is an exact resolution of the constant integer sheaf” — 8 hits, generic
  augmentation and injective-resolution facts and Mayer–Vietoris; no match.
* rg in upstream `lean/WeilConjectures` and project `lean/Sheaf`, both by the item id
  and trace/Koszul terms — no existing statement. Broader exterior/free-sheaf searches
  found SiteExteriorPower (reused) and FreeModuleSheafConstruction (a free module on a
  set SHEAF, whereas the needed input here is the representable PRESHEAF; reused its
  underlying Mathlib free-presheaf construction). Upstream scheme exterior-sheaf
  constructions and scheme-only étale free-sheaf modules do not apply to this space
  site. The names were also checked against dag/lean_names_upstream.json.

Validation: scompile.py compiled the module in sandbox and library mode, each within
60 seconds, with no errors or unexpected warnings. Only the main theorem is postponed.

## Second reading by Q119

Author's second reading, not an independent review: reopened the node, source and final
Lean file. The correspondence above covers every hypothesis and conclusion. In
particular the generator-pinned abelian comparison avoids changing E, wedge^1 is
identified through the one-vector augmentation clause, the sign deletes positions in
increasing order, exactness is sheaf exactness, and the terminal constant-integer term
is included by the final Epi. Initial elaboration failures required explicit coefficient
universes and an explicit type for the unit section; these changed no mathematical
hypothesis. No separation, finite rank or sectionwise lifting assumption was added.
The maintainer's independent review remains the independent mathematical check.
