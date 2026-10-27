## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentDerivedInternalHom` states
`AlgebraicGeometry.AlgebraicSpace.coherent_derivedInternalHom`, with one `sorry`,
and introduces no definitions. The source is the local Stacks text
`spaces-perfect.tex`, lemma-coherent-internal-hom (0D0S), read together with
`spaces-cohomology.tex`, lemma-coherent-Noetherian (07UB). The statement is unchanged.

Clause-by-clause matching:

- A scheme S and algebraic space X over S are `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
- Local Noetherianness is `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. This is the equivalent chart formulation
  already used by `coherent_kernel_cokernel_zero_finite_sum_extension`. An atlas as in
  the node implies every etale scheme chart is locally Noetherian by etale locality
  (as explicitly recalled in the proof of 07UB). Conversely the atlas in the algebraic
  space definition is one of these etale charts, so it is locally Noetherian. The
  Mathlib scheme class means Noetherian coordinate rings on every affine open,
  equivalent to the existence of the affine cover in the node. No quasi-compactness
  or Noetherianness of the base scheme is assumed.
- The small etale structure sheaf and module category are represented by the existing
  `X.SmallModules`, via `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules`.
  Its restriction functor is restriction to the actual affine etale basis, its ring
  sections are regular functions, and the section universe remains u. It is the same
  ringed topos, not a different coefficient category. `X.DerivedModules` is the
  unbounded derived category of these modules. `[HasDerivedCategory.{w}
  X.SmallModules]` chooses its localization Hom universe, independently of u.
- Coherence on every Noetherian affine etale chart is precisely
  `SheafOfModules.IsFinitePresentation`. Stacks 07UB explicitly equates coherence,
  quasi-coherence of finite type, finite presentation, and coherent scheme-chart
  pullbacks. Over each Noetherian affine ring a finite module is finitely presented,
  and the associated etale sheaf has the stipulated tensor sections B ⊗_R N.
  Conversely a local finite presentation gives quasi-coherence and finite-type
  sections on any such affine chart, recovering that finite module. Restriction to
  the affine basis preserves local finite presentations and its inverse glues them,
  so the predicate on `X.SmallModules` is exactly the node’s coherence condition.
  This reuses Mathlib’s predicate; no substitute coherence definition is introduced.
- K and L are arbitrary `K L : X.DerivedModules`.
- Their coherent cohomology is `hK` and `hL`, requiring finite presentation of
  `(DerivedCategory.homologyFunctor X.SmallModules i).obj K` and the analogous L
  for every integer i. These are the usual cohomology functors of cochain complexes.
- The upper bound on K is `hKbounded : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (...)`.
- The lower bound on L is `hLbounded : ∃ b : ℤ, ∀ i : ℤ, i < b → IsZero (...)`.
  These are global bounds, and neither object is assumed bounded on the other side.
- The derived internal Hom is `X.derivedHom.obj (op K, L)`. The existing definition
  is exactly `derivedInternalHomOfUniverses` on the small ringed model, obtained by
  localizing the Hom-complex bifunctor with K-injective replacement of the target.
  It is contravariant in K and covariant in L, with no arbitrary chosen Hom object.
- The first conjunct of the conclusion requires finite presentation of every
  cohomology object of this RHom. The second is an existential integer c and
  `IsZero` in every degree i<c. Thus it says precisely coherent cohomology and
  boundedness below; it does not assert boundedness above or perfection.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules` and the atlas in `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and its affine-cover
  criterion; `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; Mathlib `SheafOfModules.IsFinitePresentation`
  in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (local finite presentations).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and its `homologyFunctor`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the affine finite-generation
  condition identified by 07UB with the finite-presentation predicate here.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` reexports
  `CategoryTheory.derivedInternalHomOfUniverses` from `DerivedInternalHomOfUniverses`;
  this generic interface is usable, so its ordinary-module primary record needs
  no repair. The algebraic-space `derivedHom` uses that exact generic declaration.
- Added the already landed owning nodes `def-sfb-space-small-ringed-model` and
  `def-sfb-space-derived-module-calculus` to stmt_deps. Their modules
  `AlgebraicSpaceSmallRingedModel` and `AlgebraicSpaceDerivedModules` supply
  `SmallModules`, `smallModuleEquivalence`, `DerivedModules`, and `derivedHom`.
  Both node statements, signatures, and source docstrings were read. No new node.

Proof-only imports are the recorded modules `LocalizedModuleExactForSystems`,
`AffineEtaleDerivedModuleRealization`, `RingedInternalHomShiftOfUniverses` and
`BoundedAboveCoherentRHom`. The algebraic-space proof dependency is already public.
`lem-sfb-affine-etale-derived-hom-realization` has no recorded Lean declaration on
this checkout, so there is no corresponding import yet; the full proof step remains
in the theorem docstring. Its absence is not a missing notion in this statement.

Edge cases checked: K=0 or L=0; empty algebraic space (all module sheaves zero);
non-quasi-compact locally Noetherian spaces (the hypotheses retain global bounds,
so the difference b-a is a common lower bound on every chart); complexes unbounded
in the permitted opposite directions; degree-zero finite modules with possibly
unbounded positive Ext. Universes u and w are independent. No finite-atlas,
regularity, smoothness, properness, separation or finite-global-dimension assumption
has been introduced. No false or disputed clause was found.

Searches: msearch LeanFinder on the full plain-language statement returned only
abstract derived-category bounds and sheaf cohomology. Loogle `"RHom", "Coherent"`
and Mathlib grep `[Cc]oherent.*([Rr]Hom|[Ii]nternalHom)|([Rr]Hom|[Ii]nternalHom).*[Cc]oherent`
returned zero hits. LeanSearch on the full statement returned generic localization,
bounds and small-Ext declarations, not this result. Local rg on WeilConjectures for
coherent/Hom and on Sheaf’s algebraic-space modules found scheme Hom results and
`pseudoCoherent_rhom_quasiCoherent`, which only concludes quasi-coherence, not
coherence and a global lower bound. An item-id search in WeilConjectures and Sheaf
found no prior statement. The upstream name table has no matching algebraic-space
coherent-RHom result. The search results are reproduced below.

## Second reading by Q153

This is the author’s separate reading, not an independent agent review: the dispatcher
brief prohibits starting other agents and assigns independent review to the maintainer.
Reopened the node, 0D0S, 07UB and the final module. Matched the base, algebraic-space
objects, local Noetherianness, module topos, each coherence condition, the direction
of the two global bounds, the variance of RHom, and both conclusion conjuncts as
listed above. Confirmed the small-model equivalence preserves the section universe
and the finite-presentation condition. No new axioms, choices, definitions, hidden
let binders or extra geometric assumptions occur. Removed an unneeded coherence
lemma import: the existing predicate and source equivalence already state the
condition. Every variable and universe is explicit; all lines fit 100 columns.
No statement correction or dependency module was required.

## Validation

scompile.py compiled the module as both sandbox and library (3.9 s / 4.2 s), with
no errors or non-sorry warnings. The final import cleanup is checked again by the
required delivery dry run.

## Search output

```jsonl
{"t": "2026-10-24T09:17:44Z", "tool": "loogle", "query": "\"RHom\", \"Coherent\"", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-24T09:17:44Z", "tool": "grep", "query": "[Cc]oherent.*([Rr]Hom|[Ii]nternalHom)|([Rr]Hom|[Ii]nternalHom).*[Cc]oherent", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-24T09:17:45Z", "tool": "leanfinder", "query": "Derived internal Hom of bounded above coherent and bounded below coherent complexes on a locally Noetherian algebraic space has bounded below coherent cohomology", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["DerivedCategory.instIsGEObjCochainComplexIntQOfIsGE", "DerivedCategory.instIsLEObjCochainComplexIntQOfIsLE", "DerivedCategory.instIsGEObjSingleFunctor", "CategoryTheory.HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE", "DerivedCategory.isGE_Q_obj_iff", "DerivedCategory.isLE_Q_obj_iff", "CategoryTheory.Sheaf.H", "DerivedCategory.IsGE"], "digest": "48d93d0ed988e6c1"}
{"t": "2026-10-24T09:24:56Z", "tool": "leansearch", "query": "Derived internal Hom of coherent bounded above and bounded below complexes on a locally Noetherian algebraic space is bounded below coherent", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["HasDerivedCategory.standard", "DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE", "HomologicalComplex.locallySmall", "CategoryTheory.IsGrothendieckAbelian.hasExt", "CategoryTheory.HasExt.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQuasiIsoOfIsGEOfIsLEOfNat", "DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE", "DerivedCategory", "CategoryTheory.hasExt_of_hasDerivedCategory"], "digest": "55934d0e5e8492a4"}
```
