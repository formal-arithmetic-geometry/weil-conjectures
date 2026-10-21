## Worker report

Drafted `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds`, declaration
`AlgebraicGeometry.Scheme.exists_global_bounds_of_stratified_local_bounds`.
The sole theorem has proof `sorry`, with the five-step natural-language proof in its docstring.
The theorem statement is unchanged. The repair adds the definition node
`def-sfb-proetale-ring-derived-inverse-image`, with `existing: true` on the landed
canonical construction, to `stmt_deps`. The detection theorem remains in
`proof_deps` only. No Lean definition or dependency module is duplicated.

Clause-by-clause correspondence:

- The scheme is `X : Scheme.{u}`. `[IsNoetherian X]` is exactly the finite affine
  Noetherian-ring condition: Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with Noetherian
  coordinate rings on a finite affine cover. `IsNoetherian` combines local
  Noetherianity with quasi-compactness, not a dimension restriction.
- The finite immersion stratification is
  `S : FiniteLocallyClosedStratification X`, the recorded dependency declaration.
  Its `Fin S.n` strata are locally closed and pairwise disjoint, cover X, and
  have specified schemes and immersions realizing their images. No extra
  constructibility condition is imposed.
- The given covering on each stratum is
  `V : ∀ α, Scheme.Cover.{w} proetalePrecoverage (S.domain α)`.
  Its index universe `w` is arbitrary; indices need not be finite or inhabited.
  The covering is the fpqc weakly etale precoverage of Mathlib.
- `R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}` is an arbitrary commutative
  ring sheaf. Forgetting commutativity through `sheafCompose ... (forget₂ ... )`
  supplies exactly its underlying ring to the recorded `ringedSiteModules`.
  `K` is in the unbounded `DerivedCategory` of those module sheaves.
- `lower upper` choose the specified integer endpoints on every original cover
  member; `hinterval` records every inequality. Supplying the witnesses as
  parameters is the usual witness-expanded form of the existential local bounds.
- `hlocal` records vanishing in every integer degree satisfying
  `q < lower α j ∨ upper α j < q`. The restricted object is
  `proEtaleAllRingDerivedInverseImage ((V α).f j ≫ S.immersion α) ... |>.obj K`.
  This is the published exact termwise inverse image over the actual inverse-image
  ring, with no extension to different coefficients. Composite notation includes
  restriction to the stratum and then its original covering member.
- The conclusion supplies `m : Fin S.n → ℕ`, original cover indices
  `label α : Fin (m α) → (V α).I₀`, and actual open subschemes `W α k` of
  the corresponding covering members. `IsCompact (W α k : Set ...)` is precisely
  quasi-compactness of each open subscheme.
- The `Presieve.ofArrows` membership asserts that their composite maps to the
  stratum still form a pro-etale covering. The number of selected opens is finite
  since both the stratum indices and each `Fin (m α)` are finite.
- `∃ a b : ℤ, a ≤ b` gives the global interval. The two universal inequalities
  make a a lower bound for all selected original lower endpoints and b an upper
  bound for all selected original upper endpoints. In the nonempty case the next
  clause attains both bounds among the selected endpoints, hence a is their
  minimum and b their maximum. Attainment is a clause under an implication,
  so it does not accidentally demand an inhabited selected family.
- When `∀ α, m α = 0`, the clause forces `a = 0 ∧ b = 0`, exactly the empty
  selected-family convention, including zero strata.
- The last clause is `∀ q, q < a ∨ b < q → IsZero (H^q(K))` with the genuine
  derived-category `homologyFunctor`. There are no flatness, completeness,
  coefficient constancy, constructibility or dimension hypotheses on K or R.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used through
  `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian` and its exact finite-affine-cover
  characterization.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `Scheme.proetalePrecoverage`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, localization `DerivedCategory.Q`; the standard localization
  used by the published inverse-image interface is retained.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  its base change and adjunction, small-model transports and module inverse-image
  constructions. The commutative-ring interface's full signature and docstring
  were read; its extension to arbitrary ring sheaves is in
  `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`.
- `def-sfb-proetale-ring-derived-inverse-image`, with existing module
  `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`:
  `Scheme.proEtaleRingModuleInverseImage_exact`, its additive/finite-limit/finite-colimit
  instances, and `Scheme.proEtaleAllRingDerivedInverseImage`. The latter is the
  exact-functor localization of that actual inverse image. Its separate detection
  theorem has a stronger upstream stratification interface; that theorem is not
  substituted for the finite locally closed stratification in this statement.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedDerivedRestrictionGeneral`, `ringedOverFunctor_exactGeneral`,
  `ringedDerivedRestrictionSized`, and the degree-zero comparison. This dependency
  gives slice restriction; restriction along the arbitrary stratum morphisms uses
  the actual scheme inverse image above. The dependency's public module is imported.
- Proof import `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact` supplies
  `CategoryTheory.GeometricMorphism.geometric_inverse_image_exact`.

Sources checked: the local Bhatt--Scholze PDF, Lemma 6.5.3 and Proposition 6.6.11
(in particular its reverse direction); Stacks `topology.tex`,
`lemma-Noetherian-quasi-compact` (04ZA), and `proetale.tex`,
`definition-fpqc-covering` (0989) and its immediately following recognition lemma.
The arbitrary-ring boundedness lemma is the node's explicit finite-cover argument,
not a claim that the paper's adic constructibility Lemma 6.5.3 already has arbitrary
ring-sheaf hypotheses.

Edge cases checked before drafting: empty scheme; zero strata; empty covering of
an empty stratum; arbitrary infinite original index families; repeated original
cover labels; zero ring; zero complex; nonempty selected family with different
local intervals; equal interval endpoints; unbounded K a priori; nonreduced
immersion structures. None is excluded by the binders or attained-bound clauses.
For no selected opens, the output interval is forced to [0,0], with global vanishing
supplied by empty-cover detection. No mathematical dispute found.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "finite stratification local cohomological bounds
  pro-etale sheaf derived category"`: eight hits, ordinary local cohomology and
  `DerivedCategory.IsGE`/bounded-representative facts; no matching theorem.
- `msearch.py ... loogle "DerivedCategory IsGE IsLE Sheaf"`: zero hits,
  diagnostic `Unknown identifier IsGE`.
- `msearch.py ... grep "stratified|cohomological" Mathlib`: zero hits.
- `msearch.py ... leansearch "finite stratification local bounded cohomology
  derived sheaves pro etale"`: eight hits concerning Ext, finite presentations
  of sheaf modules and condensed limits; no matching theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for stratified/local
  cohomological bounds: found field-coefficient stratified lisse notions,
  unrelated classical bounds, and the general ring inverse-image/detection
  infrastructure reused here. No exact existing full conclusion.
- `rg` of the item id in `lean/WeilConjectures`: no declaration.

## New nodes

`def-sfb-proetale-ring-derived-inverse-image` owns the already existing arbitrary-ring
module inverse image and its exact termwise derived localization. Its `lean.module`
is `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`, its primary declaration is
`AlgebraicGeometry.Scheme.proEtaleAllRingDerivedInverseImage`, and `existing: true`
means no module is delivered for this node. Its source is Stacks 04JC (actual
inverse-image coefficients, identity ring structure map), 015F (the derived
functor of an exact functor is computed termwise even unboundedly), and 05RU
(localization at quasi-isomorphisms). All three source passages were opened in
sites-modules.tex and derived.tex.

Clause correspondence for the new definition: `{X Y : Scheme.{u}} (f : X ⟶ Y)`
is an arbitrary scheme morphism. `(R : Sheaf (ProEt.topology Y) RingCat.{u + 1})`
is any ring sheaf, including a noncommutative one. The declared codomain of
`proEtaleRingModuleInverseImage f R` is modules over exactly
`(proEtaleSheafInverseImage f RingCat.{u + 1}).obj R`. Its body is the existing
`proEtaleModuleToModel R ⋙ SheafOfModules.pullback (proEtaleRingModelUnit f R) ⋙
proEtaleModuleFromModel ...`, so it transports the canonical ring-unit pullback
through the existing small site model, without an arbitrary map or choice.
The primary derived abbreviation's entire body is
`(proEtaleRingModuleInverseImage f R).mapDerivedCategory`. Mathlib's
`CategoryTheory.Functor.mapDerivedCategory` is termwise localization, and its
`mapDerivedCategoryFactors` supplies the stated canonical factorization. The
registered additive, finite-limit and finite-colimit instances are exactly the
components of the already-proved `proEtaleRingModuleInverseImage_exact`.
`proEtaleAllRingModules_hasDerivedCategory` is `HasDerivedCategory.standard _`.
These auxiliary declarations are listed in the new node's `lean.declarations`.
The unowned `proEtaleRingModuleInverseImage` is also listed there: its defining
module is the public import `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`,
line 46. No definition's data is postponed, and no new theorem is introduced.

The original site keeps object universe u+1 and morphism universe u. The new
node assumes neither a stratification nor Noetherianity, boundedness, ring
commutativity or flatness. Empty schemes, identity morphisms, zero rings and
unbounded complexes are allowed. For a commutative R the consumer forgets only
commutativity, with both ring universes explicitly u+1; it does not extend scalars.

Searches for the new definition, all recorded with their actual returned log
records or rg output in `mathlib_searches`:

- LeanSearch, `exact inverse image derived category modules sheaves rings pro etale`:
  eight hits, including `SheafOfModules.pullback` and its adjunction; no separate
  arbitrary-ring pro-etale derived specialization.
- LeanFinder, `derive an exact inverse image functor on sheaves of modules over the
  inverse image ring`: eight hits, including pullback, scalar restriction and
  pushforward; the same general infrastructure, not another specialization.
- Mathlib grep, `proEtaleAllRingDerivedInverseImage|proEtaleRingModuleInverseImage|
  mapDerivedCategory` in Algebra/Homology/DerivedCategory: ten hits for generic
  exact-functor localization and its factorization, read in ExactFunctor.lean.
- The same first two identifiers in WeilConjectures: no matches. In Sheaf: found
  the exact existing module inverse image in ProEtaleRingInverseImage and the
  exactness/derived localization in NoetherianStratumDetection, all reused here.
- DAG grep found only the theorem node's bundled auxiliary declarations, with no
  definition node for this notion. `blueprint_refs.py search 'derived inverse image'`
  returned 19 general or coefficient-specific nodes, none for this specialization;
  `ancestor` gives det-lem-integral-models-stacks. This definition node is the
  explicit ownership correction requested by the maintainer, not a new construction.

## Return H2 repaired

The returned immutable head 46b27b34205e added the detection theorem to stmt_deps
solely to access definitions and instances in its module. Compared the retained
packet to the current base node; reconstructed the item from the current base,
retaining the Lean signature and changing only lean and the added definition-node
dependency. `lem-weil-pbc-noetherian-stratum-detection` is no longer in stmt_deps;
it remains in proof_deps for step 5. The new definition node owns the abbreviation,
the actual module inverse image, its exactness interface and derived-category
instance, with existing:true on the landed sources. The signature still publicly
imports NoetherianStratumDetection because that is where the recorded definition
is declared; its detection results are used only by the proof plan.

The advisory RingedDerivedRestrictionGeneral import is retained because this is
an explicitly recorded statement and proof dependency, and the stage requires
imports for the proof plan. No signature or theorem strength changed.

## Second reading by N7

Performed the required self-check without another agent, as this dispatch forbids
starting agents and reserves independent review for the maintainer. Read the saved
Lean signature against every clause of the unchanged node, including each hinterval,
hlocal, qc-open, covering, endpoint-bound, endpoint-attainment, empty-selection and
global-vanishing clause listed above. Found no mismatch. Checked the new node against
the actual signatures and bodies of all its recorded existing declarations and
Mathlib's exact-functor localization. The new node has no reference to detection,
finite strata or Noetherianity, and both detection theorems are excluded from its
lean.declarations. The generic geometric inverse-image theorem was also reread:
its module clause has commutative coefficients, while the existing pro-etale
exactness theorem explicitly covers arbitrary rings. The new definition therefore
uses and owns the latter interface directly, rather than recording the generic
commutative theorem as an arbitrary-ring specialization.

No statement correction or mathematical dispute is present. The only theorem
introduced by this delivery has proof sorry and its full five-step proof docstring.
All universes and variables are explicit; lines are at most 100 characters; the
item's lean.statement is still verbatim from the source. The new lean.statement
is verbatim from the existing abbreviation (which has an inferred result type).

## Validation

The required initial dry run on the retained packet passed server compilation
and preflight as aa33d4968a5. That packet still needed the substantive H2 ownership
repair, which is now applied as above. After repair, the prescribed explicit scompile.py check compiled the sandbox and
actual library module cleanly in 15.5 s and 14.5 s, with no diagnostics. The repaired
packet passed the prescribed deliver2.py --no-push preflight and per-file
compilation as commit 7a885ae49ff. No errors or warnings were reported.
