## Worker report

The module `Sheaf.Paper.FiniteFreeQuotientCompletion` states
`CategoryTheory.finiteFreeQuotientCompletion`, with its entire proof `sorry`.
It makes no change to the natural-language statement or its dependency lists.
There are no new DAG nodes and no repaired dependency modules.

Source reading: Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 3.4.12
and its proof, PDF pp. 22–23, and Definition 3.4.10; Stacks `sites-modules.tex`,
`lemma-abelian` (03DA), `lemma-limits-colimits` (03DB), the module-sheafification
universal property (03CY), and Section `section-tensor-product` (03EK).
The node explicitly supplies the general ringed-site finite-basis argument, rather
than claiming that Bhatt–Scholze states this finite-free comparison verbatim.
The current blueprint ancestor `lem-weil-scalar-extension-composition` was also
read: it states composition of finite scalar extensions and has no proof text.
The module docstring reproduces the node's seven-step argument, including both
cone blocks and the local derived-Hom conclusion over S.

Hypothesis and conclusion matching:

| Node text | Lean rendering |
| --- | --- |
| Small site | `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`. The universe `u` is arbitrary. The ring and module universe is large enough for this site, as in the recorded completion-unit interface. |
| Map of commutative ring sheaves R to S | `{R S : Sheaf J CommRingCat.{u}}` and `(φ : R ⟶ S)`. Forgetting commutativity uses `sheafCompose J (forget₂ CommRingCat RingCat)`, not constant coefficients. |
| Fixed finite basis, including rank zero | `(d : ℕ)` and `e : (∏ᶜ fun _ : Fin d ↦ unit R) ≅ (restrictScalars φ).obj (unit S)`. These categorical finite products are also finite direct sums in the abelian module category. The inverse of `e` supplies precisely the inverse basis coordinates. |
| Global section a and its image over S | `a : (SheafOfModules.unit ... R).sections` and `finiteFreeCoefficientSection φ a`. This helper applies Mathlib's `Functor.sectionsFunctor` to the actual coefficient map. It chooses no section. |
| Injective multiplication on both rings | `_haR : Mono (globalSectionMultiplication R a)` and `_haS : Mono (globalSectionMultiplication S (finiteFreeCoefficientSection φ a))`. For module sheaves a mono is sectionwise injective. |
| Exact countable products over both rings | The two `HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules ...)` instances. No exactness of products of arbitrary abelian sheaves is added. |
| Unbounded K-flat complex P | `P : CochainComplex (ringedSiteModules ... R) ℤ` and `_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P`. |
| Flatness of each term | `_hflat : ∀ k : ℤ, exactFunctor _ _ (tensorRight (P.X k))`. This is the node's stated exactness of tensoring with that term. |
| Q is termwise sheafified change of rings | Every occurrence of Q is the existing `SheafOfModules.changeOfRingsComplex φ P`, whose objects are `changeOfRings φ (P.X k)` and whose differentials are `changeOfRingsHom`. The recorded derived-change-of-rings module is imported, so its K-flat computation applies. |
| The two quotient completion cones and their units | The unchanged dependency constructions `regularQuotientCompletion` and `regularQuotientCompletionUnit`, over R with a and over S with its actual image. Their quotient towers represent the positive powers `a^(n+1)`. |
| Restriction identifies Q with P to the dth finite sum | The existential witness `α` in `IsFiniteFreeQuotientCompletionComparison`, together with its equation for every degree k, test object V, local scalar s, local element p and basis index i. The equation is exactly `s ⊗ p ↦ (λ_i(s) • p)_i`, with `λ_i` obtained from `e.inv ≫ Pi.π _ i`. |
| Sheafified tensor products | `finiteFreeExtendedTensorSection` first forms the elementary sectionwise tensor and then applies the actual sheafification unit `toSheafify`. It does not identify all tensor-sheaf sections with sectionwise tensors. |
| Restriction identifies the cones with the dth finite sum | The existential witness `β`. The intermediate quotient isomorphisms `θ n` are characterized by their quotient squares with `α`. Both degreewise cone-block equations specify `β` as the product reindexing of those same quotient comparisons. |
| The specified unit is preserved | The final conjunct of `IsFiniteFreeQuotientCompletionComparison` is `U.map η_S ≫ β.hom = α.hom ≫ Limits.Pi.map (fun _ ↦ η_R)`. This is equality of actual cochain maps for the dependency's specified zero-component unit. |
| Consequently local derived completeness is preserved over S | The second top-level conjunct is the implication from `IsLocallyDerivedRingedIdealComplete R ... (Q.obj P)` to the same predicate over S applied to the changed complex. This is the dependency's internal derived-Hom vanishing on every slice for every section in the generated ideal, rather than a condition only on images of R-sections. |

The `HasDerivedCategory` parameters select the ambient derived categories, also
on every slice as required by the recorded local-completeness predicate. Source
and target Hom universes `wR` and `wS` are separate. These are localization choices,
not boundedness, completeness, or mathematical extra hypotheses.

The four helper constructions besides the theorem are fully defined: image of a
global section, elementary tensors followed by sheafification, and the two cone-block
projections using the dependency's `roosχ` and product projections.
`finiteFreeQuotientComplexProducts` directly supplies Mathlib's existing degreewise
product instance for complexes over these module sheaves. It has real data, no
postponed proof, and avoids expensive recursive instance search. None replaces a
tensor, cone, localization, completeness predicate, or scalar restriction.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (full defining predicate read).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (definition and additive instance read).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the E, object/map
  equalities, universal counit, and K-flat computation fields were read.
- `Sheaf.Paper.RegularQuotientCompletionUnit`:
  `regularQuotientCompletion`, `regularQuotientCompletionUnit`, and
  `regularQuotientCompletionUnit_criterion` (all signatures and docstrings read).
  Its `PrincipalKoszulQuotientTowers` and `StrictRoosModel` dependencies supply
  `globalSectionMultiplication`, `reductionTensorTower`,
  `koszulRepresentativeQuotient`, `koszulTowerComplex`, and `roosχ`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded sheafified tensor instance.
- The already recorded ordinary termwise construction
  `Sheaf.Algebra.Homology.ChangeOfRingsComplex`:
  `SheafOfModules.changeOfRingsComplex` (definition and its differential formula read).
- Proof imports retain `SheafOfModules.changeOfRings_isKFlat_of_flat_terms` from
  `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
  `CategoryTheory.moduleSheaves_colimits_forgetful` from
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, and
  `PresheafOfModules.sheafification` from its recorded Mathlib module.
  Their complete signatures and proof docstrings were read. There is no missing
  dependency record, new notion, or need for an interface repair.

Edge cases checked before drafting and again against the result:

- `d = 0`: the basis forces the restricted S-module to be zero. All finite products
  of complexes are zero objects; coordinate and block statements have no i to check.
  The unit equality and completeness implication remain present.
- `d = 1`, identity coefficient map: the formula specializes to the chosen rank-one
  basis (and to identity coordinates for the standard basis).
- `P = 0`: both cones and all maps are the zero constructions.
- `a` a unit: all positive quotient terms vanish; local derived completeness forces
  the input to vanish, so the implication remains correct.
- `a = 0`: regularity on R forces the zero ring sheaf, which is not excluded.
- Empty site and zero ring sheaves are not excluded. There is no nonempty-site,
  nonzero-ring, positive-rank, enough-points, or boundedness hypothesis.
- The shifted-product block is constrained separately from the ordinary product
  block; the unit is not an arbitrary derived-category lift.

Searches actually run (2026-10-21):

1. `msearch.py ... leanfinder` with query
   `For a finite free map of ring sheaves restriction of scalars identifies the quotient completion cone and its unit with finite direct sums`:
   eight hits, concerning `SheafOfModules.mapFree`, free-sheaf maps, and
   `Condensed.finFree`; none states this strict quotient-cone and unit comparison.
2. `msearch.py ... leansearch` with the same query: eight hits, including
   `SheafOfModules.restrictScalars`, presheaf and ordinary module scalar restriction,
   and `SheafOfModules.free`; useful infrastructure, no exact match.
3. `msearch.py ... loogle 'SheafOfModules.restrictScalars, CochainComplex'`:
   zero hits.
4. `msearch.py ... grep 'regularQuotientCompletion|finiteFree.*[Cc]ompletion|[Cc]ompletion.*finiteFree'`:
   zero Mathlib hits.
5. `rg` on `lean/WeilConjectures` for finite-free/completion language, and for
   the exact node ID: ordinary finite-free scalar extension and module completion
   results exist, but no general ring-sheaf strict quotient-completion comparison.
6. `rg` on `lean/Sheaf` for the same notions found the canonical regular quotient
   unit dependency and a related but different, still unstated
   `lem-pur-finite-free-completion-exchange`. The existing internal-ring-object
   theorem `lem-sfb-finite-free-scalar-coordinates` has a different module encoding
   and does not state this node's cone/unit/completeness assertion. Its record was
   read; no second copy of its internal-module notion is introduced here.
7. `rg` of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for every new declaration
   name returned no existing declaration. The exact repair-note path was checked;
   no repair note exists for this item.

No statement correction or `STATEMENT-DISPUTED` finding is needed.

Elaboration diagnosis: a sandbox probe showed that nested uses of the existing
`changeOfRingsComplex` were defaulting both source universe parameters to zero.
Every delivered occurrence therefore supplies `.{u, u}` explicitly, and restriction
specifies the module universe `.{u}`. The probe is removed from the delivery.
No universe equality beyond the recorded small-site representation was added.
The upstream name index was also searched for `finiteFreeQuotientCompletion`,
with no match.

The first theorem conjunct is
`IsFiniteFreeQuotientCompletionComparison φ d e a P`. This fully defined predicate
packages the three chain isomorphisms and five normalization clauses: the scalar
coordinate equation, quotient square, shifted-block equation, product-block equation,
and unit square. It is an owning-node helper interface, with no independent object
or chosen map. Local `let` abbreviations name the actual restriction functor, changed
complex, towers and cones once; they preserve the constructions definitionally and
avoid repeatedly elaborating them. The earlier existential telescope and record
forms exceeded the file time limit; this abbreviated predicate compiled in both
sandbox and library modes (30.6 s and 40.0 s respectively). The delivered file
contains no profiling commands, debug checks or temporary probes.

Final-file verification: `scompile.py NM lem-pur-finite-free-quotient-completion
lean/Sheaf/Paper/FiniteFreeQuotientCompletion.lean` succeeded in sandbox mode
(20.0 s) and library mode (34.1 s), with no error or unexpected warning. There is
exactly one `sorry`, the named main theorem. A final comparison with the live
read clone confirms that only the node's `lean` field changes. The sandbox
contains exactly one Lean module. The explicitly requested `grep -rn` of the
item id in `lean/WeilConjectures` also returned no match.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
