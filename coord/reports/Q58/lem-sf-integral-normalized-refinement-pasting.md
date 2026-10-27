## Worker report

The module `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` states
`WeilConjectures.IntegralSystemRealization.integralNormalizedRefinementPasting`.
There is one postponed theorem, with `sorry`; every helper has actual data.
The natural-language statement is unchanged. No dependency record is repaired and
four new definition nodes register existing published constructions, as required by H2.
The small helpers merely spell out this node's
one-input word, inverse system map, and finite outside-factor notation.

Hypothesis-by-hypothesis correspondence:

- The coefficient prime is `(l : ℕ) [Fact l.Prime]`, the finite extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `(D : FiniteFieldDatum.{u})` supplies the finite-field datum and algebraic closure;
  `hl : l ≠ D.p` is precisely the distinct-characteristic assumption. The existing
  coefficient rings, uniformizer and transitions are used throughout the system
  calculus. Its index `n : ℕ` denotes exponent `n+1`, hence exactly all positive levels.
- `X Y : Over (Spec (CommRingCat.of D.k))` with the two `LocallyOfFiniteType` and
  `QuasiCompact` structure-map instances are the two finite-type k-schemes.
  `f : X ⟶ Y` is a morphism over k; `IsSeparated f.left`, `LocallyOfFiniteType f.left`
  and `QuasiCompact f.left` express separated finite type. There is no separatedness
  assumption on `X.hom` or `Y.hom`. Two definitional instance transports identify
  the bundled structure morphisms with their typeclass versions, without adding data.
- `Operations l E` and `R : Realizations l E D o` are the actual simultaneous
  strict-semilinear ordinary-derived operations and the prescribed normalized
  realizations. Their `canonicalBridge` identifies them with the intrinsic
  semilinear proper/open maps. Proper compositors are adjunction conjugates of the
  specified pullback compositors. `normalizedRefinementWord f c` is exactly B_c.
- `hDiagram` requires `Expression.domain` for each of the eighteen published
  `refinementDiagramWords`, for every binary composable-refinement diagram and input.
  This includes input, each open prefix, both refinement images, their composite,
  nested images, all final proper images and the compact-support words. Identity
  diagrams are the constant family with identity refinements. The imported domain
  unfolds to input integral constructibility and `Good` for every intermediate;
  `Good` includes normalization, constructibility, uniform finite cohomology/Tor
  intervals, and compatible retained etale-origin witnesses. This is exactly the
  node's proviso that every displayed realization applies.
- `F` assigns each actual compactification a functor on
  `finiteTorConstructibleIntegralCategory`, the recorded C_R=D^b_ctf category.
  Its inclusion is the existing object-property full-subcategory inclusion `.ι`.
  `r c` is the stated natural realization `F_c ⋙ I_Y ≅ I_X ⋙ Rp_*j_!`.
- `_compatible` says that `F_c` agrees, in the constructible category, with the
  prescribed `sfCompactSupportFiniteIntegralFunctor`, by a natural iso `η`, and that
  `r c` is exactly the resulting transport of the inverse canonical
  `sfQcqsCompactSupportRealization`. This retains the specified compact-support
  realization rather than assuming an unrelated endpoint iso. The intermediate
  inclusion `finiteTorIntegralInclusion` only forgets the Tor predicate.
- `ρ v` is the *given* natural isomorphism for every actual proper refinement.
  Refinement is the upstream `Compactification.Refinement`, with both triangles;
  its `isProper` instance supplies properness, so no extra refinement hypothesis is
  imposed. `e v` is the supplied open-to-refinement-proper-image isomorphism.
- `_transpose` fixes `e v` by the actual `ringedOpenAdj` Hom equivalence: its
  transpose followed by `PurCompactSupport.refinementRestriction` equals the open
  unit. That restriction is the existing pullback-composition map followed by the
  proper counit, i.e. restriction through the clopen section over X. This is the
  node's open-unit normalization, not equality of finite reductions.
- `_normalization` conjugates the given `ρ v` by `r c,r d`, then requires exactly
  inverse proper composition (including `v.hom_g`) followed by proper image of
  `(e v).inv`. The formula uses `ringedPushComp`, the same specified compositor.

Clause-by-clause correspondence:

1. The first conjunct is equality of the given natural isomorphisms
   `ρ (.id c) = Iso.refl (F c)`.
2. The second conjunct is `ρ (v.comp w) = ρ v ≪≫ ρ w`, for all binary refinements,
   again equality in the integral functor category itself.
3. The third conjunct asserts invertibility of the existing reverse system
   refinement at the reduced input, then the equality
   `I_Y(ρ_v) ≫ r_d = r_c ≫ c_Bc.inv ≫ L(t_v) ≫ c_Bd.hom`.
   Here `normalizedRefinementSystemMap` is `inverseOrZero` applied to
   `completedShriekRefinement`; its invertibility is a conclusion of this very
   theorem, so only the actual inverse is used on this domain. The existing reverse
   map is open image of the identity-proper unitor followed by intrinsic gamma and
   the proper compositor. Its inverse is exactly the node's forward t_v.
   Multiplying the displayed equality by `r_d.inv` gives the stated conjugation
   `I_Y(ρ_v)=a_d L(t_v) a_c^{-1}` (in conventional composition order).
4. The final conjunct gives that same equality after every finite proper/open
   outside context `q`. It applies the actual ordinary integral context functor to
   `r_c.inv ≫ I_Y(ρ_v) ≫ r_d` and identifies it with the total limit of the actual
   system context applied to t_v. `gc,gd,hc,hd` are exactly the geometric and
   all-intermediate-domain assumptions for this particular outside diagram.
   `q.realization` is the prescribed `R.comparison`, with explicit recursive
   associators identifying a substituted expression with the outside functor.
   This carries the same compositors on both sides. There is no finite evaluation
   in any equality hypothesis or conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its fields.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the coefficient-extension
  constructions and positive-ring finiteness. `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory` specialized to the imported actual ringed-site module categories.
- `Sheaf.SixFunctors.AmbientProperOpenPasting`: its `systems`, `Calculus.sComp`,
  `Calculus.gamma`, and `ambientProperOpenPasting`, for the proof plan.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`: `Realizations`,
  `comparison`, its normalization and coherence; its public expression-domain and
  canonical-bridge modules supply `System`, `Integral`, `Operations`, `Good`,
  `Expression`, `Expression.domain`, `ringedOpenAdj` and `ringedPushComp`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  including its Roos projection normalization and absence of absolute separatedness.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, `.id`, `.comp`, `.isProper`.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`:
  `WeilConjectures.purNormalizedReconstruction`, for the proof plan.
- `Sheaf.SixFunctors.GeneratorReductionStatement`: `GeneratorReduction.inverseOrZero`,
  and `generatorReductionCoherence` for the proof plan.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`: the intrinsic gamma, its
  adjunct normalization, identity and pasting equations, for the proof plan.
- Definition ownership in `stmt_deps` is recorded by the four new nodes listed below.
  `def-weil-finite-tor-amplitude` still supplies `finiteTorConstructibleIntegralCategory`
  in `Sheaf.Paper.FiniteTorAmplitudeSites`. No conclusion of the four containing
  theorem nodes is needed to type the statement. The generator-coherence theorem
  remains an original proof dependency, where its eventual use belongs.

Edge cases checked: zero input; empty source or empty open; identity refinements;
identity outside context; arbitrarily long finite proper/open outside words; first
finite level (exponent 1); no exponent-zero coefficient ring; nonseparated finite-type
source and target structure morphisms; arbitrary universe u with the imported small
pro-etale site convention. In particular the one-variable index is `ULift.{u} Unit`,
so it imposes no small-universe constraint on the schemes or inputs. Zero and empty
cases use the unique zero arrows, and identity cases use the specified unitors.

Searches made through the prescribed msearch wrapper:

- LeanFinder: `Integral compactification proper refinement maps normalized by open
  adjunction satisfy identity composition and total limit realization`: 8 hits,
  compact-open cover, Stone-Cech extension, Nobeling and LightProfinite transition
  identities; none states this integral derived refinement comparison.
- Loogle: `CategoryTheory.Adjunction.homEquiv`: 12 hits for generic adjunction Hom
  equivalences and their unit/composition formulas, not this geometric assertion.
- Mathlib grep: `integral.*refinement.*past|normalizedRefinement`: 0 hits.
- LeanSearch: `Integral derived complete compact support refinement maps compose by
  inverse limit realization`: 8 adic-completion and profinite-limit hits, no match.
- Project rg: `integral-normalized|normalizedRefinement|refinement_pasting` and then
  `integral.*refinement|refinement.*[Nn]ormal|refinement.*[Tt]rans`; upstream item-id
  search had no hit. This found the existing reverse refinement maps and the
  admissibility word list, which are reused. The completed-shriek theorem gives
  laws of its canonical maps, not the theorem for supplied normalized integral maps
  together with their actual total-limit identification. All helper names were also
  searched in Sheaf, WeilConjectures and `dag/lean_names_upstream.json`, with no
  conflict. Sources were read locally in blueprint/latest and Stacks more-etale.tex,
  including the vertical and horizontal pasting statements.

Validation: prescribed scompile.py compiled the actual library module cleanly after
removing the unused F-index binder warning. Earlier elaboration checks corrected
parentheses in the rho family type, public visibility of the inverse convention,
the structure-map instance transports, and explicit associators in the context
clause. Only this node's theorem has a postponed proof. No statement dispute.

## Second reading by Q58

Worker's in-thread rereading, not a claim of an independent second agent: the brief
forbids starting other agents and assigns the independent review to the maintainer.
I reread the node beside the full module. The two functor equations, forward map
orientation, endpoint realization conjugations, open-unit transpose and final
proper/open whiskering clause match the node. The existing reverse system arrow
was checked explicitly before defining its inverse. The draft originally omitted
the separate context equation; it now contains it with explicit associators.
The normalized-domain hypothesis retains hidden intermediate opens and composite
refinements, and the canonical compact-support compatibility uses the qcqs
realization, so absolute separatedness is not introduced. Helpers contain no
postponed data and the sole theorem docstring carries all five proof steps.

## Repair of H2

The returned head was e923f9be3ebe. The only returned defect was that four added
statement dependencies named theorem nodes even though the statement uses their
plain definitions. Replaced those four added edges by four new existing:true
definition nodes, with exactly the seven declarations named by the reviewer.
The finite-Tor definition dependency is retained. No source module, mathematical
statement, hypothesis, conclusion or original proof dependency changed. Current
main still has no Lean record for this item; the dependency declarations read from
current main are the same published constructions used by the returned module.
All new nodes reuse existing Lean data, so no new sorry or private copy is added.
The locally present dependency closures have no path back to the item; the returned
review independently confirmed that none of the four original closures reaches it.

## New nodes

`def-sf-completed-shriek-refinement-maps` registers specified system compact-support functor and reverse refinement map in `Sheaf.SixFunctors.CompletedShriekCompositionLaws`:
`WeilConjectures.IntegralSystemRealization.completedShriekF`, `WeilConjectures.IntegralSystemRealization.completedShriekRefinement`. Its signature is copied verbatim from the
published source. Source: `literature/stacks-project/more-etale.tex`, Tags 0F7B and 0F7J: the specified proper/open map and the compactification system functor, before any finite evaluation.
LeanSearch query `Compact support strict integral coefficient systems and the canonical refinement transformation` and LeanFinder query `Compact support strict integral coefficient systems canonical reverse refinement transformation` found no exact Mathlib
construction. The common Mathlib grep for all seven helper names returned zero
hits. Source rg found the existing declarations in this module; no corresponding
upstream declaration or definition-node owner exists. The exact blueprint-name
search returned zero matches. Search log records and source grep output are in
this node's `mathlib_searches`. Hence this is a new DAG owner with `existing:true`,
not a new Lean definition. It asserts no conclusion of the containing theorem.

`def-sf-refinement-diagram-words` registers eighteen typed words of a composable refinement diagram in `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility`:
`WeilConjectures.IntegralSystemRealization.refinementDiagramWords`. Its signature is copied verbatim from the
published source. Source: `literature/stacks-project/more-etale.tex`, Tags 0F7B–0F7D: words and all prefixes in vertical/horizontal proper-open pasting; blueprint exceptional inverse-image refinement argument, finite diagram bookkeeping.
LeanSearch query `Eighteen typed expressions for composable compactification refinements` and LeanFinder query `Eighteen typed expressions for a composable pair of compactification refinements` found no exact Mathlib
construction. The common Mathlib grep for all seven helper names returned zero
hits. Source rg found the existing declarations in this module; no corresponding
upstream declaration or definition-node owner exists. The exact blueprint-name
search returned zero matches. Search log records and source grep output are in
this node's `mathlib_searches`. Hence this is a new DAG owner with `existing:true`,
not a new Lean definition. It asserts no conclusion of the containing theorem.

`def-sf-integral-refinement-normalization-data` registers canonical refinement restriction and integral domain inclusion in `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
`WeilConjectures.PurCompactSupport.refinementRestriction`, `WeilConjectures.PurCompactSupport.finiteTorIntegralInclusion`, `WeilConjectures.PurCompactSupport.coefficientPrimeUnit`. Its signature is copied verbatim from the
published source. Source: `literature/stacks-project/more-etale.tex`, Tags 0F7B–0F7D: open-adjunction/counit normalization; blueprint exceptional inverse-image refinement compatibility and finite-Tor domain; finite-field coefficient convention.
LeanSearch query `Open restriction of proper compactification refinement and forgetting finite Tor amplitude` and LeanFinder query `Open restriction proper refinement finite Tor constructible category inclusion` found no exact Mathlib
construction. The common Mathlib grep for all seven helper names returned zero
hits. Source rg found the existing declarations in this module; no corresponding
upstream declaration or definition-node owner exists. The exact blueprint-name
search returned zero matches. Search log records and source grep output are in
this node's `mathlib_searches`. Hence this is a new DAG owner with `existing:true`,
not a new Lean definition. It asserts no conclusion of the containing theorem.

`def-sf-inverse-or-zero` registers inverse on isomorphisms with zero value elsewhere in `Sheaf.SixFunctors.GeneratorReductionStatement`:
`WeilConjectures.GeneratorReduction.inverseOrZero`. Its signature is copied verbatim from the
published source. Source: `literature/stacks-project/more-etale.tex`, Tags 0F7B–0F7D: notation for inversion of the canonical comparison on its invertible domain; blueprint proper/open coherence argument, complete restriction convention.
LeanSearch query `Inverse of a categorical morphism if it is an isomorphism and zero otherwise` and LeanFinder query `Inverse categorical morphism if isomorphism zero otherwise` found no exact Mathlib
construction. The common Mathlib grep for all seven helper names returned zero
hits. Source rg found the existing declarations in this module; no corresponding
upstream declaration or definition-node owner exists. The exact blueprint-name
search returned zero matches. Search log records and source grep output are in
this node's `mathlib_searches`. Hence this is a new DAG owner with `existing:true`,
not a new Lean definition. It asserts no conclusion of the containing theorem.

Repair rereading: reverse refinement has direction B_d to B_c; the item's
forward arrow still uses its inverse only after asserting invertibility. The word
list has exactly 18 entries and retains both nested and composite images. The
restriction definition uses the proper counit and the exact coefficient-composition
hypothesis. The inclusion forgets only Tor data; the prime-unit helper is already
proved. The inverse-or-zero definition includes its non-isomorphism case and has
independent category object/morphism universes. No absolute separatedness or
additional invertibility hypothesis has been introduced by a new record.

Repair validation: scompile.py compiled the unchanged module against the current
live library cleanly (only the expected postponed-theorem warning is permitted).

The first repaired dry run passed server preflight and both compilation checks.
The definition-node prose then made conventional composition order explicit as
B_c = S_pc ∘ J_jc and S_pd ∘ S_r → S_pc; the declarations are unchanged.
