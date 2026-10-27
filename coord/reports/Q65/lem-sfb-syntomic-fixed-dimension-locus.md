## Worker report

Module: `Sheaf.AlgebraicGeometry.SyntomicFixedDimensionLocus`.
Main declaration: `AlgebraicGeometry.syntomic_fixed_dimension_locus`.
The two public helpers now belong to definition node
`def-sfb-syntomic-fixed-dimension-open` and its separate module
`Sheaf.AlgebraicGeometry.SyntomicFixedDimensionOpen`. They package the exact fibre
property and construct the candidate locus as an actual supremum of source opens.
Definition node `def-sfb-local-complete-intersection-over-field` now records the exact
existing `AlgebraicGeometry.IsLocalCompleteIntersectionOver` declaration. The theorem
node that happens to contain its source is no longer a statement dependency.
Every theorem has proof `by sorry`; the definitions have fully specified data. There is
one postponed theorem and its docstring gives all ten steps of the accepted DAG proof.
No mathematical statement correction or disputed statement is needed. The repair changes
DAG definition ownership and separates the helpers; the main theorem signature and its
sorry proof are byte-for-byte the ones reviewed at immutable head 112331191ff2.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes P,T and their morphism: `{P T : Scheme.{u}} (g : P ⟶ T)`.
- Flat and locally finitely presented: `[Flat g] [LocallyOfFinitePresentation g]`.
- A nonnegative integer d: `(d : ℕ)`. No finiteness or nonemptiness assumptions on P,T.
- The scheme lci notion uses the existing `IsLocalCompleteIntersectionOver`. It is
  literally an affine-open cover by spectra of finite-type lci algebras, with the
  displayed maps compatible with the specified field structure morphism.
- Syntomic plus fixed relative dimension is the helper
  `Scheme.Hom.IsSyntomicOfRelativeDimension`: flat, locally finitely presented, and
  every geometric fibre lci and `Scheme.IsPureDimension d`. Pure dimension already
  holds vacuously for empty schemes, so testing every fibre is exactly the node's
  formulation testing every nonempty fibre. These are schemes `pullback g t`, not
  sets of geometric lifts. As in the existing affine criterion, all algebraically
  closed fields and all `Spec Ω → T` are tested. For a locally finitely presented
  morphism this agrees with the chosen-algebraic-closure formulation in the geometric
  fibre dependency, by field-change invariance. In particular it includes each
  chosen algebraic closure of a residue field; no closure of κ(x) is substituted.
- An open subscheme U is `U : P.Opens`, with its actual open immersion `U.ι` and
  scheme `U.toScheme`. Its restricted structural morphism is `U.ι ≫ g`.
- Largest open: `IsGreatest {U | (U.ι ≫ g).IsSyntomicOfRelativeDimension d}
  (g.syntomicFixedDimensionOpen d)`. The candidate is concretely the `sSup` of this
  set of opens. IsGreatest asserts both its membership in that set and largestness.
- Formation under every base change: the equality of
  `(pullback.snd g b).syntomicFixedDimensionOpen d` and the inverse-image open
  `(pullback.fst g b) ⁻¹ᵁ (g.syntomicFixedDimensionOpen d)` for every `T'` and `b`.
  The inverse-image open represents the actual fibre product of the open immersion
  with T', so this is exactly L_d(g_T') = L_d(g) ×_T T'.
- Geometric-fibre union: for each algebraically closed Ω and each t, the inverse
  image of the locus is the supremum of all opens O in `pullback g t` for which
  `IsLocalCompleteIntersectionOver Ω O.toScheme (O.ι ≫ pullback.snd g t)` and
  `O.toScheme.IsPureDimension d` hold. Suprema in Opens are open unions.
- Smooth neighbourhood inclusion: every x admitting an open H containing it and
  `SmoothOfRelativeDimension d (H.ι ≫ g)` belongs to the locus. No global smoothness
  or purity of the original family is assumed.
- Closed-point test: for every such Ω,t and c in `closedPoints` of the fibre,
  membership in the inverse-image open is equivalent to the conjunction of the
  displayed completed-algebra presentation and Krull dimension d.
- The completed local ring is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal ((pullback g t).presheaf.stalk c))
  ((pullback g t).presheaf.stalk c)`, the maximal-ideal completion of the actual stalk.
- Its complete-intersection Ω-algebra presentation has finite numbers r,s, relations
  `h : Fin s → MvPowerSeries (Fin r) Ω`, regularity
  `RingTheory.Sequence.IsRegular ... (List.ofFn h)`, and every h_i in the variable
  ideal `Ideal.span (Set.range (fun j ↦ MvPowerSeries.X j))`. Over a field this is the
  maximal ideal. It then has a ring isomorphism from the quotient by these relations
  to the completion, with the explicit equation for every a : Ω identifying the
  quotient's scalar map with constants on Spec Ω, the actual structure morphism's
  stalk map, and the completion map. This is exactly a compatible Ω-algebra
  isomorphism, not an unspecified abstract ring isomorphism or coefficient section.
- Krull dimension is `ringKrullDim` of that completion, equal to `(d : WithBot ℕ∞)`.

Dependency declarations reused:

| Module | Declaration(s) |
| --- | --- |
| Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| WeilConjectures.RingTheory.CompleteIntersectionOverField | Algebra.IsGlobalCompleteIntersection, Algebra.IsLocalCompleteIntersection |
| Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback, pullback.fst, pullback.snd |
| Sheaf.AlgebraicGeometry.PureDimension | AlgebraicGeometry.Scheme.IsPureDimension |
| Mathlib.Algebra.Field.Defs | Field |
| Mathlib.FieldTheory.IsAlgClosed.Basic; AlgebraicClosure | IsAlgClosed, AlgebraicClosure (closure only in the proof plan) |
| Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.SmoothOfRelativeDimension |
| Mathlib.Topology.JacobsonSpace | closedPoints |
| Mathlib.RingTheory.AdicCompletion.Basic; Algebra | AdicCompletion, its canonical algebraMap |
| Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| Mathlib.RingTheory.MvPowerSeries.Basic | MvPowerSeries, MvPowerSeries.X |
| Mathlib.RingTheory.Regular.RegularSequence | RingTheory.Sequence.IsRegular |
| Mathlib.AlgebraicGeometry.OpenImmersion | AlgebraicGeometry.IsOpenImmersion (inside the reused scheme-lci predicate and Opens.ι) |
| Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion | AlgebraicGeometry.IsLocalCompleteIntersectionOver |

The existing declaration `IsLocalCompleteIntersectionOver` is now owned by new
definition node `def-sfb-local-complete-intersection-over-field`, recorded with
`existing: true`. It is imported transitively through the new helper definition module.
The existing theorem module remains the physical source container of that declaration;
its affine-criterion theorem is not used in either the definition node or this theorem
statement. No existing node or declaration was rewritten or restated. All modules of already-stated proof dependencies are
imported privately, including the five dimension and completion modules, the syntomic
locus, local-ring criterion, CM stalks, field-change criterion, formal presentation and
kernel test. The Mathlib proof leaves are supplied by Flat, FinitePresentation,
QuasiSeparated, PullbackCarrier, FiniteType/AffineScheme and AlgClosed.Basic.

Edge cases checked before drafting and rechecked against the final statement:

- Empty source: the top open is empty, all geometric fibre conditions and smooth and
  closed-point tests are vacuous. The empty affine cover is available in the existing
  scheme-lci definition. Empty fibres impose no condition for any d.
- d=0 and r=s=0: Spec Ω has the empty regular sequence, power series in zero variables
  is Ω, and completed Krull dimension is zero. No positivity assumptions occur.
- An Artinian lci such as Ω[ε]/(ε²) is allowed at d=0; smoothness is not required.
- A disjoint line and plane over Ω separates into its d=1 and d=2 opens; no global
  equidimensionality of P or of its unreduced geometric fibres is assumed.
- A generic point of A¹ has local ring dimension zero but local topological dimension
  one. The completion criterion is expressly limited to closed points, so it does not
  make the false generic-point assertion.
- The nodal curve Ω[x,y]/(xy) is permitted at d=1, with the regular single equation xy
  in the formal power series ring. No regularity of the fibre is imposed.
- Arbitrary base change includes identity, empty source/base changes, inseparable and
  transcendental field extensions. No separability, finite-type or flatness assumption
  is made on b. All schemes and coefficient fields use the common universe u of the
  existing scheme category; no smaller independent test-field universe is introduced.
- Scalar compatibility uses the original Ω structure and works in every characteristic.

Searches (prescribed msearch.py, plus direct source rg):

1. LeanFinder, query `largest syntomic locus of fixed relative dimension flat locally
   finitely presented scheme morphism commutes with base change`: eight hits, including
   smooth relative-dimension base change and universal openness of flat lfp maps; none
   states the syntomic fixed-dimension locus theorem.
2. Loogle, query `AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.Flat`:
   zero hits.
3. Mathlib grep, query `[Ss]yntomic|[Ll]ocalCompleteIntersection` in AlgebraicGeometry:
   zero hits.
4. LeanSearch, query `syntomic locus fixed relative dimension largest open base change`:
   eight hits, smooth/standard-smooth base-change facts, smooth locus and etale
   base-change; no exact match.
5. Direct rg across lean/WeilConjectures, lean/Sheaf and Mathlib for
   `SyntomicOfRelativeDimension|syntomicFixedDimensionOpen|syntomic_fixed_dimension_locus`:
   no existing declarations. Direct rg for syntomic and lci found
   `IsLocalCompleteIntersectionOver` in the existing affine-criterion module, which
   this delivery imports and cites instead of recreating that notion.
6. Direct rg of the item id in lean/WeilConjectures: no existing attachment. The Sheaf
   source has consumer proof-plan mentions but no statement of this theorem.
7. Direct rg for completed-local scalar constructions found nodal helpers. The theorem
   states scalar compatibility inline with existing StructureSheaf.toStalk, stalkMap
   and algebraMap, without defining another canonical completion or scalar map.

Sources read: the node and every statement dependency, including full recorded Lean
signatures/docstrings and Mathlib match records; Stacks morphisms.tex labels
lemma-set-points-where-fibres-lci, lemma-flat-finite-presentation-CM-fibres-relative-dimension,
lemma-syntomic-relative-dimension, lemma-base-change-relative-dimension-d,
lemma-syntomic-flat-fibres; varieties.tex lemma-dimension-locally-algebraic;
more-algebra.tex lemma-completion-dimension; dpa.tex lemma-quotient-regular-ring and
lemma-check-lci-agrees; algebra.tex lemma-lci-at-prime. The example module is withdrawn,
so its node's current upstream CompactObject module was also read.

Validation: scompile.py compiles both its sandbox probe and the actual library module
cleanly (4.8 s and 1.9 s in the first successful run). The earlier compiler errors were
solely ambiguous coercions in the closed-point binder and closedPoints argument; these
were repaired by explicitly specifying Scheme.{u} and its point-type coercion.
No local build, live-source edit, direct Git command, or other agent was used.

## Second reading by Q65

A separate final reading compared each node clause with the module, including both
helper definitions. IsGreatest supplies existence and maximality; the base-change clause
is equality of opens along the correct first projection and uses the second projection
as structural morphism; the geometric union uses the actual restricted structure map;
smoothness is imposed only on a neighbourhood. The closed criterion uses closed points
of the fibre, not closed points of the total source, and the dimension belongs to the
completed stalk. Its ring equivalence is made an Ω-algebra equivalence by the scalar
condition; r and s and the empty sequence are unrestricted natural numbers. Empty fibres
remain allowed. The use of the existing lci predicate is now recorded through its new definition-node
owner, not the affine-criterion theorem. Both helpers have their own definition-node
owner and module, and the item imports that definition module. No further mathematical mismatch was found. This reading was performed
in this session under the dispatcher's prohibition on starting other agents; the
maintainer's independent delivery review remains separate.


## Repair of returned head 112331191ff2

H2 is repaired using the explicitly authorized new §1(A) definition-node option:
`def-sfb-local-complete-intersection-over-field` owns the exact existing plain predicate
`AlgebraicGeometry.IsLocalCompleteIntersectionOver`, with an `existing: true` binding.
This uses the rule in brief-stage2 §1(A)/§5 for existing declarations lacking a definition
node; it does not introduce a duplicate definition or record the affine-criterion theorem
as a statement prerequisite. The existing `def-trf-local-complete-intersection-scheme-over-field`
records only `IsLocalCompleteIntersectionOverExtension`, as the return observes, and its
Lean record remains untouched. The new definition node states exactly the plain affine
cover predicate: finite type lci algebras, open immersions, compatibility with the given
field structure, and joint surjectivity. Empty schemes/covers are explicitly allowed.

The advisory is also addressed: `IsSyntomicOfRelativeDimension` and
`syntomicFixedDimensionOpen` were moved without changing their signatures or bodies into
`Sheaf.AlgebraicGeometry.SyntomicFixedDimensionOpen`, owned by the new definition node
`def-sfb-syntomic-fixed-dimension-open`. The main module replaces its public import of
`Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion` with the new definition module.
The latter imports the existing predicate's source container solely to reuse the plain
definition recorded by its new owner. Its dependency node is the new lci definition node;
there is no DAG statement dependency on the affine-criterion theorem. Both new definition
nodes are in the item's chapter and have the prescribed ancestor/via metadata and fields.

Comparison against current main: all original fields of the item other than lean and
stmt_deps match the current live node. The previously added theorem statement dependency
is replaced by the two definition nodes. No correction record is warranted because the
mathematical statement, every original statement dependency, and the accepted proof remain
unchanged. The delivery wrapper refreshes and rebases onto current main during dry-run and
push; no direct Git command is used.

Fresh searches: LeanSearch query `scheme locally complete intersection over a field affine
open cover and largest syntomic fixed relative dimension open` returned eight generic
affine-cover/Noetherian facts; LeanFinder query `local complete intersection scheme over a
field; syntomic morphism of fixed relative dimension locus` returned eight smooth/standard
smooth facts; prescribed Mathlib grep of `IsLocalCompleteIntersectionOver|IsSyntomicOfRelativeDimension|syntomicFixedDimensionOpen`
returned zero hits. The raw search results, including timestamps and returned names, are
recorded verbatim in both new nodes' mathlib_searches. Direct rg of the live project's
WeilConjectures and Sheaf sources found only the existing plain predicate and its
OverExtension wrapper, and no live fixed-dimension helpers. DAG inspection confirmed no
definition node records the plain predicate. `blueprint_refs.py search 'local complete
intersection'` returned zero blueprint nodes; `ancestor` returned None, matching the
item's inherited metadata. Sources re-read: morphisms.tex Tag 01UG, Tag 02K1 and
`definition-syntomic-relative-dimension`; algebra.tex Tag 00S9. No theorem conclusion is
needed to give either definition's data.

The repeated edge-case review gives exactly the prior outcomes. In particular the helper
property includes empty fibres through the existing pure-dimension convention, the
candidate is defined for arbitrary g (flatness and lfp are conditions on its competing
opens), and no existence theorem supplies its data. The main theorem still has all five
conjuncts and the same closed-point scalar compatibility and completion dimension.

## New nodes

`def-sfb-local-complete-intersection-over-field` gives the requested definition-node owner
to the exact existing `AlgebraicGeometry.IsLocalCompleteIntersectionOver`. It has no new
Lean file: its existing:true record points to the actual declaration in
`Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion`, signature read at lines 51–52.
The source is Stacks Tag 01UG and algebra Tag 00S9. Its statement spells out the family I,
the algebras A_i with Algebra and FiniteType data, open-immersion maps φ_i, compatibility
φ_i ≫ s with the scalar-induced Spec map, joint surjectivity, and each A_i's lci property.
These match every binder and clause of the reused definition. This node fills the precise
ownership gap identified in the return; it does not create a second Lean notion. The
older extension definition node owns a different declaration. The search results above
and the raw records in this new node substantiate the distinction.

`def-sfb-syntomic-fixed-dimension-open` owns the property and candidate open previously
introduced as helpers in the theorem module. Its real definition module uses the existing
plain scheme-lci predicate, Flat, LocallyOfFinitePresentation, pullback, pure dimension,
and actual source Opens. The geometric-field quantifier and the restriction map U.ι ≫ g
are unchanged; the candidate data is literally the same sSup. Stacks' definition following
Tag 02K1 gives syntomic relative dimension; Tags 01UF, 02V3 and 02NM support the geometric
formulation and the candidate union used by the main theorem. The node states the union
as a definition and asserts no maximality or base-change theorem. Searches found no live
definition of either helper. The module has no theorems or sorry, and both helper docstrings
carry this owning definition node's blueprint tag.


Repair validation: both delivered Lean modules compiled successfully via the prescribed
scompile.py wrapper. The first dry run found only a signature-record formatting defect:
the extractor begins at `def`, omitting the preceding `noncomputable` modifier. The new
helper node's lean.statement was normalized to the extractor's exact signature; the
actual definition retains `noncomputable` in its source. Its two combined bracket citations
were also separated to satisfy the citation reader. Neither change alters Lean content
or mathematics. All original theorem clauses and the new definition-node mappings were
re-read after these metadata repairs.
