## Worker report

The module `Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts` states
`AlgebraicGeometry.properPerfect_rightAdjoint_preservesCoproducts`, with its only proof
`sorry`. No definition, additional node, dependency module, or statement correction is needed.
Source checked directly: https://stacks.math.columbia.edu/tag/0A9R, Lemma 48.13.1,
including the compactness/adjunction calculation and perfect-generator conclusion.
The local literature checkout is absent on this machine.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`; Noetherian on both:
  `[IsNoetherian X] [IsNoetherian Y]`. These are Noetherian schemes, not merely locally
  Noetherian schemes. The same scheme universe entails no restriction: both can be
  placed in their common universe.
- Morphism f and properness: `(f : X ⟶ Y) [IsProper f]`. Mathlib's universally-closed
  hypothesis supplies quasi-compactness, so its locally-finite-type clause is the
  finite-type clause of the dependency node.
- Perfectness, explicitly defined in the item as finite Tor dimension at every stalk:
  `hTor : ∀ x : X, ∃ n : ℕ, ∀ N i, n < i → IsZero (...)`.
  The first input of `Tor` is the source stalk as a module over the target stalk,
  obtained by `ModuleCat.restrictScalars (f.stalkMap x).hom` from its regular module.
  The second input N ranges over every module over the target stalk. Bounds may
  depend on x and precede both N and i; no flatness or finite projective dimension
  assumption is substituted. For modules concentrated in degree zero, negative Tor
  degrees vanish automatically; this is exactly finite Tor dimension.
- The parenthetical relative perfectness clause explains this finite-Tor hypothesis;
  it is not absolute perfectness of O_X as an O_Y-module. No additional hypothesis
  using `Scheme.IsPerfect` is imposed. The recorded perfect-complex definition and
  docstring were read, but its predicate is not needed to type this theorem.
- D_QCoh on each side: the recorded `schemeDerivedQCohCategory X` and
  `schemeDerivedQCohCategory Y`. The `HasDerivedCategory` binders select localization
  models of the shared O_X-module categories, not additional geometric assumptions.
- Rf_* on these subcategories: `R` together with `eR` identifies
  `R ⋙ (schemeDerivedQCohProperty Y).ι` naturally with
  `(schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f`.
  This is representation data for the restriction of the recorded ambient functor.
  It neither substitutes arbitrary pushforward nor assumes preservation of sums.
  Every restriction has such data; fullness makes any two such restrictions naturally
  isomorphic, so the choice does not strengthen the mathematical hypothesis.
- Right adjoint c: `c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X`
  and `adj : R ⊣ c`. No particular choice of right adjoint is required.
- All set-indexed families and the canonical map being an isomorphism:
  `∀ I : Type v, PreservesColimitsOfShape (Discrete I) c`. A diagram of discrete
  shape is exactly a family; its colimit is its direct sum. Mathlib's
  `PreservesCoproduct.of_iso_comparison` and the instance
  `IsIso (sigmaComparison G f)` in Limits/Preserves/Shapes/Products.lean show both
  directions of equivalence with the item's canonical comparison. Its defining
  equation is `Sigma.ι _ j ≫ sigmaComparison c K = c.map (Sigma.ι K j)`.
  No chosen coproduct structures or finite/countable-index restriction are added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and the induced local ring map `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.DerivedCategory` (imported via SchemeDerivedDirectImage):
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`,
  `schemeDerivedQCohCategory` and their full-subcategory inclusion `.ι`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: the full signature and docstring of
  `AlgebraicGeometry.Scheme.IsPerfect` were read. It is an explanatory/proof notion
  here, not a separate object/hypothesis of the item; consequently no unused import.

Mathlib supplies `ModuleCat.restrictScalars`, `Tor` (left-derived tensor in its second
variable), `IsZero`, `Adjunction`, and `PreservesColimitsOfShape`. ModuleCat's projective
resolutions and tensor category instances are imported, so no Tor or finite-Tor
predicate is privately defined.

Edge cases checked before writing: the empty index type is allowed and expresses
preservation of the zero coproduct; zero complexes and arbitrary unbounded complexes
are allowed in the full quasi-coherent derived categories; empty X or Y is not
excluded, and `hTor` is appropriately vacuous on empty X. The n=0 Tor bound is
allowed (flat morphisms are included), and no characteristic assumption is present.
The index universe v is arbitrary and independent; the theorem preserves coproducts
whenever they exist at that size, and makes no artificial existence assumption for
sets too large for a chosen category model. Standard set-sized coproducts in D_QCoh
are the mathematical direct sums in the source.

Searches (all service searches run through the required msearch.py, with results
recorded in searches.jsonl):

- LeanSearch: `right adjoint of derived pushforward proper perfect morphism preserves
  coproducts`: unavailable, Internal Server Error.
- LeanFinder, same query: eight results concerning underived module pushforward,
  site pushforward and reflective categories; none states the item.
- Loogle: `CategoryTheory.Limits.PreservesColimitsOfShape`: twelve hits for the
  generic preservation API, none for this geometric theorem.
- Mathlib grep: `flatDimension|FlatDimension|FiniteTor|TorDimension`: zero hits.
- Mathlib CategoryTheory grep:
  `rightAdjoint.*(Coproduct|coproduct)|proper.*perfect|sigmaComparison`: twelve hits
  for the generic coproduct comparison and preservation equivalence, no geometric
  theorem. Opened the relevant comparison and preservation signatures/docstrings.
- Source/project rg for finite-Tor, proper-perfect, right-adjoint coproduct names,
  and the item id: existing scheme finite-Tor notions concern derived O_X-complexes,
  not this relative stalk module condition; source hits concern constructible
  etale/pro-etale coefficients and perfect fields. No duplicate statement.
- Exact proposed declaration name searched in Mathlib/source/project name records:
  no existing declaration. The blueprint item id search in WeilConjectures has no hit.

No STATEMENT-DISPUTED flag or node fault found. The declaration docstring carries
all three DAG proof steps, including orthogonality to every shift and the cone test.
Server scompile.py: compiled in 2.3 seconds, exit code 0, no warnings or errors.

## Second reading by H1

Independent second reader opened the item JSON, its entire Lean module, all five
statement-dependency nodes and the declarations they record. No mismatch was found;
the Lean module and node record are unchanged. No new nodes, dependency modules,
or statement correction are present.

Source: the Stacks duality.tex fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/duality.tex into the
item's scratchpad (the local literature checkout is absent), section
section-perfect-proper, lemma-proper-flat-noetherian, Tag 0A9R. The preceding section
text mentions the possible qcqs generalization, but the lemma itself assumes
Noetherian schemes. Its statement and proof agree with the node. The source's
chosen right adjoint can be replaced by any right adjoint by uniqueness up to natural
isomorphism. No smoothness, flatness, base field or characteristic is assumed.

Object/hypothesis/conclusion checklist, with verdicts:

1. Schemes X and Y: `{X Y : Scheme.{u}}` uses the recorded Mathlib Scheme and
   Scheme.Hom, not affine schemes or ringed spaces substituted for schemes. Pass.
2. Both schemes Noetherian: `[IsNoetherian X] [IsNoetherian Y]`. Opened Mathlib
   Noetherian.lean: IsNoetherian extends IsLocallyNoetherian and CompactSpace,
   exactly Noetherian, not just locally Noetherian. Pass.
3. Morphism f proper: `(f : X ⟶ Y) [IsProper f]`. Read Proper.lean and the
   dependency node; IsProper extends separated, universally closed and locally
   finite type. Universally closed supplies quasi-compactness, hence finite type.
   No extra flatness or smoothness. Pass.
4. Finite Tor dimension at each source point: `hTor : ∀ x : X, ∃ n : ℕ, ∀ N i,
   n < i → IsZero (...)`. Mathlib Scheme.Hom.stalkMap has direction
   O_Y,f(x) → O_X,x. ModuleCat.restrictScalars applied to ModuleCat.of O_X,x O_X,x
   gives exactly the source local ring as a target-local-ring module.
   Opened Tor.lean: Tor left-derives tensoring with this module in the second
   variable; N ranges over target-stalk modules, and IsZero is module vanishing.
   The bound precedes N and i and may depend on x; this matches the node exactly.
   Natural-number degrees suffice for a degree-zero module, whose negative Tor
   degrees vanish. No finite generation of this module over O_Y,f(x) is asserted.
   Pass.
5. Quasi-coherent unbounded derived categories: `schemeDerivedQCohCategory X/Y`.
   Read DerivedCategory.lean: the shared O-module category is localized at
   quasi-isomorphisms and its full subcategory requires quasi-coherence of every
   integer-degree cohomology sheaf. The HasDerivedCategory binders choose category
   models and impose no extra geometric restriction. Pass.
6. Rf_* on those subcategories: R and eR identify R followed by the full-subcategory
   inclusion with the shared schemeDerivedDirectImage f preceded by inclusion.
   Read SchemeDerivedDirectImage.lean and RingedSpaceDerivedDirectImage.lean:
   this is unbounded right-derived module direct image, computed by K-injectives.
   eR is representation data, not an assumption that an arbitrary functor is the
   desired pushforward. A qcqs proper morphism has the required restriction.
   Fullness gives a unique restriction up to natural isomorphism. Pass.
7. Its right adjoint: c has direction D_QCoh(Y) → D_QCoh(X) and `adj : R ⊣ c`.
   No assumption that c already preserves sums. Pass.
8. Every set-indexed family and canonical comparison an isomorphism:
   `∀ I : Type v, PreservesColimitsOfShape (Discrete I) c` quantifies over all
   discrete diagrams/families of this size. Read Products.lean:
   PreservesCoproduct.of_iso_comparison and the converse IsIso sigmaComparison
   instance identify preservation with invertibility of the canonical map
   ⨁ c(K_j) → c(⨁ K_j). Preservation uses existing colimit cocones, so it does
   not add an unwarranted existence hypothesis for oversized sets. Pass.
9. The parenthetical perfect-complex clause is explanatory relative perfectness.
   Opened Scheme.IsPerfect and IsStrictlyPerfect in PerfectComplex.lean; these
   describe absolute perfect complexes on one scheme and are proof notions here,
   not an additional hypothesis that the source stalk is finite projective over
   the target stalk. Pass.

Edge cases: I can be empty (preservation of the zero coproduct), finite, infinite,
or in any index universe v. Zero and unbounded derived objects are included.
Empty schemes are allowed and hTor is vacuous for empty X; no point or nonemptiness
binder is introduced. The n=0 bound includes flat morphisms, but Tor_0 is not forced
to vanish. The stalk rings remain arbitrary commutative local rings; characteristic
zero, positive characteristic and mixed characteristic are all covered. Scheme
universe u is arbitrary and both schemes may be placed in a common universe;
wX and wY independently select derived-category Hom universes. Testing u-sized
modules detects finite flat/Tor dimension; cyclic test modules already have this
size, so the stalk-module binder imposes no smaller testing universe than the ring.
All universes and variables are explicitly bound.

Independent searches through msearch.py, using different wording:
- LeanSearch: `proper perfect pushforward right adjoint coproduct preservation`:
  unavailable (Internal Server Error); no semantic no-match verdict inferred.
- LeanFinder: `compact generators adjunction right adjoint preserves arbitrary
  coproducts`: eight hits, for general adjoint-functor theorems, presentability,
  evaluation and condensed categories, none for this geometric statement.
- Loogle: `CategoryTheory.Tor`: four hits; opened Tor and confirmed its tensor
  order/left-derived construction rather than introducing a private Tor notion.
- rg of Mathlib, WeilConjectures and lean/Sheaf for right-adjoint/coproduct and
  direct-sum phrases, Tag 0A9R, the item id and proposed declaration name found
  no copy of this theorem. Opened nearby QCqsDerivedDirectImageRightAdjoint and
  DerivedDirectImagePreservesDirectSums: the former establishes existence of the
  right adjoint, the latter preserves sums for pushforward itself, neither is
  preservation by the right adjoint. General Brown representability/pre-derived
  adjunction and pro-etale exceptional-adjoint hits are different statements.
- FiniteTorDimension and LocallyFiniteTorDimension were opened: their predicates
  concern absolute derived O_X-complexes, not the relative stalk module of f.
  They cannot replace hTor. Source finite-Tor hits concern module derived objects
  and etale/pro-etale coefficient categories; no relative scheme-morphism notion
  duplicating the hypothesis was found. The upstream name record has no duplicate.

H5/H6/H8/H9: no definitions or local notation/instances were added. The only theorem
has proof `by sorry`. Its source/docstring names the item and carries all three
proof steps: perfect direct image and compactness, the adjunction Hom calculation,
and orthogonality of the cone to all shifts followed by perfect generation.
All lines satisfy the 100-character limit. The JSON lean.statement was checked
verbatim against the file's complete signature by a string-equality assertion.

Validation: the required scompile.py invocation from the sandbox failed before
Lean ran: SSH to the project server timed out during banner exchange (exit 255).
The first invocation used a repository-relative path and was corrected to run in
the sandbox. Remote validation is being retried; the prior worker compile is not
used as this reader's validation.

Retry: scompile.py succeeded, exit 0, compiled in 2.2 seconds with no errors or
warnings. The transient SSH failure is resolved. No Lean/node repair was necessary;
this second reading added only the independent review and validation record.
