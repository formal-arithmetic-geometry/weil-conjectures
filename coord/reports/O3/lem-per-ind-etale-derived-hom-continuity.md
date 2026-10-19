## Worker report

The module `Sheaf.AlgebraicGeometry.IndEtaleDerivedHomContinuity` states
`AlgebraicGeometry.Etale.indEtaleDerivedHomContinuity`. All theorem proofs are `sorry`;
all complex, functor, cocone and comparison-map data are actual constructions.
The item's natural statement is unchanged.

Hypotheses and clauses, in the order of the node:

- The qcqs base scheme is `(X : Scheme.{u}) [CompactSpace X]
  [QuasiSeparatedSpace X]`.
- The finite field is `(A : Type (u + 1)) [Field A] [Finite A]`.
  Coefficients use the recorded ordinary fixed-ring sheaf encoding
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`. On the pro-etale site the
  coefficient realization of `ProEtaleFiniteModules` identifies fixed-ring module
  sheaves with modules over the specified sheafified continuous-function ring.
  There is no completion or condensed replacement.
- The small cofiltered presentation is `{I : Type u} [SmallCategory I]
  [IsCofiltered I] (D : I ⥤ X.Etale)`, with affine objects and affine transitions
  specified by the two dependent `IsAffine`/`IsAffineHom` instances. The category
  of etale objects retains its actual structure morphisms `j_i = (D.obj i).hom`.
  Finitely presented is automatic here: etale is locally of finite presentation;
  each source is affine, and the target is quasi-separated, giving the requisite
  quasi-compactness and quasi-separatedness of the structure morphism. There is
  consequently no added finite-presentation instance that merely restates a
  derived consequence of these hypotheses.
- The limit is the actual cone `c : Cone (D ⋙ Scheme.toProEt X)`. `_hc` says that
  the underlying scheme cone is a limit. Thus `U = c.pt.left`, `j = c.pt.hom`,
  and the maps to the stages are exactly `(c.π.app i).left`. Presenting U as a
  pro-etale object just supplies the structure that is automatic for this
  affine-etale limit and is needed for the first expression's slice.
- `L : DerivedCategory.Plus (...)` is exactly the bounded-below condition.
  `K : DerivedCategoryModule A X` with
  `_hK : DerivedCategory.isBoundedConstructible A X K` uses the recorded finite
  stratification/finite module-value constructibility, not the upstream
  finite-Tor or site-perfect predicate.
- `J`, `a`, the strictly-GE and termwise-injective instances, and `e : Q.obj J ≅
  L.obj` are arbitrary bounded-below injective representative data for L.
  This quantifies over a model of an already assumed object, not over a new
  mathematical class of L. Such representatives exist for every L in D-plus.
  The first comparison is asserted for every such model.
- The first displayed comparison is
  `IsIso (ProEtale.affineContinuityProEtaleMap D c L.obj J e)`. Its source is Q of
  the degreewise colimit of the strict section diagram `J(U_i)`. Its target is
  derived evaluation of the comparison inverse image at `c.pt`, precisely
  derived sections in the pro-etale slice over U. The recorded affine-continuity
  theorem also identifies each stage section complex with its stage derived
  sections. Its map is the actual comparison unit followed by section restriction
  and the derived-evaluation unit.
- The second comparison is `IsIso (indEtaleGlobalHomMap D c K L.obj)`. The strict
  complex in degree n is the actual A-module `Hom(j_i* K, j_i* L[n])`, with zero
  differential. The cocone has limit vertex `Hom(j* K,j* L[n])` degree by degree.
  Its maps are the already recorded `boundedConstructibleDerivedHomPullback`,
  including the actual exact inverse-image functor, its composition comparison,
  and `commShiftIso`. The comparison is Q applied to `colimit.desc` of this
  constructed cocone; no map, comparison isomorphism, or equivalence is an input.
- Why this states an isomorphism of global derived Hom complexes: over the
  *field* A, every complex of A-modules splits into its cohomology complex plus
  a contractible complex. Homology is fully faithful on D(A), so the graded Hom
  complex is a model of global RHom naturally in both variables. This identification
  is itself stated, with `sorry`, as `indEtaleGlobalHom_model`, a natural
  isomorphism with the existing `Etale.derivedHom` followed by
  `Etale.rightDerivedGlobalSections`. Its proof docstring explains the injective
  Hom-complex calculation and splitting argument. The comparison map uses none
  of the arbitrary choices of splittings: its cohomology maps are actual pullback.
  This construction would not express global RHom over general coefficient
  rings; the main statement retains exactly the finite-field hypothesis.
- Derived filtered colimits are represented by degreewise colimits of the strict
  complex diagrams. Exactness of filtered module colimits makes this precisely
  the derived colimit, for the section model as well as the Hom model.
- Naturality in both Hom variables is implemented by
  `indEtaleGlobalHomBifunctor`: precomposition by the pulled-back source morphism
  and postcomposition by the shifted pulled-back target morphism. The restriction
  maps use the same functor. Identity and composition coherence are separately
  stated by the two `indEtaleGlobalHomPullback_*` theorems; they give the actual
  diagram and cocone laws. Pullback of composition gives evaluation compatibility,
  including evaluation against a section (a morphism out of the constant unit).
  Naturality and evaluation compatibility are explicitly stated by
  `indEtaleGlobalHomPullback_naturality` and
  `indEtaleGlobalHomPullback_evaluation`. Neither comparison is an arbitrary
  isomorphism between two objects.
- No cohomological-dimension, Noetherian, upper bound on L, constructibility of L,
  finite-Tor, or local projectivity assumption occurs in the main theorem.

Dependency declarations read and reused:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, Mathlib `DerivedCategory.Plus`, and the homology
  functors (the missing local upstream source was read with `scompile.py --source`).
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  fixed-coefficient module categories, `finiteCoefficientRealization`, its exact
  equivalence, and `finiteCoefficientDerivedComparison`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: `RingHom.IndEtaleAcrossUniverses`
  and its public import's existing ind-etale affine-limit vocabulary.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `Scheme.AffineProEt`, its inclusion `toProEt`, and its induced topology.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and its full subcategory.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and its module adjunction, whose left adjoint
  is the actual Kan-extension/sheafification comparison functor.
- `Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity`:
  `affineContinuityProEtaleMap` and its strict section construction; this is the
  already recorded proof dependency `det-sf-comparison-affine-continuity`.
- `Sheaf.TraceFormula.BoundedConstructibleDerivedHomContinuity`:
  `boundedConstructibleDerivedHomPullback` and its composition/shift formula.
  Its concrete map definitions are carried by the new definition node
  `def-per-derived-hom-pullback`; the theorem is kept in proof dependencies. The theorem in that module, which has additional
  boundedness and Noetherian hypotheses, is *not* used to assert this item.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom` and `.GlobalSections`:
  `Etale.derivedHom` and `Etale.rightDerivedGlobalSections`, which are the actual
  global derived Hom object in the model-identification theorem.

The remaining recorded proof-dependency modules are imported privately, following
the nine-step finite-affine-syzygy/Postnikov proof in the main theorem's docstring.
Canonical-map helpers belong to this node's own comparison construction and are
listed in `lean.declarations`; no independent notion or dependency is restated.

Edge cases checked: cofiltered includes nonempty, so no false empty-presentation
case is silently admitted. Arbitrary small categories, not only directed posets,
are quantified. A constant one-stage diagram and identity projection yield the
ordinary identity comparisons (the unit coherence is explicit). Empty schemes
and zero K or L give zero section/Hom complexes. Every integer shift n is retained,
including negative degrees and arbitrarily high positive degrees. L may be
unbounded above and have nonconstructible cohomology. All finite fields and
characteristics are allowed. Scheme, site and coefficient universes agree with
the recorded ordinary coefficient convention; there is no equality of independent
site-object and site-morphism universes. No statement fault or dispute was found.

Searches before writing (all through the prescribed search wrapper or read-only rg):

- LeanFinder: "Derived sections and global derived Hom of constructible etale
  sheaves commute with inverse limits of affine etale schemes": 8 hits, all scheme
  limit/global-section facts, no derived Hom continuity theorem.
- Loogle: `IsCofiltered, IsIso`: no hits, unknown identifier IsCofiltered.
- Mathlib grep: `([Ee]tale|[Pp]roetale).*([Cc]ontinuity|[Hh]om)|[Cc]ontinuity.*[Dd]erived`:
  24 hits in etale/pro-etale site and morphism files; no matching theorem.
- LeanSearch: "Derived Hom constructible etale sheaves inverse limit affine
  schemes continuity": 8 hits, including sheafHom and affine scheme limits,
  no matching theorem.
- rg in Mathlib, the source project and the side Lean library for Hom continuity,
  derived continuity, the item id, linearCoyoneda, HomComplex and derivedHom:
  found the recorded affine sections theorem and the bounded constructible Hom
  theorem described above, but no theorem with the requested bounded-below target.
- DAG/blueprint searches for "global derived Hom" and a split/zero-differential
  Hom model found no existing field-normalized etale restriction model. A further
  LeanFinder query asked for the field zero-differential derived Hom model.
- Read the actual cited Bhatt--Scholze PDF at Corollary 5.1.6, Lemmas 6.3.14 and
  6.3.16, and the neighboring Remark 6.3.15. The lower-bound restriction and absence
  of a uniform cohomological-dimension hypothesis agree with the node.

Validation is by `scompile.py` and then `deliver2.py --no-push`; final compiler and
preflight results are recorded below after the checks finish.

The nine postponed theorems are the main theorem, the global-Hom model
identification, the two general pullback laws, the two diagram laws, cocone
naturality, pullback naturality in both variables, and evaluation compatibility.
Each has a source/blueprint tag and a complete natural-language proof. These
state the node's canonical-map and naturality clauses and supply only proof
fields to the explicitly constructed maps and diagrams; no data is chosen
from a theorem with `sorry`.

The additional field-model LeanFinder query returned eight general Ext,
single-complex, and injective/projective derived-category facts, with no
matching global etale Hom model. The added map-provider statement dependency
was checked for a dependency path back to this item: none exists.

Final validation: `scompile.py` compiled both the sandbox probe (14.9 s) and the
module at its real library path (8.3 s), with no errors or non-sorry warnings.
`deliver2.py N3 lem-per-ind-etale-derived-hom-continuity --no-push` printed
`OK (dry run): commit 9026f244f6 passes the preflight and compiles; nothing pushed`.
That validation describes the returned packet. The repaired packet also contains the
two definition-node records described below.


## New nodes

`def-per-derived-hom-pullback` carries the existing definitions
`boundedConstructibleDerivedHom`, `boundedConstructibleDerivedHomCompIso`, and
`boundedConstructibleDerivedHomPullback` in the unchanged module
`Sheaf.TraceFormula.BoundedConstructibleDerivedHomContinuity`. Its statement gives
the Hom group, composition comparison, and full pullback formula, over an arbitrary
commutative ring and with no boundedness or constructibility restriction. Sources
are Stacks Tags 0149, 0D6D and 09YU, as in the existing definition docstrings.
The primary Lean signature is copied verbatim from the pullback definition.

`def-per-affine-proetale-continuity-map` carries the existing comparison map and
its strict section diagram, comparison unit, cocone and derived-evaluation helpers
in the unchanged module `Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity`. Its
statement gives the actual cocone-induced map, the derived evaluation unit and
normalization by the supplied representative isomorphism. Its source is the current
blueprint's affine-continuity formula and the reviewed strict-section specification.
The primary Lean signature is copied verbatim from `affineContinuityProEtaleMap`.
The definition needs neither a limit cone nor injectivity; the item's theorem
retains those hypotheses for its isomorphism conclusion.

For both new nodes, the three prescribed search kinds were run with the query
“Canonical pullback on shifted derived Hom of etale module sheaves and affine
proetale derived sections comparison map”: LeanSearch and LeanFinder each returned
eight general pullback facts, no exact definition; Mathlib grep of the two actual
declaration names returned no hits. Their exact JSON search outputs are retained
in each new node. Read-only rg found no upstream construction and found precisely
the two side modules. DAG and blueprint searches found the owning theorem records
and unrelated Hom/tensor definitions, but no definition node for these maps. Hence
these are existing:true records, with no new Lean module or duplicate definition.

## Returned-delivery repair

Repaired L's H2 ownership finding at immutable head 9e6cc8c69b86. The new definition
nodes replace the added theorem in the item's statement dependencies. Both
`det-sf-comparison-affine-continuity` and
`lem-trf-bounded-constructible-derived-hom-continuity` are in proof dependencies,
as explicitly requested by the return. The natural-language statement, all its
hypotheses and clauses, and the complete Lean module remain unchanged. Existing
item fields were refreshed from the current shared base before applying only these
authorized metadata repairs. No statement correction is involved.

## Repair self-check by N3

I reopened the item statement, complete Lean file, both existing helper definitions
and their docstrings. The main hypotheses and two IsIso conclusions match the
clause-by-clause Worker report above. The Hom definition record includes all three
plain definitions named in the return, including the composition comparison; the
section-map record includes the actual canonical map and its construction helpers.
Neither record attributes a plain definition to a theorem or chooses data from a
postponed theorem. The new nodes preserve the item's chapter, unit, blueprint
ancestor and via chain and cite only their defining notions. The empty/zero/identity
cases and the arbitrary small cofiltered indexing remain as previously reviewed.
This is a worker self-check; no independent reviewer was started by this worker.


## Repair validation and delivery-tool block

`scompile.py N3 lem-per-ind-etale-derived-hom-continuity` compiled the unchanged
module in the sandbox (5.6 s) and at its library path (5.8 s), cleanly. The repaired
`deliver2.py --no-push` printed `OK (dry run): commit 445eb2a078 passes the preflight
and compiles; nothing pushed`, staging the item module, item node, two new
definition nodes, and report. However, it also printed:

> note: lem-per-ind-etale-derived-hom-continuity: these fields differed in your copy and were NOT delivered (not yours to change): ['proof_deps']

That discards the explicit return instruction to keep both continuity theorems in
proof dependencies: the current base has det-sf-comparison-affine-continuity there
but lacks lem-trf-bounded-constructible-derived-hom-continuity. The sandbox includes
the requested addition. Read-only inspection of deliver2.py lines 119–132 confirms
that proof_deps is writable only for a statement correction, whereas this repair
changes no mathematical statement and must not invent a correction. Per the human
launcher-file instruction, no gate was patched or worked around and no push was
attempted. The retained packet is ready once the tool permits this explicitly
authorized metadata repair.


## Retried saved packet, 2026-10-18

As instructed on the retry, I first read this report and ran the saved packet
through `deliver2.py N3 lem-per-ind-etale-derived-hom-continuity --no-push`.
The wrapper compiled the delivery module and existing-declaration probe and printed
`OK (dry run): commit e1111a5592 passes the preflight and compiles; nothing pushed`.
It also again printed that `proof_deps` was NOT delivered (not yours to change).

A structured comparison with the current shared item shows only the intended
`lean` record, the two added definition-node statement dependencies, and the
addition of `lem-trf-bounded-constructible-derived-hom-continuity` to `proof_deps`.
The current base still lacks that theorem in `proof_deps`; the saved node has it.
Read-only inspection of the prescribed wrapper confirms that its field filter
(lines 118–132) allows `proof_deps` changes only when the mathematical statement
changes. This repair has no mathematical statement change and must not invent one.
The required metadata repair therefore remains absent from the built commit
despite the successful preflight. No launcher tool was modified or bypassed, and
no incomplete packet was pushed. The saved repair packet is retained unchanged.

## Saved-packet retry: dry run 568a1ad77b

On 2026-10-18 this retry began by inspecting the retained report and running the
prescribed `deliver2.py N3 lem-per-ind-etale-derived-hom-continuity --no-push`.
It compiled the two checked Lean files and passed server preflight, printing:

> OK (dry run): commit 568a1ad77b passes the preflight and compiles; nothing pushed

It again explicitly discarded `proof_deps` as “not yours to change.” A structured
comparison with the refreshed shared base confirmed that the saved packet differs
only in `lean`, the two requested new definition-node `stmt_deps`, and the required
addition of `lem-trf-bounded-constructible-derived-hom-continuity` to `proof_deps`.
The base already includes `det-sf-comparison-affine-continuity` in `proof_deps`.
The mathematical statement is identical. Read-only inspection of `deliver2.py`
confirmed that `proof_deps` is copied only when `statement` differs, so this
unchanged-statement repair cannot deliver the explicit return instruction through
the prescribed wrapper. No statement correction was invented, no tool was changed
or bypassed, and no incomplete packet was pushed. The complete repaired sandbox
packet remains retained for a wrapper fix or authorized base metadata repair.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
