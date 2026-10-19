## Worker report

The module `Sheaf.CategoryTheory.Sites.FiniteLocallyConstant` defines
`CategoryTheory.IsFiniteLocallyConstant`; the module
`Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent` states
`CategoryTheory.finiteLocallyConstant_coherent` with `sorry` proof. The definition
uses a finite family `U : Fin n → E`, an epimorphic coproduct to the terminal object,
and for each member a pullback square whose object over `U i` is a finite coproduct
of copies of `U i`. This is the slice formulation of finite local constancy and
renders the node's finite-cover trivialization and finite-set constant-sheaf clause.

The theorem hypothesis `_hE : IsCoherentTopos E` renders the Grothendieck/coherent-topos
setting from `def-trf-coherent-topos`; `F` is the sheaf object and the first conclusion
is `IsCoherentObject F`. The first operation clause quantifies a finite family
`G : Fin n → E` and gives finite local constancy of its coproduct. The second quantifies
an arbitrary finite category `J` and diagram `D : J ⥤ E`, assumes every diagram object
finite locally constant, and gives finite local constancy of `limit D`; this includes
terminal objects, finite products, and equalizers. The fourth clause takes a morphism
`f : G ⟶ H` with finite locally constant source and target and gives finite local
constancy of `image f`. The final clause takes an internal equivalence relation
`r₁ r₂ : R ⟶ G`, assumes `IsEquivalenceRelation r₁ r₂` and finite local constancy of
`R` and `G`, and gives finite local constancy of `coequalizer r₁ r₂`, the quotient
sheaf. No proof is supplied.

Dependencies used are `CategoryTheory.IsCoherentTopos` from
`Sheaf.CategoryTheory.Sites.CoherentTopos` and `CategoryTheory.constantSheaf` as the
Mathlib meaning of the constant-sheaf part of `def-weil-pbc-constant-sheaf`. The new
DAG definition node `def-trf-finite-locally-constant-set-sheaf` records the missing
finite-local-constancy notion and is cited by the item. The site and size dependencies
are retained in the node statement dependencies.

Edge cases checked: `n = 0` gives the empty coproduct and therefore cannot be an
epimorphic cover of a non-initial terminal object; `n = 1` gives a single trivializing
object; `Fin 0` in the finite-limit diagram is the terminal object; finite coproducts
allow empty coproducts; the image of an identity and the quotient by equality are
covered by the image and coequalizer clauses. The definition and theorem elaborate
with explicit universes and no auto-implicit variables.

Searches made before introducing the new definition: `msearch.py ... leanfinder
"finite locally constant set sheaf finite cover slice constant sheaf"` returned
CompHausLike.LocallyConstant and LightCondensed.IsDiscrete but no arbitrary-topos
predicate; `msearch.py ... loogle "CategoryTheory.constantSheaf IsConstant finite
locally constant"` returned only `CategoryTheory.constantSheaf`/`Sheaf.IsConstant`,
which omit finite covering triviality; `msearch.py ... grep
"locally.?constant|finite.*constant|IsConstant"` found only Mathlib's constantSheaf
and IsConstant declarations. Repository `rg` found only scheme/module predicates
`Scheme.IsFiniteLocallyConstantSheaf`, which have different objects and coefficients.
Thus the new definition is not a duplicate.

## New nodes

`def-trf-finite-locally-constant-set-sheaf` supplies the previously missing notion
used by the item. It is implemented in
`Sheaf.CategoryTheory.Sites.FiniteLocallyConstant` as
`CategoryTheory.IsFiniteLocallyConstant`, with real data (finite `Fin n` family,
epimorphic coproduct cover, pullback square, and finite coproduct slice model).
The item cites this node in `stmt_deps`.

## Second reading by NP

Independent maintainer reading of immutable commit
`9bdeb0003afd2ae4d2bc41dfd5f18543b1a6a20c`, 2026-10-18. The reader did not
write this delivery. The original placeholder under this heading is replaced
by this reading; the worker report above is retained.

I read the item and all five statement dependencies from the snapshot, both
Lean modules and the exact dependency declarations. Source places read:
Stacks sites-modules.tex lines 8409–8468 and 8542–8565 (093P, 093Q, 093R,
093S(1), 093U(1)); sites.tex lines 2099–2125 (constant sheaves and sheaf
colimits); Orgogozo author draft §8.1, printed pp. 17–18. The latter explicitly
uses coherence of locally finite constant objects in a coherent topos.

Clause matching:

- The Grothendieck-topos setting is `IsCoherentTopos.{w} E`, whose definition
  contains `IsGrothendieckTopos.{w} E`, an equivalence to Type-w-valued sheaves
  on a w-small site, and coherent finite-limit-closed generators. The node's
  finite-limit finite-cover presentation supplies this hypothesis through the
  recorded `finitarySiteCoherentGenerators`. Thus this intrinsic formulation
  adds no independent mathematical hypothesis. Images, finite limits and
  coequalizers exist in a Grothendieck topos; their instances specify choices.
- A finite covering family of arbitrary topos objects is `Fin n`, `U`, and
  `Epi (Sigma.desc u)`. The definition does not require representable objects.
  `IsPullback p q (terminal.from F) (u i)` is the restriction of F over U_i.
  `Over.mk q ≅ Over.mk (Sigma.desc (fun _ : Fin m => 𝟙 (U i)))` identifies it
  with m copies of U_i in the slice. This is the constant finite sheaf since
  the constant-sheaf functor is the sheafification of the constant presheaf
  and preserves coproducts. `Fin m` represents every finite set up to iso.
- The first conclusion is exactly `IsCoherentObject.{w} F`, i.e. quasi-compact
  and quasi-separated in the same universe as the coherent topos.
- The next two conclusions quantify every `Fin n` coproduct and every finite
  category diagram, respectively, assuming finite local constancy of each
  object. They give finite local constancy of the chosen coproduct and limit.
- The image clause quantifies an arbitrary arrow between finite locally
  constant objects, with result `IsFiniteLocallyConstant (image f)`.
- The quotient clause uses Mathlib `IsEquivalenceRelation`: this includes
  joint monicity and reflexivity, symmetry and transitivity, not just two
  arbitrary maps. The result concerns the coequalizer, exactly the quotient
  sheaf. Both the relation and its underlying object have the required
  finite-local-constancy hypotheses.

The outer implication on F packages the closure assertions together with
coherence of F. This introduces no substantive restriction: the terminal
object is always finite locally constant via its identity cover and the
singleton finite set, so the closure assertions can always be extracted.

Edge cases: empty coproducts and empty finite diagrams are allowed. An empty
trivializing family is epic only in the degenerate topos; it then correctly
trivializes every object. Empty constant values, empty images, identity images,
equality and full equivalence relations are included. No coefficient ring,
characteristic, nonemptiness, point, Noetherian or pro-etale assumption occurs.
The finite index universe can remain zero: every finite indexing category
can be replaced by a finite skeleton. The ambient site/coherence universe
must be arbitrary, and is now explicitly w, independently of u and v.

One-definition check: I searched the project, pinned Mathlib Sites sources,
upstream WeilConjectures and dag/lean_names_upstream.json by finite local
constancy and related names. I opened constantSheaf/Sheaf.IsConstant,
Scheme.IsFiniteLocallyConstantSheafOfTypes (HenselianFiniteEtale.lean:83),
and ProEtale.IsFiniteLocallyConstant (ConstructibleSheaf.lean:59). The first
pair lacks local finite triviality, the second is restricted to scheme etale
sites, and the third has module coefficients on pro-etale sites. None
supplies this arbitrary-topos finite-cover predicate. The worker records
LeanFinder, Loogle, LeanSearch and grep queries; these remain worker evidence,
not newly claimed independent service calls. No second definition was added.
The new definition node has real data, empty proof fields, matching ownership,
source, blueprint ancestry and dependencies. Its doubled TeX escapes were
repaired, and the source label made explicit.

Findings and repairs:

1. H3 (universe specialization): `[HasCoproducts.{0} E]` alone specialized
   `IsCoherentTopos` and `IsCoherentObject` to universe zero. Add
   `[HasCoproducts.{w} E]` and explicitly use `IsCoherentTopos.{w}` and
   `IsCoherentObject.{w}`. Retain zero-universe coproducts for finite families.
   This uses the existing generalized dependency interface; no new helper or
   source-based statement correction is needed.
2. H8: the original theorem docstring only summarized the conclusion. Supply
   all five proof steps: refine by coherent generators; construct the coherent
   epimorphic presentation and its quasi-compact kernel pair; refine finite
   diagrams into finite-set diagrams; compute images; compute coequalizers.
   The cited dependencies have exactly the statements used. Import the
   published finitary-site criterion, coherent quotient theorem and Mathlib
   sheafification exactness, as the stage-3 proof plan requires.
3. H1/H11: replace the placeholder second reading with this clause-by-clause
   reading; correct the worker report's module attribution.
4. B4/H12: normalize doubled TeX escapes in the new definition node only.
   The inherited item's mathematical statement is unchanged.
5. H9: remove redundant Basic, EquivalenceRelation and Images imports from
   the theorem module; the required interfaces remain public through the
   finite-local-constancy dependency. All lines are at most 100 characters.

Both original lean.statement fields were checked verbatim against the source
signatures and matched. The fixed item's complete replacement lean record
contains its new signature verbatim. The merge tool also re-reads that signature.
No statement_change or citer audit is required: the mathematical item and
all its dependencies retain their statements.

Compilation: the delivered report did not record a reproducible per-file run.
I ran scompile.py on both immutable files; rc 0, no errors or warnings,
library checks 1.2 s (definition), 1.4 s (theorem). After the fixes I ran
scompile.py again on the definition and corrected theorem under their intended
module names; rc 0, no errors or warnings, library checks 1.4 s and 1.9 s,
sandbox checks 1.3 s and 4.7 s. The current prescribed wrapper dispatches the
private nt-local-compile side overlay through its server wrapper; it is not
currently a local-host lcompile invocation. It compiled the published coherent
quotient import as well (1.6 s). No direct ssh command, lake build, global
build or project-clone edit was run. Only the named theorem has a `sorry`;
the definition has none and no local theorem was proved.

The current route-pivot dropped-node list has no intersection with the item's
statement or proof dependencies, and there is no repair note for this item.
No infinity/dg/model machinery or pro-etale substitute was introduced.

Verdict: FIX. Complete replacement module, lean record, new definition JSON
and this report are supplied in fixes; immutable delivery files stay untouched.
