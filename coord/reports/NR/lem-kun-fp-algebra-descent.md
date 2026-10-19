## Worker report

Recorded existing declaration `CommRingCat.exists_isPushout_of_finitePresentation`
in `WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation`
(upstream source, theorem at line 222). No module is written: this is precisely
the node's statement, already proved upstream. The published source was also
read using `scompile.py --source` and agrees with the local declaration.
Only the node's `lean` field is changed; its statement is unchanged.

Hypothesis and conclusion correspondence:

- The filtered diagram of commutative rings is `{J : Type uJ}`,
  `[Category.{vJ} J]`, `[IsFiltered J]`, and `(F : J ⥤ CommRingCat.{u})`.
- The specified colimit ring A and its structural maps are `(c : Cocone F)`,
  `c.pt`, `c.ι.app j`, and `(hc : IsColimit c)`. The upstream theorem also
  has `[PreservesColimit F (forget CommRingCat)]`. This is automatically
  available for the usual small filtered diagrams (`J : Type u` with
  `CommRingCat.{u}`), by Mathlib's
  `CommRingCat.forget_preservesFilteredColimits`; it is not an additional
  mathematical hypothesis. The more general upstream universes permit
  other diagrams whenever the same preservation property is available.
- The A-algebra B is `{S : CommRingCat.{u}}` and `(f : c.pt ⟶ S)`.
  Finite presentation is `(hf : f.hom.FinitePresentation)`.
- The conclusion supplies an index `j : J`, a commutative ring
  `T : CommRingCat.{u}`, its stage-algebra structure `g : F.obj j ⟶ T`,
  and its finite presentation `g.hom.FinitePresentation`.
- The map `h : T ⟶ S` and `IsPushout (c.ι.app j) g f h` assert precisely
  that S is the scalar extension of T to c.pt. In commutative rings the
  tensor product is the pushout, as stated in Mathlib's
  `CommRingCat.isPushout_tensorProduct` in
  `Mathlib.Algebra.Category.Ring.Constructions` (line 116). Uniqueness of
  pushouts identifies `T ⊗[F.obj j] c.pt` with S. Compatibility with the
  `c.pt` leg makes this an A-algebra isomorphism, not merely a ring
  isomorphism; tensor symmetry gives the displayed order. Conversely an
  A-algebra isomorphism in the node supplies this pushout square.

There are no statement-dependency nodes. The proof-dependency convention
node does not need a new import or repair because no module is delivered.
The existing proof follows exactly the supplied finite-presentation argument:
choose a finite polynomial quotient, lift its finitely many relations to a
common stage, take the quotient there, and use the pushout property of that
quotient. The source theorem's full docstring and proof were read.

Edge cases: `IsFiltered` includes nonemptiness, so an empty indexing category
is excluded by the original hypothesis, not an extra restriction. Zero rings,
zero variables, zero relations, and singleton/constant diagrams are permitted.
No nontriviality, characteristic, injectivity, or surjectivity assumption is
present. Choosing a common universe for the set-indexed system, colimit, and
algebra does not exclude any ordinary small diagram: their sizes can all be
raised together. No independent small test universe is introduced.

Searches performed on 2026-10-15:

- `msearch.py ... leanfinder` with "A finitely presented algebra over a
  filtered colimit of commutative rings descends to a stage": eight hits,
  including `CommRingCat.isFinitelyPresentable_hom` and
  `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`, concerning
  maps out of finitely presented algebras rather than descent of objects.
- `msearch.py ... loogle` with
  `CommRingCat.exists_isPushout_of_finitePresentation`: no hits, unknown
  identifier in Mathlib (the exact theorem belongs to the project upstream).
- `msearch.py ... grep` with
  `exists_isPushout_of_finitePresentation|exists.*[Ff]initePresentation`,
  restricted to `Algebra/Category/Ring`: one related Mathlib map-descent
  hit, `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`.
- `rg` of upstream `WeilConjectures` for the exact theorem and the item id
  finds the exact theorem and its quotient variant in the recorded module,
  plus uses in `AlgebraicGeometry/AffineTransitionLimit.lean`.
- `rg` of `lean/Sheaf` for the theorem and finite-presentation descent finds
  its use in `Algebra/LimitFinitePresentation/Core.lean` and several module
  descent theorems. Core's full statement was read; it constructs a special
  integer-subalgebra approximation system, so it is not the arbitrary given
  filtered-diagram statement of this item.
- `rg` of `dag/lean_names_upstream.json` for the exact theorem/item has no
  hits; the item's `lean_audit.slopmaster2` already records the exact
  theorem and a closed proof audit.
- `rg` of Mathlib ring constructions for tensor-product pushouts found
  `CommRingCat.isPushout_tensorProduct`, whose signature and construction
  were read; filtered-colimit source confirms the preservation instance.

No statement dispute, missing notion, or correction was found.

Validation: the existing declaration and tensor-product pushout declaration
are checked on the server using the prescribed `scompile.py` mechanism;
the delivery dry run independently checks the recorded existing declaration.


## Second reading by NR

I independently opened the node, its blueprint source, the full upstream
module (including section variables and proof), and the published server
source obtained with `scompile.py --source`. Verdict: the existing theorem
states exactly the node, using the equivalent pushout formulation.

Object/hypothesis/conclusion checklist:

1. A filtered system of commutative rings: `{J : Type uJ}`,
   `[Category.{vJ} J]`, `[IsFiltered J]`, and
   `(F : J ⥤ CommRingCat.{u})`. This covers the node's filtered index set
   and also allows filtered categories. Verdict: matches.
2. Its specified colimit A and structural maps: `(c : Cocone F)`,
   `(hc : IsColimit c)`, `c.pt`, and `c.ι.app j`. The section's
   `[PreservesColimit F (forget CommRingCat)]` is automatically supplied
   for a small filtered system by
   `CommRingCat.forget_preservesFilteredColimits` in Mathlib's
   `Algebra/Category/Ring/FilteredColimits.lean:363`. All objects and the
   set of indices can be put in a common universe; thus this parameter
   does not add a mathematical hypothesis to the node. Verdict: matches.
3. A finitely presented A-algebra B: `{S : CommRingCat.{u}}`,
   `(f : c.pt ⟶ S)`, `(hf : f.hom.FinitePresentation)`.
   I opened `RingHom.FinitePresentation` at
   `Mathlib/RingTheory/FinitePresentation.lean:392`: it is precisely
   `Algebra.FinitePresentation` for `f.hom.toAlgebra`. No finite-module,
   field, Noetherian, or nontriviality assumption is substituted.
   Verdict: matches.
4. There exists an index i: `∃ (j : J)`. Verdict: matches.
5. There exists a finitely presented stage algebra B_i:
   `(T : CommRingCat.{u}) (g : F.obj j ⟶ T)` followed by
   `(_ : g.hom.FinitePresentation)`. The existential order agrees
   with the node. Verdict: matches.
6. An A-algebra isomorphism B ≅ B_i ⊗[A_i] A:
   `∃ (h : T ⟶ S), IsPushout (c.ι.app j) g f h`.
   I opened `CommRingCat.isPushout_tensorProduct` in Mathlib's ring
   constructions. The tensor product is the pushout of the two algebra
   maps. Uniqueness of pushouts identifies S with the tensor product,
   respecting its c.pt leg f; tensor symmetry gives the node's factor
   order. Conversely the stated A-algebra isomorphism supplies h and
   this pushout. No selected map beyond that isomorphism is required.
   Verdict: equivalent, with neither a missing nor an extra clause.

Source check: the node's source is the blueprint lemma, whose statement
and finite-coefficient proof were read directly. I also read Stacks
`algebra.tex`, `lemma-colimit-category-fp-algebras` (tag 05N9), part (1)
and its proof, at lines 32178 onwards. Its assumptions are a directed
colimit of rings and a finitely presented algebra, exactly as here; no
standing locality, Noetherianity, or characteristic restriction occurs.
The upstream module incorrectly labels this theorem with tag 00R4:
`tags/tags` identifies that tag as `lemma-CM-over-regular-flat`, and I
opened its statement (miracle flatness). This is a citation error only.
I added the correct citation and explanation to the delivery's lean.note;
the read-only upstream module and the node's mathematical statement are
unchanged. The blueprint proof's conventions reference is only a bundle
of scheme conventions, not a missing ring-algebra construction; I read
that dependency node too. There are no statement dependencies, new nodes,
or dependency modules in this delivery.

Proof check: the upstream proof chooses a finite polynomial quotient,
lifts the finite set of relation polynomials to a common stage, takes the
quotient by those lifted relations, obtains the pushout using
`exists_isPushout_quotient_span`, and verifies finite presentation of the
stage quotient. These are precisely the node's proof steps. No new theorem
or definition is introduced, so no new sorry, hollow data, or unbound
variable is present. Existing-source docstrings are not rewritten.
The lean.statement was mechanically compared with the source signature
from `theorem` through its conclusion, excluding `:= by`: verbatim equal.

Edge cases: IsFiltered already requires a nonempty index category, as
filtered colimits do here. Zero rings and the zero algebra remain allowed.
Zero generators or zero relations cause no restriction (the finite-stage
argument still supplies a stage for the empty set). No characteristic is
fixed. Empty schemes are irrelevant to this ring statement. Arbitrarily
large small set-indexed systems fit by a common universe enlargement;
there is no independent too-small test universe or extra universe equality.

Independent searches, using different wording from the first reading:

- `msearch.py NR lem-kun-fp-algebra-descent leanfinder` with
  "finite presentation algebra defined over one ring of a direct limit":
  eight hits including `Algebra.Presentation.instFinitePresentationModelOfHasCoeffsOfFinite`
  and `RingHom.finitePresentation_algebraMap`; these supply presentation
  models or finiteness equivalence, not the full arbitrary-diagram theorem.
- Loogle query `IsPushout, RingHom.FinitePresentation`: no hits; Loogle's
  database does not recognize `IsPushout` for this query. This is recorded
  as an unsuccessful search, not evidence of absence.
- Direct rg of Mathlib's ring category files for existential finite
  presentation, colimit and pushout combinations finds map descent
  (`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`), not the
  object-descent theorem. Direct rg of upstream's ring finite-presentation
  module locates the exact theorem, its surjective variant, and polynomial
  lifting helpers. Direct rg and reading of project
  `Sheaf/Algebra/LimitFinitePresentation/Core.lean` finds the theorem's
  use for a special integer-subalgebra approximation, not a replacement
  for the arbitrary specified system. Hence the existing upstream
  declaration is the correct unique interface to record.

Validation: through `scompile.run_server` in the prescribed scompile.py,
compiled the scratch ExistingChecks.lean on the server: 1.3 seconds,
nice 19, two threads, 60-second limit, no warnings or errors. The expanded
signature includes the colimit witness and the discussed preservation
instance. The tensor-product pushout also checks, and `#print axioms`
for the recorded theorem reports only propext, Classical.choice, Quot.sound.
Only the citation note needed repair; all mathematical content is retained.
