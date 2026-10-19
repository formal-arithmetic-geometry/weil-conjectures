## Worker report

Existing declaration, no new module:
`AlgebraicGeometry.nagataCompactification_of_isNoetherian`, in
`WeilConjectures.Compactification.Noetherian` (upstream source, theorem near line 244
in the current published source; local older source near line 228).
I read the complete signature and docstring in the local checkout and confirmed
its current published source using `scompile.py --source`.
The node's current blueprint source is
`literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/`
`sk-thm-nagata-sketch-noetherian/_section.md`.
It states exactly this theorem.

Clause-by-clause correspondence:

- Schemes and their morphism: the enclosing explicit `universe u` and
  `variable {X S : Scheme.{u}}`, then `(f : X ⟶ S)`.
- The base is Noetherian: `[IsNoetherian S]`.
- The morphism is separated: `[IsSeparated f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`. Mathlib's
  `AlgebraicGeometry.Morphisms.FiniteType` module documentation explicitly says
  finite type means locally finite type and quasi-compact; this is no extra
  hypothesis.
- Admits a compactification: `HasCompactification f`. I read its definition in
  `WeilConjectures.Compactification.Defs`: it asserts
  `Nonempty (Compactification f)`, whose actual data are a scheme `Z`, a proper
  `g : Z ⟶ S`, an open immersion `i : X ⟶ Z`, and `comm : f = i ≫ g`.
  The upstream structure does not store quasi-compactness of `i`, but
  `AlgebraicGeometry.Compactification.quasiCompact_openImmersion` in the same
  module has signature
  `theorem quasiCompact_openImmersion (hf : QuasiCompact f) : QuasiCompact c.i`
  for every `c : Compactification f`. Thus even the quasi-compact-open-immersion
  convention of compactification is met under the stated finite-type hypothesis.
  This helper is also listed in `lean.declarations`.

There are no statement-dependency nodes (`stmt_deps` is empty). The recorded
upstream theorem uses the canonical Mathlib `Scheme`, `IsNoetherian`,
`IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`, and the upstream
`Compactification`/`HasCompactification` declarations just described.
The proof dependency `sk-lem-nagata-sketch-affine-cover` has no Lean binding in
this snapshot; it is not a prerequisite to reusing the already existing theorem,
and no statement of that node is introduced. The existing theorem's docstring
and implementation follow the stated affine-cover/partial-union induction.

Edge cases checked: neither scheme is assumed nonempty, integral, reduced,
affine, or separated absolutely. The empty source is explicitly the zero step
of the upstream construction, compactified as a proper morphism. The empty
base is permitted and forces the source empty. The theorem's arbitrary universe
`u` imposes no finite/countable restriction. Separatedness is relative to `S`;
no separatedness of `S` is required. No projectivity or density of the final
open immersion is added to the conclusion.

Searches for reuse (2026-10-16 UTC):

- `msearch.py ... leanfinder "Every separated finite type morphism of schemes to
  a Noetherian scheme admits a compactification"`: eight hits, on finite/proper
  morphisms and quasi-compactness over Noetherian schemes; no exact Mathlib theorem.
- `msearch.py ... leansearch "Nagata compactification theorem separated finite
  type morphism Noetherian scheme"`: eight hits, separatedness and properness;
  no compactification theorem.
- `msearch.py ... loogle "AlgebraicGeometry.HasCompactification,
  AlgebraicGeometry.IsNoetherian"`: no hits; unknown identifier
  `AlgebraicGeometry.HasCompactification` in the Mathlib search index.
- `msearch.py ... grep "nagataCompactification|HasCompactification"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `WeilConjectures` for
  `nagataCompactification_of_isNoetherian|sk-thm-nagata-sketch-noetherian`:
  found the exact theorem in `Compactification/Noetherian.lean`, with uses and
  axiom checks in the other compactification modules; no literal node-id tag.
- `rg` over `lean/Sheaf` for
  `nagataCompactification_of_isNoetherian|HasCompactification`: found consumers
  of compactification and a field specialization `CompactifiableOverField`;
  the general Noetherian theorem is supplied upstream.
- `rg` in `dag/lean_names_upstream.json` found the exact theorem name twice.

No new nodes, dependency modules, statement correction, or statement dispute.
Only the item's `lean` field is changed; its pre-existing imported status and
all other fields are preserved. The old attachment was incomplete metadata;
this delivery supplies the complete existing-declaration record. No Lean file
is written because doing so would duplicate the existing theorem.

Validation: the prescribed `deliver2.py --no-push` checks both listed existing
declarations by importing the upstream module and running `#check` through
`scompile.py`, and runs the server preflight. The second reader supplies the
independent reading and performs delivery.

## Second reading by Q63

I independently read the node, its exact current blueprint source
`main-20261015/blueprint/sec-nagata-compactification/`
`sk-thm-nagata-sketch-noetherian/_section.md`, the chapter and compactification
definition, the local upstream files, and both current published upstream modules
using `scompile.py --source WeilConjectures.Compactification.Noetherian` and
`scompile.py --source WeilConjectures.Compactification.Defs`. There is no repair
note for this item. The item has no statement dependencies, new nodes, dependency
modules, or statement correction to audit.

The mathematical list and its Lean rendering are:

1. Arbitrary schemes X and S: `universe u` and
   `variable {X S : Scheme.{u}}` in the enclosing published module. PASS: the
   theorem is universe-polymorphic and neither scheme carries extra structure.
2. A morphism X to S: `(f : X ⟶ S)`. PASS: this is the same arbitrary morphism,
   rather than an absolute structure map or a field specialization.
3. S is Noetherian: `[IsNoetherian S]`. PASS: Mathlib's class extends
   `IsLocallyNoetherian S` and `CompactSpace S`; local Noetherianity means all
   affine-open section rings are Noetherian. This is global Noetherianity, exactly
   as the source states. No separate absolute separatedness is assumed.
4. f is separated: `[IsSeparated f]`. PASS: relative separatedness of this f.
5. f is finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`. PASS: these are
   precisely the two conditions in the module documentation of Mathlib's
   `AlgebraicGeometry.Morphisms.FiniteType`, not two extra finiteness hypotheses.
6. There exists a compactification: `HasCompactification f`. PASS: I unfolded
   the declaration by reading `Defs`: its sole field is
   `Nonempty (Compactification f)`. The structure introduces `Z : Scheme.{u}`,
   `g : Z ⟶ S`, `i : X ⟶ Z`, `comm : f = i ≫ g`, `IsProper g`, and
   `IsOpenImmersion i`. Thus the ambient scheme and both maps are existential
   after f and its hypotheses, with the required factorization. For the source's
   quasi-compact-open convention, the independently checked helper is
   `Compactification.quasiCompact_openImmersion (hf : QuasiCompact f) :
   QuasiCompact c.i` for every `c : Compactification f`. The finite-type
   hypothesis supplies hf. Conversely such a quasi-compact open factorization
   is already a `Compactification f`, so no conclusion is weakened or strengthened.

I also read the Stacks source `flat.tex`, section `section-compactifications`
and theorem `theorem-nagata` (tag 0F41), especially its Noetherian paragraph.
The section imposes no background field or characteristic. The general theorem
assumes a qcqs base; a Noetherian scheme is qcqs. Its Noetherian paragraph uses
exactly a separated finite-type morphism, a finite affine cover with dense total
intersection, affine compactifications, and repeated two-open gluing. This agrees
with the node's proof and with the published module's complete proof description:
empty partial union, affine first union, dense-overlap gluing, and final union X.
The current unit source itself states only existence of a compactification;
scheme-theoretic density is a separately named additional property and is not
an omitted clause here.

Edge cases: empty X is permitted (the published construction's zero step uses
the empty scheme); empty S forces empty X and is also permitted. A zero ring
therefore introduces no exception. There is no nonempty, reduced, integral,
affine, projective, absolute-separatedness, base-field, or characteristic
assumption. The finite-cover length may be zero in the construction; it is not
a positive binder of the statement. `u` is arbitrary, and choosing a common
universe for the schemes excludes no pair of schemes after enlarging universes.
All binders in the recorded signature are bound explicitly in its source.

Independent reuse searches, using queries different from the worker's:

- LeanFinder: "A separated morphism of finite type to a noetherian scheme
  factors through an open immersion into a proper scheme" returned eight
  related properness/separatedness results, with no exact Mathlib theorem.
- Loogle: `AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.IsSeparated`
  returned zero hits.
- LeanSearch: "A finite type separated scheme morphism to a Noetherian base
  has a compactification" returned eight related finiteness/properness results,
  with no exact compactification theorem.
- `rg -i 'nagata|compactification'` over Mathlib's AlgebraicGeometry returned
  no matches. Searching `WeilConjectures/Compactification` located the exact
  Noetherian theorem and the shared compactification definitions. Searching
  `lean/Sheaf` for `HasCompactification|nagataCompactification|CompactifiableOverField`
  located consumers and the field specialization, not a replacement general
  Noetherian theorem. The upstream name inventory also lists the exact theorem.

Verdict: the existing binding is correct. No mismatches or changes to the Lean
record, node statement, dependencies, or upstream source were needed. The
recorded `lean.statement` is verbatim the published theorem signature (without
the proof). No module is delivered, so no duplicate definition, new proof,
hollow data, or new docstring obligation is introduced. The older upstream
blueprint label in its docstring is retained; the exact current source and node
identity are recorded here. Second reading adds this report only.
