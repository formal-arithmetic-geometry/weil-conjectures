## Worker report

Repair of return R-ftr1046 (head b443ddb19), H4. The item now records the existing
`CategoryTheory.Sheaf.Torsor` in `WeilConjectures.CategoryTheory.Sites.Torsor`, branch
`slopmaster2`. Its verbatim source signature is
`structure Torsor (G : Sheaf J AddCommGrpCat.{w})`.
The duplicate module `lean/Sheaf/AlgebraicGeometry/FiniteEtaleSheafTorsor.lean` has been
removed, including its duplicate class-set, basepoint, trivial torsor and special-case theorem.
No new definition, theorem, dependency module or node is delivered.

The node's hypotheses and clauses correspond to the existing declarations as follows:

- A scheme is `Y : Scheme.{u}`; a finite abelian group is `M : Type (u + 1)` with
  `[AddCommGroup M] [Finite M]`. Specialize the site's binders to `Y.Etale` and
  `J = Y.smallEtaleTopology` and set
  `G = (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)`.
  This is exactly the source expression used by `Scheme.EtaleTorsor.toSheafTorsor`
  and `Scheme.EtaleTorsor.quotientToSheafTorsor`.
- The sheaf of sets `P` is `Sheaf.Torsor.sheaf : Sheaf J (Type (u + 1))` at this
  specialization. The action is `vadd`, its identity and composition laws are
  `zero_vadd` and `add_vadd`, and compatibility with restriction is `map_vadd`.
- The map `(m,p) ↦ (m+p,p)` is a sheaf isomorphism precisely because `bijective_vadd`
  says the action map onto the first coordinate is bijective for each fixed second
  coordinate at every object. Naturality comes from `map_vadd`; bijectivity is vacuous
  at an object with no sections, as required for this map.
- Local nonemptiness is `nonemptySieve_mem U`: arrows from objects with nonempty
  sections form a covering sieve in `Y.smallEtaleTopology`. The dependency's
  `Scheme.ofArrows_mem_smallEtaleTopology_iff` identifies covering families with jointly
  surjective etale families, giving exactly the local-cover clause.
- Finite local constancy is automatic, not extra data or an additional restriction:
  `AlgebraicGeometry.Scheme.EtaleTorsor.isFiniteLocallyConstantSheafOfTypes_sheaf`
  in `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` applies to every
  such `P`. Its target predicate, `Scheme.IsFiniteLocallyConstantSheafOfTypes`, is
  defined in `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` by constancy on
  an etale cover and finite geometric stalks, the same two clauses as the dependency's
  `Scheme.IsFiniteLocallyConstantEtaleSheafOfSets`.
- `Tor^1(Y,M)` is `Quotient (Sheaf.Torsor.setoid (G := G))`. That setoid's relation is
  `Nonempty (Sheaf.Torsor.Iso P Q)`, where `Iso` is an equivariant isomorphism of the
  underlying sheaves. Its base point is `Quotient.mk _ (Sheaf.Torsor.trivial G)`.
  The trivial torsor is `G` acting on itself by translation. These are existing
  constructions; they need no new named wrappers.

Dependency declarations read: `Scheme.smallEtaleTopology` and
`Scheme.ofArrows_mem_smallEtaleTopology_iff` in `Mathlib.AlgebraicGeometry.Sites.Etale`
(the `mathlib_match` of `def-weil-pbc-etale-site`); the recorded declarations of
`def-weil-pbc-etale-sheaves` in `Sheaf.AlgebraicGeometry.EtaleSheaves`, in particular
`Scheme.IsLocallyConstantEtaleSheafOfSets` and `Scheme.IsFiniteLocallyConstantEtaleSheafOfSets`.
The constant sheaf is `CategoryTheory.constantSheaf` in
`Mathlib.CategoryTheory.Sites.ConstantSheaf`. The action, equivariant isomorphism,
setoid and trivial torsor are all supplied by the existing source torsor module.

Edge cases: no connectedness, nonemptiness, characteristic or nonzero integer assumption
on `Y` occurs; the empty scheme is allowed. The zero/singleton group is allowed by
`[Finite M]`. No globally inhabited section type is assumed: an object can have no
sections, but local sections are required on a covering sieve. On a nonempty base that
excludes the empty sheaf; on the empty base an empty covering is legitimate and must
not be ruled out. The trivial torsor gives a basepoint in every case. The universe
choice is the source's own scheme/sheaf convention and accommodates finite groups.
No statement correction or STATEMENT-DISPUTED issue is needed.

Searches (the negative Mathlib results do not imply absence in the source):

- `msearch.py leanfinder`, query "finite abelian constant sheaf torsor on small etale
  site isomorphism classes": eight unrelated Mathlib hits (condensed/locally constant
  modules and Galois categories); no torsor definition found by that search.
- `msearch.py loogle`, query "Torsor, constantSheaf": zero hits, unknown identifier
  `constantSheaf`; this does not decide the source-repository match.
- `msearch.py grep`, query `FiniteEtaleTorsor|FiniteTorsor|TorOne|Torsor`, subdirectory
  Mathlib `CategoryTheory`: zero hits. The earlier `leansearch` request recorded in
  `searches.jsonl` was unavailable (Internal Server Error).
- Source `rg` for `structure Torsor|instance setoid|def trivial` finds the exact
  declarations at `WeilConjectures/CategoryTheory/Sites/Torsor.lean:80,134,140`.
  Source `rg` for `toSheafTorsor|quotientToSheafTorsor` finds the precise constant-sheaf
  specialization and quotient in `AlgebraicGeometry/Morphisms/EtaleTorsor.lean`.
  Source `rg` for `isFiniteLocallyConstantSheafOfTypes_sheaf` finds the general
  finite-constant-sheaf result in `EtaleTorsorDescent.lean:457`.
- Source search for `def-weil-pbc-finite-torsors` within the torsor module yields no
  blueprint-id hit; the match is mathematical, established by reading the signatures
  and docstrings, rather than by an id annotation.
- Project `rg` for `Torsor|torsor` under `lean/Sheaf` finds unrelated normal-scheme
  data, not an alternative definition needed here. The existing source API suffices.

The former search conclusion that the general torsor "lacks the finite locally constant
specialization" was wrong: specializing `G` and using the source theorem gives exactly
the node. The lean record's note now explains the specialization, quotient, basepoint,
and automatic finite local constancy explicitly.

Validation: a scratch file outside the delivery modules compiled cleanly on the server
with `scompile.py` (exit code 0, 2.4 seconds). It checked the source theorem at the exact
constant-sheaf specialization and the quotient class of the trivial torsor. No scratch
declaration is included in the delivery.

## Earlier second reading (a previous round; superseded)

The previous second reading is superseded by the independent maintainer review
R-ftr1046, which identified H4. Its findings have been checked against the open node,
`Sites/Torsor.lean`, `EtaleTorsor.lean` and `EtaleTorsorDescent.lean` during this repair.
The second reader will inspect this revised delivery before pushing it.

The mismatch was duplication, including an unnecessary finite-local-constancy field
and a redundant theorem for the trivial torsor. The repair deletes that module and
records `Sheaf.Torsor`, `Sheaf.Torsor.setoid` and `Sheaf.Torsor.trivial` as existing.
For finite abelian `M` and arbitrary `Y`, the stated constant `G` gives the node's
underlying sheaf and action; `zero_vadd`, `add_vadd`, `map_vadd` give its laws;
`bijective_vadd` gives the displayed isomorphism; `nonemptySieve_mem` gives local
nonemptiness. The source's finite-local-constancy theorem gives both local constancy
and finite stalks without imposing another condition. The equivariant-isomorphism
setoid and the class of `trivial G` give exactly the pointed isomorphism-class set.
The empty-scheme and zero-group cases remain permitted. The corrected search section
no longer treats the negative Mathlib searches as evidence against these source matches.

## Second reading by G1

I independently opened the sandbox node and the existing source declarations in
`WeilConjectures/CategoryTheory/Sites/Torsor.lean` (lines 61–149), the constant-sheaf
specialization in `AlgebraicGeometry/Morphisms/EtaleTorsor.lean`, and the theorem in
`EtaleTorsorDescent.lean` (lines 365–482). The item has `existing: true`; there is no
module, new node or dependency module in this delivery. Its `lean.statement` is verbatim
`structure Torsor (G : Sheaf J AddCommGrpCat.{w})`, immediately before `where` in the source.
No statement correction is present or needed.

The statement inventory and matching Lean are:

1. Arbitrary scheme Y: `Y : Scheme.{u}`, site `Y.Etale`, topology
   `Y.smallEtaleTopology`. I read the dependency's Mathlib declaration and
   `Scheme.ofArrows_mem_smallEtaleTopology_iff`: coverings are exactly jointly
   surjective families. Verdict: same scheme and site, no extra assumptions.
2. Finite abelian M: `M : Type (u + 1)` with `[AddCommGroup M] [Finite M]`.
   The group sheaf is `(constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
   (AddCommGrpCat.of M)`. This is the sheafification-based constant sheaf, not the
   generally incorrect constant presheaf. Verdict: exact specialization.
3. Sheaf of sets P: `Sheaf.Torsor.sheaf : Sheaf J (Type w)`, specialized to the
   preceding J and `w = u + 1`. Verdict: same sheaf category.
4. Action of the constant group sheaf: `vadd`, with `zero_vadd`, `add_vadd` and
   `map_vadd` giving the identity, group law and restriction compatibility.
   Verdict: an action of sheaves, not only an action of the abstract group on sections.
5. Displayed map `(m,p) ↦ (m+p,p)` is an isomorphism: `bijective_vadd U p` makes
   each fibre over p bijective; hence the product map is bijective objectwise,
   and `map_vadd` makes it natural. Conversely the product isomorphism gives those
   fibre bijections. Verdict: equivalent, including objects without sections.
6. Every object has a covering with sections: `nonemptySieve_mem U` and the
   definition `nonemptySieve`, whose arrows are precisely those with a section
   on their domain. On the small etale topology, a covering sieve contains a
   jointly surjective etale covering family; conversely such a family generates
   a covering sieve. Verdict: exactly local nonemptiness, not global nonemptiness.
7. Finite locally constant P: the source theorem
   `Scheme.EtaleTorsor.isFiniteLocallyConstantSheafOfTypes_sheaf` takes every P of
   precisely this specialization. I read its surrounding binders: only finite M
   and arbitrary Y remain; the theorem omits the temporary topology instances on M.
   Its proof uses a local section to identify the restriction with constant M, and
   proves the geometric fibres finite. I opened the dependency module
   `Sheaf.AlgebraicGeometry.EtaleSheaves`, its two relevant definitions, and
   `HenselianFiniteEtale.lean:83` / `ConstructibleSheaf/Defs.lean:192`:
   the cover/constant restriction clauses agree, and the source's `IsFiniteSheaf`
   for Type means finite fibres (via `ConcreteCategory.isFinitelyGenerated_iff_finite`).
   The source checks separably closed fields, which includes the dependency's
   algebraically closed fields; finite-constant torsors satisfy both formulations.
   Verdict: automatic condition; adding its proof as data would not change the notion
   but would needlessly duplicate an existing definition.
8. Isomorphism classes: `Quotient (Sheaf.Torsor.setoid (G := G))` with relation
   `Nonempty (Sheaf.Torsor.Iso P Q)`. I read `Iso`: its underlying sheaf isomorphism
   commutes with the action. Verdict: precisely torsor isomorphism classes.
9. Distinguished class: `Quotient.mk _ (Sheaf.Torsor.trivial G)`; `trivial` uses
   G's underlying set sheaf and addition. Verdict: the required trivial-torsor basepoint.

Source check: the literature paths recorded by the node are not materialized in this
clone. I read the local Stacks source at
`/home/ubuntu/c1-stacks-review/sites-cohomology.tex:242–274`; the tags table identifies
this as 03AH, `sites-cohomology-definition-torsor`. It assumes only a site and a group
sheaf: simply transitive action when sections exist, and a covering with sections for
*every* object. The trivial torsor is the group sheaf with its left action. There is no
ambient Noetherian, connectedness, characteristic or nonempty-base hypothesis. The
node's finite abelian constant-sheaf case agrees with that definition.

Edge cases: the trivial/zero group is allowed; an abelian group is necessarily inhabited,
so an empty M is not an omitted case. Empty Y is allowed, as are empty covering families
when they cover an empty object. A sheaf sends the empty object to a singleton by the
sheaf condition, so “empty sheaf” should not be interpreted as the presheaf that is empty
on every object. Local sections exclude the initial sheaf as a torsor on a nonempty base.
No global section is required, and section types on nonempty objects may be empty.
There is no integer n or restriction on characteristic. Universes are explicit in the
existing general definition; choosing u large enough and transporting a finite group
along a universe lift covers any input finite group and scheme. No hypothesis or clause
was added or dropped by the specialization.

Independent searches, using different queries from the worker:

- `msearch.py leanfinder`, “sheaf with simply transitive abelian group action and local
  sections”: eight unrelated module/sheafification results, no matching site torsor.
- `msearch.py loogle`, `"Torsor"`: twelve results around Mathlib's `Torsor` and
  `AddTorsor` on inhabited types. These are not sheaf torsors: they require global
  inhabitation and do not encode restriction compatibility or local covering sections.
- `msearch.py grep`, `simply transitive|principal homogeneous`: two Mathlib hits
  (algebraic torsors and Cartesian-module documentation), not the site notion.
- Direct `rg` on Mathlib's `CategoryTheory/Sites`, the source's
  `WeilConjectures/CategoryTheory/Sites`, and project `lean/Sheaf`, for
  `principal homogeneous|Torsor|torsor`: the source definition and its APIs are the
  match. The current project also has torsor extension/contracted-product modules;
  these import the same source `Sheaf.Torsor`, rather than defining this notion again.
  This updates the worker's older project-search description, which mentioned only
  unrelated normal-scheme data.

Mismatch findings and changes: no mismatch in the revised existing record. The previous
round's duplicate definition was already removed by the worker; I confirmed no delivery
module remains. I preserved the correct node and added this independent review, including
more precise empty-scheme and current project-search explanations. Existing source
objects are concrete, with no hollow definition in the recorded torsor, setoid or trivial
construction. No proof or duplicate definition is delivered; the docstring and line-width
requirements for new modules therefore do not apply. The node has no proof steps.

Validation: I reran `scompile.py G1 def-weil-pbc-finite-torsors scratchpad/Check.lean`
(the absolute sandbox path was passed). It checked the finite-local-constancy theorem
at the exact specialization and the quotient/basepoint expression: compiled in 2.3 seconds,
exit code 0, no warnings. The scratch file is not a delivery module.
