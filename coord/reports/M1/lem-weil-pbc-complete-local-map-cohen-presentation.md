## Worker report

The module `Sheaf.RingTheory.CompleteLocalMapCohenPresentation` states
`RingHom.exists_complete_local_map_cohen_presentation`, with its sole proof `sorry`.
The node statement is unchanged. One definition node is added for the ordered parameter list.
No statement dispute or source correction was needed.

Hypotheses, matched individually:
- Commutative local rings A and B: `{A : Type u} {B : Type v}`, `[CommRing A]`,
  `[CommRing B]`, `[IsLocalRing A]`, `[IsLocalRing B]`. Local rings are nonzero.
- Noetherian: `[IsNoetherianRing A]`, `[IsNoetherianRing B]`.
- Complete for the respective maximal-ideal-adic topologies:
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]` and the analogous B binder.
- The given local homomorphism: `(f : A →+* B) [IsLocalHom f]`.

Conclusion, matched clause by clause:
- Existential coefficient rings ΛA, ΛB, their commutative-ring structures, and finite
  variable counts `n m : ℕ`. The local rings are the explicit representatives
  `R := MvPowerSeries (Fin n) ΛA`, `S := MvPowerSeries (Fin m) ΛB`.
  Choosing representatives of the asserted power-series rings changes no assertion.
- Complete regular local rings: existential `IsRegularLocalRing R` and
  `IsRegularLocalRing S`, followed by the two `IsAdicComplete` clauses. The regular-local
  witnesses provide their local-ring and Noetherian instances for the remainder.
- Characteristic-zero residue field: `CharZero (IsLocalRing.ResidueField A) →
  IsField ΛA ∧ IsField ΛB`. `IsField` is the existing commutative-ring predicate,
  equivalent to a compatible Field structure; it does not introduce another multiplication.
- Positive residue characteristic: for every prime p with `CharP (ResidueField A) p`,
  both coefficients are domains with `IsDiscreteValuationRing` witnesses, their maximal
  ideals equal `Ideal.span {(p : ΛA)}` and `Ideal.span {(p : ΛB)}`, and both are
  maximal-ideal-adically complete. This is precisely the composed Mathlib match recorded
  by `def-weil-pbc-cohen-ring`, not a private Cohen-ring definition.
- Surjective local q and v: `Function.Surjective q ∧ IsLocalHom q`, similarly for v.
- Local u and the commutative square: `IsLocalHom u` and `v.comp u = f.comp q`.
- Flatness: `u.Flat`, which uses the module structure induced by u.
- Regular local closed fibre: `IsRegularLocalRing
  (S ⧸ (IsLocalRing.maximalIdeal R).map u)`; ideal map is extension of m_R to S.
- Chosen parameters of R: `∃ (t : List R)`, `IsLocalRing.IsRegularSystemOfParameters t`.
- Their images extend to parameters of S: `∃ (z : List S)`,
  `IsLocalRing.IsRegularSystemOfParameters (t.map u ++ z)`.
- First parameter p in positive residue characteristic: for every prime p with that
  residue characteristic, `t.head? = some (p : R)`. This requires nonemptiness exactly
  in the positive-characteristic case and indexes t₁ as the head of the ordered list.

Dependency declarations read and used:
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation for Noetherian as a self-module.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`, combining separatedness and completeness. Its recorded match is
  the equivalence with bijectivity of the canonical completion map.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, families indexed by finite-support monomial exponent vectors.
- `def-weil-pbc-cohen-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` and its `irreducible_iff_uniformizer` characterization,
  together with `IsAdicComplete` as specified in the composed recorded match.
  A domain plus this DVR structure is exactly a local PID that is not a field.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`.
- `def-weil-regular-scheme`: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularLocalRing`. Only the ring clause, not a scheme specialization, is needed.
- Added dependency `def-weil-pbc-regular-system-of-parameters`:
  `Sheaf.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters`.

Edge cases checked before writing:
- n=0 or m=0 is allowed: formal series with no variables represent the coefficient ring.
- Dimension zero in the field case uses t=[], and extension by z is still meaningful.
  The definition spans the empty set and requires dimension zero.
- Positive residue characteristic allows n=0 but then R is a Cohen DVR; t starts with p,
  hence still has length at least one. Equal-characteristic p A and B are allowed:
  their presenting Cohen rings need not have characteristic p themselves.
- A and B may have different dimensions and different residue fields. Neither n=m nor
  any equality of coefficient rings is imposed. Locality forces matching residue
  characteristics, so conditioning both coefficient rings on A's residue characteristic
  also covers B correctly.
- The zero ring is excluded by the original local-ring hypothesis, not by a new assumption.
- A and B may lie in different universes u and v. Coefficients are in `Type (max u v)`;
  their residue fields and Cohen rings can be chosen there. This allows the small rings
  to be lifted to that universe, with no cardinality restriction beyond the input rings.

Searches for existing declarations:
- msearch leanfinder: "local homomorphism of complete Noetherian local rings has
  compatible Cohen power series presentations with regular parameters and flat map".
  Eight results about Henselianity/Weierstrass theory; no presentation theorem.
- msearch loogle: `IsRegularLocalRing, MvPowerSeries, IsLocalHom`: zero hits.
- msearch grep: `Cohen|cohen|[Rr]egular[Ss]ystem|[Ss]ystemOfParameters` in RingTheory:
  only the unrelated Cohen citation in Noetherian/OfPrime.lean.
- msearch leansearch: "regular system of parameters local ring finite family generates
  maximal ideal and length equals Krull dimension": service unavailable (Internal Server Error).
- msearch leanfinder, same parameter query: eight Krull-dimension lemmas about regular
  sequences, not a definition of a regular system of parameters.
- msearch grep: `IsRegularSystemOfParameters|regular system of parameters|IsCohenRing|Cohen ring`:
  no hits in Mathlib.
- rg over `WeilConjectures` and `lean/Sheaf`, and grep by the item id in WeilConjectures:
  no presentation theorem, Cohen-ring definition, or parameter-system definition.
  Name collision search in `dag/lean_names_upstream.json`: no proposed names.
- DAG definition-node search for "system of parameters": no definition node.
  `tools/blueprint_refs.py search 'regular system of parameters'`: zero blueprint nodes;
  its ancestor command identifies `thm-weil-pbc-finite-etale-lifting`.

Sources inspected online because this clone has no Stacks TeX checkout:
[07NN](https://stacks.math.columbia.edu/tag/07NN) gives compatible presentations;
[07NQ](https://stacks.math.columbia.edu/tag/07NQ) supplies the choice t₁=p;
[00KU](https://stacks.math.columbia.edu/tag/00KU) defines parameters;
[0327](https://stacks.math.columbia.edu/tag/0327) defines Cohen rings.
Both modules compiled together cleanly on the server, with no warnings or errors.

## New nodes

`def-weil-pbc-regular-system-of-parameters` gives the finite ordered family needed by
07NN: its length equals Krull dimension and its generated ideal is the maximal ideal.
Source: Stacks 00KU(2). The definition uses existing Mathlib ideal span, List, maximalIdeal,
and ringKrullDim; its real data contains no sorry. It cites the existing Noetherian and
regular-local-ring definition nodes. All three kinds of search are recorded from actual
msearch output (LeanSearch unavailable, LeanFinder available, grep available), with project,
source and DAG searches as well. No existing definition states this notion. The item gains
this dependency without changing its statement or proof. There are no dependency modules.

## Second reading by M1

Independent reading against the item node, both delivered modules, every statement
 dependency node, and the actual Stacks TeX. Downloaded more-algebra.tex, algebra.tex,
and tags/tags into scratchpad because this clone lacks the literature checkout.
Read 07NN at more-algebra.tex:9769, 07NQ at :10081 (especially the choice of t₁=p),
00KU at algebra.tex:14615, and 0327 at :44872. The surrounding dimension discussion
assumes a Noetherian local ring; no additional base field, finiteness, characteristic,
or separability hypothesis is implicit in 07NN.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- A and B, commutative Noetherian local rings: independent `Type u`, `Type v`,
  `CommRing`, `IsLocalRing`, `IsNoetherianRing` binders. No extra instance is assumed.
- Maximal-ideal completeness of both: the two input `IsAdicComplete` instances.
- Given local map f: `(f : A →+* B) [IsLocalHom f]`.
- Existence of complete regular local R and S: existential coefficient types and ring
  structures, natural variable counts, `let R := MvPowerSeries (Fin n) ΛA`, analogous S,
  existential `IsRegularLocalRing` witnesses and both output completeness predicates.
  Choosing literal power-series representatives transports the abstract witnesses by
  ring isomorphism; it does not change this existence assertion.
- Power series over fields in residue characteristic zero: `CharZero (ResidueField A)
  → IsField ΛA ∧ IsField ΛB`. IsField supplies inverse existence for the chosen ring
  operations, rather than changing those operations.
- Power series over Cohen rings in residue characteristic p: universal prime p with
  `CharP (ResidueField A) p`, then domain and DVR witnesses for each coefficient ring,
  maximal ideal equal to `Ideal.span {(p : Λ)}`, and maximal-ideal completeness.
  DVR nonfieldness ensures p is nonzero. This uses the dependency's recorded composed
  Mathlib definition, not a private alternative.
- q:R→A and v:S→B, surjective and local: existential ring maps and the two
  `Function.Surjective` and `IsLocalHom` conjunctions.
- u:R→S local, square commutative: `IsLocalHom u` and `v.comp u = f.comp q`.
- Flatness of u: `u.Flat`, using precisely u's induced algebra/module structure.
- Regular closed fibre: `IsRegularLocalRing (S ⧸ (maximalIdeal R).map u)`.
  Ideal.map is extension, so this is S/m_R S rather than a different quotient.
- Ordered regular parameters of R: existential `t : List R` with the delivered
  `IsLocalRing.IsRegularSystemOfParameters t`.
- Images extend to ordered regular parameters of S: existential `z : List S` with
  that same predicate on `t.map u ++ z`; the given images form the initial segment.
- First parameter p in positive residue characteristic: `t.head? = some (p : R)`
  for every prime p realizing the residue characteristic. This explicitly includes
  nonemptiness and uses the same t, chosen after q,v,u. All quantifiers agree.

Dependency audit: opened the Noetherian, completion, power-series, Cohen-ring, flat-map,
and regular-scheme nodes and their recorded signatures. Read Mathlib Noetherian/Defs
(IsNoetherianRing and ideal finite generation), AdicCompletion/Basic (IsAdicComplete
and of_bijective_iff), MvPowerSeries/Basic (coefficient families), DiscreteValuationRing/Basic
(class and irreducible_iff_uniformizer), RingHom/Flat (f.toAlgebra), RegularLocalRing/Defs
(class extends local and Noetherian), Algebra/Field/IsField, and Units/Hom (IsLocalHom).
The regular-scheme dependency's ring clause is used, not its scheme clause. All are
usable as recorded; no dependency module is needed.

New definition node read independently as stage 1: its finite ordered list generates
m and has length equal to Krull dimension, exactly 00KU(2). Span equality entails
membership of each parameter in m. Noetherian and local instances match the source;
regularity follows from the condition and is not an extra hypothesis. Its body is a
real Prop expression, not sorry. Its fields, chapter, unit, ancestor/via, cited
Noetherian/regular-ring notions and three search kinds satisfy brief-stage2 §5.
Found and corrected its source label from `definition-system-parameters` to
`definition-regular-local`, verified by tags/tags and algebra.tex. No mathematical
statement, Lean signature, proof, or dependency was changed.

Edge cases: Fin 0 allows zero variables. In dimension zero, t=[] generates the zero
maximal ideal of a field; the extension list can also be empty. Positive residue
characteristic with n=0 still presents over a Cohen DVR, with t=[p], so a false empty
head is excluded exactly where required. Both equal and mixed characteristic are
covered: only residue characteristic determines the coefficient case. A local map
induces a residue-field embedding, hence both residue characteristics agree. Zero
rings are excluded by the source's local-ring assumption (IsLocalRing extends
Nontrivial). There are no schemes or arbitrary index families here. Universes u,v
are independent; coefficients may be chosen in max u v (Cohen construction and
finite-variable series need no larger cardinal universe). No variables or universes
are unbound.

Independent searches, using different wording from the first reader:

- msearch loogle `MvPowerSeries, IsRegularLocalRing`: zero results.
- msearch leanfinder "A local map between complete local Noetherian rings lifts to a
  flat map of regular local power series rings preserving a minimal generating tuple
  of maximal ideals": eight results, about formally smooth maps and adic-completion
  lifts/flatness; none states this presentation.
- msearch leanfinder "An ordered tuple of dimension many elements generating the
  maximal ideal in a Noetherian local ring is a regular system of parameters": eight
  results concerning regular sequences, dimension formulas and DVRs; no parameter
  predicate. A regular sequence alone is not a regular system of parameters.
- rg case-insensitively for `parameter(s)? system`, `system.?of.?parameter`,
  `regular.?system`, `cohen.?presentation`, `cohen.?structure`, and
  `embed.*complete.*local` over Mathlib/RingTheory, WeilConjectures, and repository
  lean/Sheaf: no hits. Parsed DAG definition-node titles/statements for "system of
  parameters": no existing node. The worker's LeanSearch outage was recorded honestly;
  the successful independent semantic and type searches add no matching declaration.

H5/H6/H8/H9: neither definition contains sorry; the only theorem proof is sorry.
Docstrings identify the correct blueprint nodes and sources; the theorem docstring
contains all five proof steps, including the lift, variable adjunction, commutative
square, parameters, flatness and closed fibre. Imports are used, declarations have
upstream namespaces, and line lengths obey the convention. Recorded lean.statement
strings equal the signatures verbatim. No statement correction/citer audit is needed.

Validation: scompile.py compiled both modules together in dependency order on the
server, exit 0, in 1.7 seconds, without errors or warnings. The review found no H3
mathematical mismatch; the sole change is the new definition node's TeX source label.
