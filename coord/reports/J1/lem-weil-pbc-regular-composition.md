## Worker report

The module `Sheaf.RingTheory.RegularComposition` states
`RingHom.IsRegular.comp_of_fiber_noetherian`. It introduces commutative rings
`A`, `B`, and `C`, ring maps `f : A →+* B` and `g : B →+* C`, hypotheses
`hf : f.IsRegular` and `hg : g.IsRegular`, and concludes that the composite
`g.comp f` is regular under the fibre Noetherian hypothesis.

The Lean rendering of each clause is as follows. The two regular-map hypotheses
are `(hf : f.IsRegular)` and `(hg : g.IsRegular)`. For every prime
`p : Ideal A`, the fibre condition is
`IsNoetherianRing (@Ideal.Fiber A _ p _ C _
(@Algebra.toModule A C _ _ (RingHom.toAlgebra (g.comp f))))`; the explicit module
structure is the one induced by the composite ring map. The conclusion is
`(g.comp f).IsRegular`.

The regular-map notion is the recorded declaration `RingHom.IsRegular` from
`Sheaf.RingTheory.GRing`. The Noetherian ring notion is Mathlib's
`IsNoetherianRing`; the fibre is Mathlib's `Ideal.Fiber`, with the composite
algebra structure made explicit. The theorem proof is `sorry`, as required for
stage 2.

Edge cases checked: the source and target rings may be zero rings; no
nonemptiness, domain, characteristic, finite-type, or universe restrictions are
added. The source prime type is in the universe of `A`, and the fibre uses the
composite `A`-module structure, so no independent universe or alternate tensor
order is introduced.

Searches made before writing: `msearch.py leanfinder` for composition of regular
ring maps (no matching declaration); `msearch.py loogle` for regular ring-map
composition (only smooth/flat composition results); `msearch.py grep` and `rg`
over Mathlib and `WeilConjectures` for `G-ring`, `IsRegular`, and geometrically
regular composition (no existing theorem). The project declaration search found
`RingHom.IsRegular` in `Sheaf.RingTheory.GRing`, which is the dependency
recorded by `def-weil-pbc-g-ring`; no duplicate notion was introduced.

## Earlier second reading (a previous round; superseded)

The theorem signature was reread against every clause of the node. `A → B` and
`B → C` are the two explicit ring maps, `hf` and `hg` render the two regularity
hypotheses, and the universal prime/fibre Noetherian clause is retained exactly.
The conclusion is the regularity of the composite. No hypotheses or conclusion
clauses were added, dropped, strengthened, or weakened.

## Second reading by J1

Read the sandbox node and module, all three statement-dependency nodes, and
`Sheaf.RingTheory.GRing` in full. Read the source on the server:
`literature/stacks-project/more-algebra.tex`, lines 10355–10465, including the
section introduction, Definition 07BZ, base change, and Lemma 07QI with its proof.
The section assumes commutative rings, not globally Noetherian rings; geometric
regularity is Noetherianity plus regularity after every finite purely inseparable
residue-field extension. There is no statement correction in this delivery.

The node's complete object/hypothesis/conclusion list and its Lean matching:

- Three commutative rings A, B, C: `(A : Type u) (B : Type v) (C : Type w)`
  with `[CommRing A] [CommRing B] [CommRing C]`. Exact; independent universes
  and no domain, field, local, finite-type or global Noetherian assumptions.
- A ring map A → B: `(f : A →+* B)`. Exact, unital commutative-ring map.
- A ring map B → C: `(g : B →+* C)`. Exact; its source is the same B.
- First map regular: `(hf : f.IsRegular)`. Exact: opened the dependency's
  `RingHom.IsRegular`, which installs `f.toAlgebra` and requires `f.Flat` and
  geometric regularity of every prime fibre. Opened `Algebra.IsGeometricallyRegular`
  too: it includes Noetherianity and all finite purely inseparable field extensions
  in `Type (max u v)`, with `IsRegularRing` as its conclusion. Thus this is the
  source's regular-map notion, not smoothness, regular sequences or schemes.
- Second map regular: `(hg : g.IsRegular)`. Exact, using the same definition
  with the algebra structure induced by g.
- For every prime ideal p of A, the composite fibre is Noetherian:
  `(h : ∀ (p : Ideal A) [p.IsPrime], IsNoetherianRing
  (@Ideal.Fiber A _ p _ C _ (@Algebra.toModule A C _ _
  (RingHom.toAlgebra (g.comp f)))))`. Exact; the module is explicitly induced by
  the composite, with no unrelated algebra or scalar-tower assumption. Opened
  Mathlib `LocalRing/ResidueField/Fiber.lean:66`: `Ideal.Fiber` is
  κ(p) ⊗[A] C; tensor commutativity identifies it with the node's C ⊗[A] κ(p).
  This is the recorded localization/residue-field/fibre dependency, not a private
  fibre definition. Opened `Noetherian/Defs.lean:196` and the ideal-finiteness
  equivalence: `IsNoetherianRing` means every ideal finitely generated.
- Conclusion: `(g.comp f).IsRegular`. Exact; composition has order A → B → C,
  and the same regular-map predicate includes both flatness and every fibre's
  Noetherian geometric regularity. No clause or quantifier is missing or added.

Edge cases: zero commutative rings are allowed. When A has no prime ideals the
fibre premise is vacuous, as in the source, while the regularity hypotheses still
include flatness. Zero B or C and zero fibre rings are not excluded by any
`Nontrivial` assumption; regular rings use Noetherianity and regularity at primes.
No index set or n occurs, so empty-index and n = 0 checks are inapplicable.
All characteristics are allowed; purely inseparable extensions remain those in
the recorded definition, including the identity extension. Every universe is
bound (`universe u v w`), the three rings need not share a universe, and fibre
carriers live in the appropriate maximum universe. No small test universe or
extra class instance restricts the statement.

Independent H4 searches performed using the required msearch tool:

- LeanFinder: "flat ring homomorphisms with geometrically regular fibers closed
  under composition when composite fibers are Noetherian". Eight results,
  including `RingHom.Flat.comp` and smooth/faithfully-flat composition; none has
  the geometric-regularity conclusion of 07QI.
- Loogle: `"GeometricallyRegular"`. Zero hits.
- Mathlib grep: `geometrically.?regular|regular.*ring.*hom|comp_of_fiber_noetherian`
  in RingTheory. Zero hits.
- LeanSearch: "Composition of flat homomorphisms whose fibers are geometrically
  regular, assuming Noetherian fibers of the composite". Service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- Independently used `rg` over the project's `lean/Sheaf` and the source
  `WeilConjectures` for `GeometricallyRegular`, `comp_of_fiber_noetherian`,
  `regular ring map`, and `regular ring homomorphism`. Found the recorded GRing
  definition and related project lemmas, but no existing composition theorem;
  the source library supplied no matching declaration. No duplicate is written.

Mismatch found: H8. The first docstring compressed the three-step DAG proof into
one sentence and omitted the Noetherian base-change argument and the fibre-field
extension argument. Expanded it to all three steps with the dependency IDs:
localization and two finite-type base changes, Noetherianity of C tensor k,
flatness and geometrically regular fibres of B tensor k → C tensor k, the local
031E criterion, and composition of flatness. The signature, node statement,
imports and proof are unchanged. The node's `lean.statement` is verbatim the
module signature. There are no new nodes or dependency modules to audit; the
existing dependency definitions are usable. H5/H6: no definitions or instances
are introduced, and the only theorem proof remains `sorry`. H9: the sole import
is used, the namespace is RingHom, all variables/universes are bound, and the
source references and blueprint tag are present. Compilation and delivery
preflight are run after this review using the prescribed scripts.
