## Worker report

The module `Sheaf.RingTheory.SimpleFiltration` states
`Module.exists_simple_filtration_of_length_lt_top`, with its sole proof `sorry`.
No new definitions, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- An R-module M: `(M : Type v) [AddCommGroup M] [Module R M]`.
  Universes u and v are declared independently and explicitly.
- Finite length, length_R(M) < infinity: `(hM : Module.length R M < ⊤)`.
- An integer r >= 0: `∃ (r : ℕ)`; natural numbers encode exactly the nonnegative integers.
- R-submodules M_0 through M_r: `(F : Fin (r + 1) → Submodule R M)`.
- M_0 = 0 and M_r = M: `F 0 = ⊥ ∧ F (Fin.last r) = ⊤`.
- Every adjacent inclusion is strict: `∀ i : Fin r, F i.castSucc < F i.succ`.
- Every successive quotient is simple: `∀ i : Fin r, IsSimpleModule R
  (↥(F i.succ) ⧸ Submodule.comap (F i.succ).subtype (F i.castSucc))`.
  The comap regards the lower submodule as a submodule of the upper term;
  since the lower term is contained in the upper term, this is exactly the
  quotient M_(i+1)/M_i. The quotient has its inherited R-module structure.
  `IsSimpleModule` includes both nonzeroness and the absence of other submodules.

Dependency declarations read and used:

- `def-weil-pbc-module-length` is a Mathlib leaf with `mathlib_match`
  `Module.length`, from `Mathlib.RingTheory.Length`. Its definition is the
  submodule lattice's Krull dimension, unbot to ℕ∞, matching the node's length.
- `def-weil-pbc-simple-module` is a Mathlib leaf with `mathlib_match`
  `IsSimpleModule`, from `Mathlib.RingTheory.SimpleModule.Basic` (transitively
  imported by Length). Its superclass `IsSimpleOrder (Submodule R M)` says the
  submodule lattice is nontrivial and every element is bottom or top.

Edge cases checked before writing: when M is zero, take r = 0 and the sole
term equal to bottom = top; `Fin 0` makes both conditions on adjacent pairs
vacuous, so no zero quotient is required to be simple. A nonzero simple module
admits r = 1. A zero ring forces its modules to be zero and is allowed; no
`Nontrivial R` or `Nontrivial M` is assumed. Arbitrary characteristic is allowed.
Only finite length is assumed; no finite cardinality or finite-dimensional
vector space assumption is added.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py G1
lem-weil-pbc-finite-length-module-simple-filtration`:

- `leanfinder`: "A finite length module admits a finite strictly increasing
  filtration of submodules from zero to the whole module with simple successive
  quotients". Eight hits include `isFiniteLength_iff_exists_compositionSeries`,
  `exists_compositionSeries_of_isNoetherian_isArtinian`,
  `Module.length_compositionSeries`, and `Module.length_ne_top_iff`.
  Their signatures were read: these are ingredients rather than the explicit
  filtration statement with this length hypothesis and simple quotients.
- `loogle`: `Module.length, IsSimpleModule`. Two hits:
  `Module.length_eq_one` and `Module.length_eq_one_iff`; neither is the statement.
- `grep`: `exists.*(filtration|compositionSeries)|simple.*filtration`, subdirectory
  `RingTheory`. Eleven hits, all composition-series ingredients or their uses.
- `leansearch`: "finite length module admits filtration with simple successive
  quotients". Service unavailable (Internal Server Error); no verdict inferred.
- Local `rg -n` for `simple.*filtration|filtration.*simple|exists.*compositionSeries|
  lem-weil-pbc-finite-length-module-simple-filtration` in source
  `WeilConjectures` and project `lean/Sheaf`: only the natural-language reference
  in `Sheaf/Paper/ArtinianIdealLengthOneFiltration.lean`, no existing declaration.
- Local `rg -n` for `simple_filtration_of_length_lt_top|exists_simple_filtration`
  in `dag/lean_names_upstream.json`, Mathlib, source `WeilConjectures`, and
  `lean/Sheaf`: no name clash.

The local Stacks source checkout is absent. Read the source online instead:
[02LY](https://stacks.math.columbia.edu/tag/02LY) defines length via strict chains,
[00J1](https://stacks.math.columbia.edu/tag/00J1) defines simple modules, and
[00J3](https://stacks.math.columbia.edu/tag/00J3), part (2), gives simple factors
of a maximal chain. The declaration docstring carries both proof steps from
the DAG: existence of a longest chain and refinement if a quotient is not simple.
No statement fault or dispute was found.

Server validation: `scompile.py G1
lem-weil-pbc-finite-length-module-simple-filtration
<SimpleFiltration.lean>` compiled cleanly in 1.3 seconds, exit code 0, no warnings.

## Second reading by G1

I reread the node and the source places (Stacks Algebra Tags 02LY, 00J1, and
00J3) against `Sheaf.RingTheory.SimpleFiltration`.

The objects and hypotheses match item by item: `R : Type u` with
`[CommRing R]` is the commutative ring; `M : Type v` with
`[AddCommGroup M] [Module R M]` is its module; and
`hM : Module.length R M < ⊤` is finite length.  The conclusion's
`∃ r : ℕ` is the integer (r\ge0), and
`F : Fin (r + 1) → Submodule R M` is the chain
`M_0,\ldots,M_r`.  `F 0 = ⊥` and `F (Fin.last r) = ⊤` give the endpoints;
`∀ i : Fin r, F i.castSucc < F i.succ` gives all strict adjacent inclusions;
and the final universal quantifier gives simplicity of every successive
quotient, with
`Submodule.comap (F i.succ).subtype (F i.castSucc)` the lower submodule viewed
inside the upper one.  The conjunction nesting and quantifier order are the
same as the node.

The source's edge cases are represented: `r = 0` permits the zero module,
with both endpoint equalities and no adjacent or quotient obligations;
`r = 1` handles a nonzero simple module.  No nontriviality, characteristic,
finite-cardinality, Noetherian, or universe restriction is added.  The zero
ring and arbitrary universes are allowed by the binders.

I searched Mathlib and the project/source with LeanFinder, Loogle, grep, and
`msearch.py`; only composition-series ingredients (`Module.length`,
`isFiniteLength_iff_exists_compositionSeries`, and
`covBy_iff_quot_is_simple`) were found, and no existing declaration states
this explicit filtration.  The source confirms that 00J3 asserts simple
successive quotients for a maximal chain (and also identifies its length),
while the node intentionally retains only the existence conclusion.

No mismatch was found, so no Lean or node change was required.  The module
was recompiled with `scompile.py` and remains clean apart from its permitted
`sorry` proof.
