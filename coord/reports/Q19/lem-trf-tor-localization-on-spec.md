## Worker report

The delivery states `lem-trf-tor-localization-on-spec` in
`Sheaf.RingTheory.TorCoefficientLocalization` and adds the missing all-degree
coefficient-action interface in `Sheaf.RingTheory.TorCoefficientModule`.
No mathematical statement is corrected. Only `lean` and the permitted new-definition
addition to the item's `stmt_deps` change. Every theorem proof is `sorry`.

Hypotheses and clauses, read against the original item:

- The commutative rings are `(R A : Type u) [CommRing R] [CommRing A]`.
  `[Algebra R A]` is the arbitrary specified ring homomorphism `R → A`;
  commutative-ring homomorphisms give exactly these algebra structures.
- The arbitrary `R`-module is `(M : ModuleCat.{u} R)` and the nonnegative
  degree is `(n : ℕ)`. These bind all objects and degrees, including zero.
  The common universe can be chosen large enough for any given rings and module;
  no quantification over a smaller universe of test rings or modules occurs.
- A prime is `p : PrimeSpectrum A`, its ideal is `p.asIdeal`, and its localization
  is exactly `Localization.AtPrime p.asIdeal`, the recorded dependency declaration.
- `torCoefficientModule R A M A n` has the underlying additive group of
  `(((Tor' (ModuleCat R) n).obj M).obj (ModuleCat.of R A))` definitionally.
  Its coefficient action is the functorial image of multiplication on `A`.
  For `B = A_p`, `torCoefficientModule R A M B n` similarly has the exact
  underlying Tor group over the original base ring `R`, with its coefficient
  `A`-action. The base ring is not changed to `A` or to `A_p`.
- The source localization is `LocalizedModule p.asIdeal.primeCompl` of that
  exact coefficient module. `torCoefficientLinearMap` is the actual map of
  `Tor'` induced by the underlying `R`-linear algebra homomorphism.
  `torCoefficientLocalizationMap` is `LocalizedModule.lift` of this map for
  `Algebra.ofId A A_p`. Its denominator inverses are justified by the named
  theorem `torCoefficientLocalization_units`. Thus it is the canonical map,
  not an arbitrary map, an unspecified equivalence, or a choice of Tor groups.
  `LocalizedModule.lift_mk` gives its fraction formula; in particular it sends
  `t/1` to the functorial coefficient image of `t`.
- The first conjunct says `∀ p, Function.Bijective` of this precise linear map.
  A bijective linear map is precisely an isomorphism of modules. The target's
  `A_p` action can also be used, but bijectivity of the canonical map already
  states the full isomorphism assertion, without assuming a new action.
- The second conjunct says `Subsingleton` of the original Tor group iff
  `Subsingleton` of every localized-coefficient Tor group. For an additive group
  this is exactly vanishing. It states both directions, not just the consequence
  from global to local vanishing. Primes are quantified inside the conclusion,
  so a prime does not become a hypothesis of the global criterion.

Dependency declarations read and used:

- `def-weil-pbc-tor-modules`: `Mathlib.CategoryTheory.Monoidal.Tor`,
  `CategoryTheory.Tor'`. Read the full definition and docstring: it derives the
  first argument, as the node requires. The helper constructs an action on that
  group; it does not compute a new derived functor or replace the dependency.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Read its definition `Localization p.primeCompl` and localization docstring.
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`,
  `LocalizedModule.mkLinearMap`, `LocalizedModule.lift`, and `lift_mk`.
  Read the fraction relation, action, lift signature and its universal property.
- New definition `def-trf-tor-coefficient-module`:
  `ModuleCat.torCoefficientModule`, `ModuleCat.torCoefficientAction`, and
  `ModuleCat.torCoefficientLinearMap`, in `Sheaf.RingTheory.TorCoefficientModule`.
- Stated proof dependencies are imported without `public`:
  `Mathlib.RingTheory.Flat.Localization` (`IsLocalization.flat`),
  `Mathlib.RingTheory.Localization.BaseChange` (`IsLocalizedModule.rTensor`,
  `IsLocalizedModule.map_lTensor`), and
  `Mathlib.RingTheory.LocalProperties.Exactness` (`bijective_of_localized_maximal`).
  Read all their recorded signatures/docstrings. `lem-trf-tor-flat-base-change`
  has no recorded declaration on the read-only base, so there is no module to
  import yet; it is a proof dependency only, and is included in the proof docstring.

Edge cases checked before and after writing:

- `n=0`: the map is tensor localization `M tensor_R A → M tensor_R A_p`.
  Nothing assumes `0 < n`; the action and maps are defined for zero too.
- `M=0`: all Tor groups vanish, and the canonical map is a map between zero modules.
- `A=0`: `PrimeSpectrum A` is empty, so the first conjunct and local side of the
  vanishing criterion are vacuous, while Tor with coefficient zero is zero.
  In particular, the theorem has no selected-prime hypothesis and no `Nontrivial A`.
- `R=Z`, `A=Z/2`, `M=Z/2`: nonflat coefficients are permitted. The nonzero
  degree-one Tor is localized in its coefficient action. No flatness over `R`
  is imposed; only the localization is flat over `A` in the proof plan.
- `R=Z[x]`, `A=Z` via `x ↦ 0`, `M=Z`: degree-one Tor is `Z`, and localization
  gives `Z_(l)`. The target remains Tor over `R`, not Tor over the coefficient ring.
- Zero divisors in `R` and `A` are allowed. There is no finite-generation,
  Noetherian, flatness, faithfulness, domain, or characteristic hypothesis.

Searches performed (msearch logs are retained in the sandbox):

- LeanFinder: “Localization of the coefficient ring commutes with Tor over a
  fixed commutative base ring”: eight localization/tensor hits, including
  `IsLocalizedModule.rTensor`, `map_lTensor` and
  `IsLocalization.tensorProduct_isLocalizedModule`; no Tor-localization theorem.
- Loogle: `CategoryTheory.Tor, IsLocalizedModule`: zero hits.
- Mathlib grep: `Tor.*localiz|localiz.*Tor` in `RingTheory`: 25 unrelated
  localized-module/local-property hits, no Tor coefficient theorem.
- LeanSearch: “The natural coefficient algebra module structure on Tor over a
  commutative base ring”: eight tensor-module/action hits, no Tor action interface.
- Loogle: `ModuleCat.mkOfSMul, CategoryTheory.Tor`: zero hits.
- LeanFinder: “For a fixed module M, Tor is additive in coefficient homomorphisms
  and the coefficient algebra acts functorially”: eight hits, including `Rep.Tor`
  and `ModuleCat.instMonoidalPreadditive`; no required coefficient interface.
- Mathlib grep: `torCoefficient|TorCoefficient|torSecondFunctor`: zero hits;
  `Tor.*[Mm]odule|torCoefficient|TorCoefficient` in `CategoryTheory/Monoidal`:
  12 unrelated module-category hits.
- Direct `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no proposed declaration names. The item-id
  search found no upstream statement. Broader action searches found
  `CategoryTheory.torOneModule` and `torOneCoefficientMap` in
  `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle`; I opened the full declarations.
  They cover only degree one, and cannot state the present all-degree theorem.
  They do not provide a generic coefficient-module construction to reuse.
- DAG searches and `tools/blueprint_refs.py search 'Tor coefficient'` found no
  all-degree coefficient-action definition node (the blueprint search returned
  four unrelated nodes). Existing first-degree additivity/linearity nodes are
  specifically degree one. `blueprint_refs.py ancestor` gives
  `lem-trf-local-term-locality` for the new node's ancestry.

Source check: opened the local `algebra.tex` section Functorialities for Tor,
Tag 00M7, especially item (1), and the following Lemma 00M8 and its proof.
00M8 itself changes the base ring; the item's citation explicitly uses its
free-resolution argument for flat change in the coefficient ring. The Lean keeps
`R` fixed exactly as the item requires. The local tags table confirms
00LY, 00M7, 00M8, 00DK and 00HN.

There is no `STATEMENT-DISPUTED` flag and no node fault.

## New nodes

`def-trf-tor-coefficient-module` supplies the canonical all-degree coefficient
algebra action on the existing Tor group and its canonical map for algebra
homomorphisms (Stacks Tags 00LY and 00M7(1)). Its definition uses
`Module.toModuleEnd`, `ModuleCat.endRingEquiv`, functorial endomorphism/additive
maps, and `ModuleCat.mkOfSMul`. All data is explicit. The two postponed helper
theorems are precisely the additivity and scalar compatibility included in the
new node's statement, with complete resolution/naturality proofs in docstrings.
They supply proof fields only; no object is chosen from an unproved existence
statement. Search results, including the degree-one-only existing interface,
are recorded in the node's `mathlib_searches`. It cites the recorded Tor definition
and is cited directly by the item. There are no dependency-record repairs.

## Second reading by Q19

I reopened the node copy and both modules for a separate manual rereading in this
single-worker dispatcher session. The maintainer performs the independent review;
no second agent was started and this section does not claim another reviewer.
The commutative-ring/algebra binders, arbitrary module, degree, prime complement,
fixed original Tor base ring, actual functor-induced coefficient map, localized
source, bijectivity and both vanishing directions match clause by clause as above.
The helper's scalar map is obtained from multiplication on the original coefficient
module and then functoriality, so it cannot accidentally select a trivial action.
The source of the extension is the localized Tor group, not the localization of
`M` or of `R`. The canonical map's target is Tor with coefficient `A_p`, not Tor
over `A_p`. `Subsingleton` is applied to additive group types, and no claim of
`IsZero` on a bare type is used. The helper's map on elements is the exact map of
`Tor'`, with its scalar-compatibility theorem supplying only a proof field.
The zero-ring rereading confirms that primes occur under `∀`, preserving the
empty-spectrum case. No mismatch or mathematical change was found.

Validation: both modules compiled cleanly through the prescribed `scompile.py`,
separately in dependency order, with the default 60-second per-file limit.
All variables and the universe are explicit; there is no file-local notation,
local instance, private declaration, `let` in a statement, or theorem proof other
than `sorry`. The localization module imports every currently stated proof
prerequisite. The final delivery preflight and compile are recorded below.

Dry run: `deliver2.py Q19 lem-trf-tor-localization-on-spec --no-push` returned
`OK (dry run): commit 176339cef2 passes the preflight and compiles; nothing pushed`.
The only first-run preflight issue was that the definition's recorded signature
included the preceding `noncomputable`; the record now starts at `def`, as required
by the checker. No Lean statement or construction changed for that record repair.
