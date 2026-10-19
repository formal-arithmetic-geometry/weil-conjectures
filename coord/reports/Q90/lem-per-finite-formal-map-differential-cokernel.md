## Worker report

The module `Sheaf.RingTheory.FiniteFormalMapDifferentialCokernel` states
`KaehlerDifferential.finite_formal_map_differential_cokernel`, with its whole proof `sorry`.
It introduces no definitions, helper theorems, new nodes, or dependency repairs. The node is
unchanged except for `lean`. There is no statement dispute or correction.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IV 1.2.5, printed p. 49,
and IV 2.1.12, printed pp. 52--53, in the supplied PDF. Section 1.2.5 gives completed
universal differentials and the continuous-derivation characterization. Section 2.1.12
identifies finite ordinary relative differentials with their completion and displays the
completed transitivity sequence. The module docstring records all six proof steps of the
node, including residue generators, completion, topological Nakayama, relative finiteness,
the canonical right arrow, truncation, and the inverse from universal derivations.

Hypotheses and objects, individually:

- The field `k` is `(k : Type u) [Field k]`.
- The commutative local `k`-algebra is `(B : Type v) [CommRing B] [Algebra k B]
  [IsLocalRing B]`. Its specified maximal ideal is `IsLocalRing.maximalIdeal B`.
- Noetherianity is `[IsNoetherianRing B]`.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal B) B]`, which includes
  separatedness, exactly as required by the recorded completion definition.
- The coefficient field induces the residue isomorphism precisely when `hres` holds:
  `Function.Bijective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)).comp
  (algebraMap k B))`. This is the actual coefficient map followed by the quotient map.
  Its bijectivity, rather than existence of an unrelated residue-field isomorphism,
  retains the source's section condition.
- The nonnegative number of variables is `(e : ℕ)`, with no positivity assumption.
  The ring `R` is literally `MvPowerSeries (Fin e) k`, the recorded power-series notion.
- The supplied map `φ` is encoded by `[Algebra (MvPowerSeries (Fin e) k) B]`.
  Its underlying map is `algebraMap (MvPowerSeries (Fin e) k) B`. Quantification over
  these algebra structures is quantification over the supplied ring maps; this does not
  impose an embedding or a choice of parameters. `[IsScalarTower k
  (MvPowerSeries (Fin e) k) B]` says exactly that this map respects the given coefficient
  map, hence that it is a `k`-algebra map. Localness is the explicit
  `[IsLocalHom (algebraMap (MvPowerSeries (Fin e) k) B)]`.
- Finiteness of `B` over the supplied power-series ring is
  `[Module.Finite (MvPowerSeries (Fin e) k) B]`.
- Each `bᵢ` is written directly as `algebraMap (MvPowerSeries (Fin e) k) B
  (MvPowerSeries.X i)`; there is no extra parameter family or identification hypothesis.
- The completed absolute differential module is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal B) (KaehlerDifferential k B)`.
  Mathlib defines this as compatible elements of `Ω/n^mΩ`, with componentwise operations,
  including the harmless zero quotient at `m = 0`. This is the node's inverse limit, not
  the tensor completion used in some other project nodes.

Conclusions and maps, individually:

- The first conjunct `Module.Finite B (AdicCompletion ... (KaehlerDifferential k B))`
  is finiteness of the completed absolute module.
- The second conjunct `Module.Finite B (KaehlerDifferential
  (MvPowerSeries (Fin e) k) B)` is finiteness of the ordinary relative module.
- The third conjunct `IsAdicComplete (IsLocalRing.maximalIdeal B)
  (KaehlerDifferential (MvPowerSeries (Fin e) k) B)` is its adic completeness and
  separatedness. It is a conclusion, not an additional hypothesis.
- The final existential constructs a `B`-linear map `q` from the completed absolute
  module to the ordinary relative module. Its defining clause is, for every `z`,
  `AdicCompletion.of n Ωrel (q z) = AdicCompletion.map n
  (KaehlerDifferential.map k R B B) z`. Here `KaehlerDifferential.map k R B B`
  is the actual universal map carrying `d_{B/k}b` to `d_{B/R}b`, and
  `AdicCompletion.map` is the actual map on compatible quotient sequences.
  Since the preceding completeness conclusion makes `AdicCompletion.of n Ωrel`
  bijective, this equation determines `q` uniquely as its inverse composed with the
  completed universal map. In particular the existential does not weaken the specified
  right arrow to an arbitrary surjection or an assumed comparison.
- `Function.Exact` is applied to the written function on `(c : Fin e → B)`:
  `∑ i, c i • AdicCompletion.of n Ωabs (KaehlerDifferential.D k B bᵢ)`, followed by
  `q`. Thus the first arrow has the specified coefficients, differential symbols and
  completion map, and the image is exactly the kernel of the canonical right arrow.
  Linearity of this first function follows from the displayed formula; no independent
  choice of a map or basis is being made.
- `Function.Surjective q` is exactness at the relative module, namely the terminal
  `Ω[B/R] → 0`. No injectivity of the first arrow is asserted.

Dependency declarations used (read their signatures and docstrings):

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`, `AdicCompletion`, and
  `AdicCompletion.of`, from `Mathlib.RingTheory.AdicCompletion.Basic`. The definition
  of `AdicCompletion` is the subtype of compatible quotient sequences.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`, from
  `Mathlib.RingTheory.MvPowerSeries.Basic`, imported publicly through
  `Mathlib.RingTheory.MvPowerSeries.Inverse` for its local-ring instance.
- `def-weil-finitely-generated-module`: `Module.Finite`, from
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and `KaehlerDifferential.map`, from `Mathlib.RingTheory.Kaehler.Basic`.
  `linearMapEquivDerivation` supplies the universal-property proof route.
- The public `Mathlib.RingTheory.AdicCompletion.Functoriality` import supplies the
  canonical `AdicCompletion.map` in the statement; its value at each quotient is
  `LinearMap.reduceModIdeal` of the universal differential map.
- Proof-only `WeilConjectures.RingTheory.FiniteModuleComplete` supplies the recorded
  `finite_module_complete_over_complete_noetherian`. Its current published source was
  read with `scompile.py --source`, since the older source checkout has no such file.
- Proof-only `Sheaf.RingTheory.FiniteOverCompleteRing` supplies the recorded
  `Module.finite_and_span_eq_top_of_adicComplete` (including chosen generators).
- Proof-only `Mathlib.RingTheory.AdicCompletion.Completeness` supplies
  `AdicCompletion.isAdicComplete` and `AdicCompletion.pow_smul_top_eq_ker_eval`,
  as the `mathlib_match` of `lem-weil-pbc-module-completion-complete` specifies.

Edge cases checked before writing:

- `e = 0`: the empty coefficient tuple has zero sum. The power-series ring in no
  variables is `k`; the claim says the completion maps isomorphically onto the ordinary
  relative differentials. Finite `B/k` makes that module finite and complete, consistent
  with the hypotheses. The residue section forces its residue field to be `k`.
- `B = k` and variable images zero: both differential modules vanish, and both
  exactness and surjectivity are valid. In particular noninjective supplied maps remain
  permitted; no algebraic independence has been added.
- The identity parameter map `k[[T]] → k[[T]]` gives the usual one-generator completed
  differential module and zero relative differentials.
- In characteristic `p`, the finite local map `k[[T]] → k[[x]]`, `T ↦ x^p`, has zero
  left arrow and relative differential module generated by `dx`; the exact statement
  remains valid, without any separability assumption.
- For `B = k[[x]]/(x²)` and `T ↦ x`, the first arrow is still the actual `dx`, whether
  or not `2 = 0`; no freeness or injectivity assertion is implicit in exactness.
- Universes `u` and `v` are independent; finite variable types introduce no size
  restriction on `k` or `B`. Every universe and variable is bound, with
  `set_option autoImplicit false` in the module.

Searches made for an existing declaration:

- `msearch.py ... leanfinder "finite formal power series map completed Kahler
  differentials exact cokernel sequence"`: 8 hits, chiefly Jacobi--Zariski exact
  sequences and finite-presentation results. None gives this completed formal-map
  sequence.
- `msearch.py ... loogle '"KaehlerDifferential", "map"'`: 12 hits. This supplied the
  canonical `KaehlerDifferential.map` and ordinary transitivity
  `exact_mapBaseChange_map`; ordinary transitivity does not identify the completed
  source with the displayed finite free module or give the asserted completion result.
- `msearch.py ... grep 'KaehlerDifferential.*(complete|adic)|completed.*(differential|cotangent)'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "completed Kahler differentials finite formal power series
  algebra cokernel exact sequence"`: 8 hits, including `KaehlerDifferential`,
  `KaehlerDifferential.finite`, and ordinary cotangent presentations. None matches.
- `rg` in `WeilConjectures` and `lean/Sheaf` for completed differentials and the item id:
  no upstream match; the project has continuous differentials, completed Jacobian
  presentations and a comparison theorem for a localized finite-type algebra and a
  separable coefficient section. Opened those modules: they use different inputs and
  tensor-completed or quotient-ring differentials, and none states this finite formal
  parameter map theorem. In particular this theorem uses `AdicCompletion` directly,
  without redefining the project's `Continuous` or `CompletedDifferentials` notions.
- `grep -rn` for the item id in `WeilConjectures`: no hits. The proposed declaration
  name was also searched in `dag/lean_names_upstream.json`, `WeilConjectures` and
  `lean/Sheaf`, with no collision.

Validation: `scompile.py Q90 lem-per-finite-formal-map-differential-cokernel` on the
module succeeded in both the sandbox and library-module contexts (1.7 s and 1.9 s),
with no errors or warnings. The prescribed `deliver2.py --no-push` also passed the
server preflight and per-file compilation, printing `OK (dry run)` (commit ecd5c42367).

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
