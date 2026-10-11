## Worker report

The module `Sheaf.RingTheory.FibreRingNoetherian` states
`Ideal.isNoetherianRing_tensorProduct_residueField`, with only `sorry` as proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- The commutative rings are `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  Independent explicit universes impose no size restriction relating the rings.
- The homomorphism A → B is the structure map of `[Algebra A B]`. Every ring
  homomorphism between commutative rings equips B with precisely this algebra
  structure (`RingHom.toAlgebra`); no injectivity or finiteness is assumed.
- B Noetherian is `[IsNoetherianRing B]`.
- The prime ideal of A is `(p : Ideal A) [p.IsPrime]`.
- Its residue field A_p / pA_p is Mathlib's `p.ResidueField`.
- The conclusion is `IsNoetherianRing (B ⊗[A] p.ResidueField)`, using exactly
  the tensor-factor order in the node, rather than the reversed `p.Fiber B`.

Dependency declarations read and used:
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, defined as Noetherian over itself;
  its docstring and `isNoetherianRing_iff_ideal_fg` identify this with finite
  generation of every ideal.
- `def-weil-pbc-localization-at-prime`: the recorded Mathlib matches are
  `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and
  `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
  Read their full definitions and docstrings. The statement uses the second;
  it is the residue field of `Localization.AtPrime p`, hence the required
  quotient. The third has reversed tensor factors and is not needed in the
  signature. The first is used through the residue-field definition.
- The tensor ring structure and notation use
  `Mathlib.RingTheory.TensorProduct.Basic`.

Source check: the literature checkout is absent on this machine. Read the
primary Stacks pages instead: https://stacks.math.columbia.edu/tag/00E6
(Remark 10.18.5, fibre identified with the localization quotient) and
https://stacks.math.columbia.edu/tag/00FN (Lemma 10.31.1, localization
permanence and the quotient argument in its proof). They require no
Noetherian hypothesis on A. The docstring carries all three proof steps of
this node and names each proof dependency.

Edge cases checked before writing: B may be the zero ring, and a nonzero B
may have zero fibre when p is outside the image on spectra. Both are allowed;
the zero ring is Noetherian. A cannot be the zero ring when it has a prime,
which is already enforced by `p.IsPrime`, so no additional hypothesis is
needed. There is no finite-type, flatness, localness, characteristic, or
Noetherian-A restriction. The argument works in every characteristic and
for p = 0 when A is a domain. No disputed statement or node fault found.

Searches (2026-10-11):
- msearch leansearch: "The tensor product of a Noetherian algebra with the
  residue field of a prime of its base ring is Noetherian". Service unavailable
  (Internal Server Error); no result inferred.
- msearch leanfinder: "The fibre ring B tensor over A the residue field of a
  prime ideal is Noetherian if B is Noetherian". Eight hits, including
  `Algebra.QuasiFinite.finite_fiber`, `isNoetherian_of_liesOver`,
  `Algebra.EssFiniteType.isNoetherianRing`, and `IsNoetherianRing.of_finite`.
  None has exactly this statement: they impose different hypotheses or
  concern different module/ring conclusions.
- msearch loogle: `IsNoetherianRing, Ideal.ResidueField`. Zero hits.
- msearch grep: `IsNoetherianRing|isNoetherianRing` in
  `RingTheory/LocalRing/ResidueField`. Zero hits.
- rg across Mathlib, WeilConjectures and lean/Sheaf:
  `IsNoetherianRing.*(Fiber|⊗)|isNoetherianRing.*[Ff]iber|[Ff]iber.*isNoetherianRing`.
  Hits are local proof-body facts under finite-type hypotheses and specific
  formal-fibre statements; no declaration for the node. Read the local fact
  in `WeilConjectures/RingTheory/RelativeComponentConstructible.lean:151`:
  it uses finite type over the residue field and does not state this lemma.
- rg in WeilConjectures and lean/Sheaf for fibre/fiber with Noetherian:
  geometric-fibre scheme instances and specialized formal-fibre results,
  no exact match.
- rg for the blueprint id in WeilConjectures: no matches.
- rg for `isNoetherianRing_tensorProduct_residueField` in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no collision.

Validation: server single-file compilation succeeded (exit code 0, 1.3 s),
with no errors or warnings. All variables and universes are explicit.
Independent second reading is reserved for the second reader.

## Second reading by J1

Read the sandbox node and module independently against both statement dependencies.
The local literature checkout is absent. Read the actual upstream Stacks `.tex`
via `https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex`
and `more-algebra.tex`: algebra's `section-conventions`,
`remark-fundamental-diagram` (00E6), `section-Noetherian` (00FM),
`lemma-Noetherian-permanence` (00FN), and more-algebra's
`lemma-filtered-colimit-etale-noetherian-fibres` (0AH1). Also checked the
primary rendered pages https://stacks.math.columbia.edu/tag/00E6,
https://stacks.math.columbia.edu/tag/00FN and
https://stacks.math.columbia.edu/tag/0AH1. The conventions allow the zero
ring and require commutative unital rings. The diagram in 00E6 has only a
ring map and a base prime; the localization and quotient argument of 00FN
requires only that the ring being localized is Noetherian. The etale-colimit
assumption of 0AH1 is not needed for its incidental Noetherian-fibre assertion.

Object/hypothesis/conclusion list and exact correspondence (H3):

- Objects A and B, arbitrary commutative unital rings: `{A : Type u}`,
  `{B : Type v}`, `[CommRing A]`, `[CommRing B]`. Verdict: exact; no domain,
  field, local-ring, nonzero-ring, or common-universe restriction.
- Object the ring map A to B: `[Algebra A B]`, with map `algebraMap A B`.
  Read `RingHom.toAlgebra` and `RingHom.algebraMap_toAlgebra` in Mathlib's
  `Algebra/Algebra/Defs.lean:197,205`; every commutative-ring map is represented
  and recovered exactly. Verdict: no extra hypothesis on the map.
- Hypothesis B Noetherian: `[IsNoetherianRing B]`. Read dependency
  `def-weil-pbc-noetherian-ring` and its recorded signature, then
  `Noetherian/Defs.lean:196-205`: Noetherian as a self-module is exactly all
  ideals finitely generated. Verdict: exact, and A is not assumed Noetherian.
- Object p and hypothesis p prime: `(p : Ideal A) [p.IsPrime]`.
  Verdict: arbitrary base prime, introduced after the ring map as in the node.
- Object kappa(p) = A_p / pA_p: `p.ResidueField`. Read dependency
  `def-weil-pbc-localization-at-prime` and all its recorded Mathlib matches:
  `Localization.AtPrime` (`Localization/AtPrime/Basic.lean:57`),
  `Ideal.ResidueField` (`LocalRing/ResidueField/Ideal.lean:33`), and
  `Ideal.Fiber` (`LocalRing/ResidueField/Fiber.lean:66`). Also read
  `IsLocalRing.ResidueField` (`ResidueField/Defs.lean:30`) and
  `IsLocalization.AtPrime.map_eq_maximalIdeal` (`AtPrime/Basic.lean:524`).
  Together these identify the actual quotient by pA_p, with its canonical
  A-algebra structure. Verdict: exact, no private residue-field definition.
- Object fibre ring and the sole conclusion: `B ⊗[A] p.ResidueField` and
  `IsNoetherianRing (B ⊗[A] p.ResidueField)`. Verdict: exact tensor-factor order
  and conclusion. The dependency's `p.Fiber B` has reversed factors; writing
  the tensor product directly uses Mathlib's same tensor notion, not a new
  fibre definition. No conclusion about module finiteness is substituted.

Edge cases: zero B is allowed and yields a Noetherian zero fibre; nonzero B
can also yield zero fibre (A = Z, B = Q, p = (2)). No `Nontrivial` instance
is required for B or the fibre. Zero A has no prime, matching the source's
vacuous case. For a domain A, p = 0 is allowed. Independent universes u and v
cover arbitrary ring sizes. All characteristics are covered. No index set,
scheme, or natural-number parameter occurs, so empty-index, empty-scheme,
and n = 0 cases introduce no extra obligation here.

Independent searches, 2026-10-11 (H4):

- msearch loogle `IsNoetherianRing, TensorProduct`: eight hits, Rees-algebra
  and adic-completion statements; their signatures involve different rings
  or finite-module hypotheses, not this assertion.
- msearch leanfinder `localizing a Noetherian target algebra and reducing
  modulo a prime ideal of the base gives a Noetherian fiber`: eight hits,
  including `IsLocalization.isNoetherianRing`, quasi-finite fibre finiteness,
  and Noetherian quotient modules. None states this fibre-ring result.
- msearch leansearch `For an arbitrary ring map into a Noetherian commutative
  ring, its fiber over any base prime is a Noetherian ring`: unavailable
  (Internal Server Error); no no-match verdict inferred.
- Independent rg in Mathlib/RingTheory, WeilConjectures, and lean/Sheaf for
  Noetherian near fiber/fibre/residuefield/tensorproduct in either order.
  Inspected the finite-type local fact at
  `WeilConjectures/RingTheory/RelativeComponentConstructible.lean:151` and
  the tensor commutation fact in
  `WeilConjectures/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:1180`;
  both use finite type over a field inside longer proofs. Project formal-fibre
  results are special cases with additional hypotheses. Read
  `IsLocalization.isNoetherianRing` and
  `Algebra.EssFiniteType.isNoetherianRing` in `Localization/Submodule.lean`:
  these are ingredients requiring an additional localization/essentially
  finite-type argument, not the existing statement of this node.
- rg for the item id and proposed declaration name in WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: only other modules' proof
  citations of the item; no declaration collision or existing exact result.

H5-H9: no definitions or auxiliary theorems are added; the single proof is
`by sorry`. The declaration docstring gives each of the node's three proof
steps and its dependency ids: localization-quotient identification, Noetherian
localization, and surjective image via the inverse identification. Source and
blueprint markers occur in both docstrings. Imports supply Noetherian,
residue-field, and tensor-ring structures; topic, namespace, and line lengths
follow the example. Universes u and v and all ring variables are bound.
There are no new nodes, dependency modules, or statement corrections, so H12,
H13, and corrected-statement citer review do not arise.

Mismatches and repairs: none found. Kept the module and node record unchanged;
appended this independent reading and its searches only. Verified the stored
`lean.statement` is verbatim equal to the signature before `:=`.
Server scompile of the module succeeded, exit 0, 1.3 seconds, with no errors
or warnings. Delivery dry run and push are performed after this reading.

## Reviewer fix (R-frn1008, 2026-10-11)

FIX (H4, one definition per notion): the fibre ring is written as Mathlib's `p.Fiber B`
(`= κ(p) ⊗[A] B`, `Ideal.Fiber`), the form accepted for fibre rings in landed modules
(E1 846bd08dc, F1 c84d7f11f, PolynomialFormalFiber), instead of the hand-written
`B ⊗[A] p.ResidueField`; the factor order of the node is identified with it by
`Algebra.TensorProduct.comm`. Declaration renamed `Ideal.isNoetherianRing_fiber`; import
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber` replaces the residue-field and tensor imports.
Hypotheses unchanged (arbitrary commutative A, B; B Noetherian; p prime; A not Noetherian, no
finite type). Not `existing: true`: `Algebra.FiniteType.isNoetherianRing` needs finite type of
the fibre over κ(p), which the node does not assume. Recompiled clean as L.
