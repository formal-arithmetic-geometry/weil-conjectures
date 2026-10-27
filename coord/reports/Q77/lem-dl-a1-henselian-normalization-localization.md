## Worker report

The module `Sheaf.RingTheory.HenselianNormalizationLocalization` states
`Algebra.henselianNormalization_localization`, with its proof `sorry`. It adds no definition,
new node, dependency repair, or statement correction. The node copy changes only `lean`.
There is no released repair note for this item. All variables and universes are explicitly
bound (`set_option autoImplicit false`), and the file is in module mode.

Sources read: Stacks `pione.tex`, Section Ramification theory (0BSD), setup and the complete
proof of `lemma-identify-inertia` (0BSW); `more-algebra.tex`, statement and proof of
`lemma-integral-over-henselian` (092X). The node isolates the ordinary-henselization part
of the comparison and supplies its six-step direct argument, valid for arbitrary algebraic
Omega/K under the explicitly assumed normal henselian localization hypotheses. Its six
steps are carried in the theorem docstring. The broader existing theorem
`Algebra.henselianGlobalInertiaComparison` requires a separable closure and has additional
strict-henselization data, so it is not this node's statement.

Hypotheses and conclusion, clause by clause:

- A normal local domain: `(A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsIntegrallyClosed A]`. Normal domain uses the dependency's recorded Mathlib meaning,
  not a second normality predicate.
- K = Frac(A): `(K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]`.
  Omega/K algebraic: `(Omega : Type v) [Field Omega] [Algebra K Omega]
  [Algebra.IsAlgebraic K Omega]`. The file uses the symbol `Ω`. The A-algebra on Omega
  and `[IsScalarTower A K Ω]` specify the same ambient embedding. No separability,
  Galois, finite-dimensionality, Noetherianity, or characteristic restriction is imposed.
- B is exactly Mathlib's `integralClosure A Ω`, a subalgebra with carrier
  `{x | IsIntegral A x}`. It is not a variable assumed to be some unspecified normalization.
- q is a maximal ideal of B: `(q : Ideal (integralClosure A Ω)) [q.IsMaximal]`.
  It lies over m_A by `_hq : q.comap (algebraMap A (integralClosure A Ω)) = maximalIdeal A`.
- T is the actual `Localization.AtPrime q`, with its canonical ring structure. Its locality
  and domain property come from localization of the subring B of the field Omega;
  `[HenselianLocalRing (Localization.AtPrime q)]` and
  `[IsIntegrallyClosed (Localization.AtPrime q)]` express the stated henselian normal
  hypotheses. `[Algebra (Localization.AtPrime q) Ω] [IsFractionRing ... Ω]` express that
  Omega is its fraction field, while `_hTΩ` identifies the algebra map with the existing
  canonical `Ideal.atPrimeToField q`. Thus no unrelated map into Omega is substituted.
- H is a henselization of the local ring A: `(H : Type z) [CommRing H]
  [HenselianLocalRing H]`, the algebra over `Localization.AtPrime (maximalIdeal A)`,
  and `_hH : Algebra.IsHenselizationAtPrime' A (maximalIdeal A) H`. The A-algebra and
  scalar tower identify the A-structure. This is the recorded dependency predicate,
  using its full universal property, not an assumed arbitrary henselian algebra.
- H is a domain: `_hHdomain : IsDomain H`. This is an explicit proof binder rather than
  a second overlapping instance; the statement does not require a field instance on
  `FractionRing H` in order to type its algebra map or algebraicity predicate.
- H embeds locally as an A-algebra into T: `[Algebra H (Localization.AtPrime q)]`,
  `[IsScalarTower A H (Localization.AtPrime q)]`, `_hHT : IsLocalHom (algebraMap H ...)`,
  and `_hHTinj : Function.Injective (algebraMap H ...)`.
- The H-algebra on Omega agrees with that embedding by
  `[IsScalarTower H (Localization.AtPrime q) Ω]`; `[IsScalarTower A H Ω]` also fixes the
  common A-structure. The algebra on `FractionRing H` has the canonical H-structure,
  `[Algebra (FractionRing H) Ω] [IsScalarTower H (FractionRing H) Ω]`.
  `[Algebra.IsAlgebraic (FractionRing H) Ω]` is exactly the remaining algebraicity
  assumption. The compatible extension of the embedded H to its fraction field is
  unique; it is not an arbitrary independent field embedding.
- C is exactly `integralClosure H Ω`. Henselian locality is the conclusion
  `∃ (_ : HenselianLocalRing (integralClosure H Ω)), ...`; the dependent existential
  makes its `maximalIdeal` available in the subsequent clause instead of assuming
  the conclusion as an input instance.
- C = T inside Omega is
  `Set.range (algebraMap (integralClosure H Ω) Ω) =
  Set.range (algebraMap (Localization.AtPrime q) Ω)`.
  The first map is the canonical subtype inclusion; `_hTΩ` fixes the second canonical
  inclusion. Equality of these images is precisely equality as subrings of Omega.
- B intersect n = q is the set equality
  `{b : integralClosure A Ω | (b : Ω) ∈
    (integralClosure H Ω).val '' (maximalIdeal (integralClosure H Ω) : Set _)} =
    (q : Set (integralClosure A Ω))`.
  This states contraction in the common field without needing a separately named
  inclusion B -> C or a proof of its well-definedness.
- The subgroup equality is
  `MulAction.stabilizer (Ω ≃ₐ[K] Ω) q =
    (IntermediateField.adjoin K (Set.range (algebraMap (FractionRing H) Ω))).fixingSubgroup`.
  The action on B and ideals is Mathlib's canonical action (with `Pointwise` scope).
  The right side is the subgroup of K-automorphisms fixing the image of Frac(H)
  pointwise; adjoining K adds no fixed-point condition to elements already fixing K.
  This is the requested equality inside G, not only an abstract group isomorphism.

Dependencies used (their recorded declarations, signatures and docstrings were read):

- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with `IsDomain` for the normal-domain specialization.
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`; uses the recorded Mathlib
  `HenselianLocalRing` (the strict henselian class is not needed here).
- `def-weil-pbc-henselization-at-prime`:
  `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`, `Algebra.IsHenselizationAtPrime'`.
  Its test rings live in `Type (max u z)` as the recorded generalized interface prescribes.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure` and `IsIntegral`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its canonical embedding in the field is the already published
  `Ideal.atPrimeToField` in `WeilConjectures.RingTheory.StrictlyHenselianNormal`;
  its full definition and injectivity lemma were read.
- The sole additional proof dependency is imported privately:
  `Sheaf.RingTheory.IntegralComponentHenselianPermanence`,
  `HenselianLocalRing.integral_component_henselian_permanence`. Its connected integral
  algebra statement specializes to the domain C as step 1 requires. All remaining proof
  dependencies are among the publicly imported statement dependencies.

Edge cases checked: A may be a field (m_A = 0, B = Omega, q = 0, T = Omega, H is A up to
its specified henselization embedding); the conclusion becomes C = Omega and the full
K-automorphism subgroup. Trivial extensions Omega/K and H/A are retained. Purely
inseparable extensions are retained; no nontrivial automorphism or separability is assumed.
There is no dimension, residue-perfectness, finite-generation or characteristic hypothesis.
The zero ring is excluded exactly by the given domain hypotheses. Universes u, v, w, z
are independent; no equality between the source, extension, fraction-field, and
henselization universes was introduced.

Searches actually run:

- `msearch.py leanfinder`: "The integral closure of a henselization equals a henselian
  localization of the normalization and its prime stabilizer fixes the fraction field".
  Eight hits: `Algebra.intNorm_eq_of_isLocalization`,
  `IsLocalization.Away.integralClosure`, `IsLocalization.integralClosure`,
  `integralClosure_le_completeIntegralClosure`, `IsIntegralClosure.isLocalization`,
  `completeIntegralClosure_eq_integralClosure`,
  `instIsIntegralAtPrimeLocalizationAlgebraMapSubmonoidPrimeCompl`, and
  `IsIntegralClosure.isLocalization_of_isSeparable`. None identifies a henselization,
  the local integral closure and its decomposition subgroup as this node does.
- `msearch.py loogle`: "integralClosure, HenselianLocalRing": zero hits.
- `msearch.py grep`:
  "integralClosure.*[Hh]enselian|[Hh]enselian.*integralClosure|integralClosureInclusion":
  zero Mathlib hits.
- `msearch.py leansearch`: "The normalization of a henselization is the henselian
  localization of the normalization and the decomposition group fixes its fraction field".
  Eight hits about normal closures, scheme normalization, the henselian maximal-ideal
  pair, the henselian local parent, valuation-subring inertia, and fields being henselian;
  none states this comparison.
- `rg`/`grep` over both `lean/WeilConjectures` and `lean/Sheaf` for henselization,
  normalization, integralClosure H, stabilizer, Frac(H), 0BSW, and the exact node id.
  Read `HenselianGlobalInertiaComparison`, `StrictlyHenselianNormal`,
  `InertiaStrictHenselization`, `StrictHenselianFractionInertia`,
  `SeparableNormalizationLocalEmbeddings`, and `IntegralComponentHenselianPermanence`.
  The global comparison is more specialized; the others provide components or different
  conclusions. No exact match. Exact declaration-name search in both source directories,
  Mathlib, and `dag/lean_names_upstream.json` had no match before this delivery.

Validation: `scompile.py Q77 lem-dl-a1-henselian-normalization-localization` compiled the
actual sandbox file both as a sandbox module and as
`Sheaf.RingTheory.HenselianNormalizationLocalization`, cleanly (about 6 seconds each).
No errors or warnings remain. The theorem alone contains `sorry`.

## Second reading by Q77

This is the dispatcher's single-worker task; the brief forbids starting another agent.
This section records a fresh self-check with the node and final module open; it does not
claim an independent worker review. The maintainer performs the independent delivery review.

Checked every binder and clause against the unchanged node and the local Stacks sources.
The early draft incorrectly left H unbound, used a second CommRing instance on the already
constructed localization, omitted the explicit domain hypothesis on H, and placed the
maximal ideal after a non-dependent henselian conjunct. The final file binds H explicitly
in its independent universe, retains the canonical ring structure of the localization,
includes `_hHdomain`, and uses a dependent existential for C's henselian structure.
An unnecessary helper B -> C was removed: contraction is now expressed directly in Omega.
The canonical ideal action is enabled by Mathlib's `Pointwise` scope. The injectivity,
locality, above-m condition, algebraicity, and compatibility conditions all remain exactly
as stated; C = T is literal equality of images in the same field, and the final clause
is an equality of the two actual subgroups of G. No source clause is dropped and no extra
separability or field-size hypothesis appears. The six proof steps are in the docstring,
and the matching integral-component theorem is a private proof import. One overlong line
was wrapped. The final compile is clean. No statement dispute or node fault remains.
