## Worker report

The single module `Sheaf.RingTheory.IndEtaleTotalFractionComparison` states
`Algebra.indEtale_totalFraction_comparison`, with one `sorry` proof and no new definitions.
It gives the nonzerodivisor preservation and the canonical B-algebra isomorphism
Q(A) ⊗[A] B ≃ Q(B), with the exact fraction formula. The node is unchanged except for `lean`.

Hypothesis and clause matching:

- Commutative rings A and B: `(A : Type u) (B : Type v) [CommRing A] [CommRing B]`.
  Independent universes are allowed.
- The map f: A → B is encoded by `[Algebra A B]`, with `f = algebraMap A B`.
  Every unital ring map gives precisely such an algebra structure via `f.toAlgebra`.
- Noetherianity of both rings: `[IsNoetherianRing A] [IsNoetherianRing B]`.
- Reducedness of both rings: `[IsReduced A] [IsReduced B]`, meaning that every
  nilpotent is zero. Both target-ring hypotheses are retained, even though the
  mathematical argument does not need them.
- Ind-étaleness: `hind : RingHom.IndEtaleAcrossUniverses (algebraMap A B)`, the
  dependency's recorded definition using canonical ULift to a common universe.
- T_R is `nonZeroDivisors R`. For commutative rings, Mathlib's
  `mem_nonZeroDivisors_iff_left` is exactly ∀ r, s*r = 0 → r = 0.
- Q(R) is `FractionRing R = Localization (nonZeroDivisors R)`. The recorded
  module-localization type `LocalizedModule (nonZeroDivisors R) R` is definitionally
  the same localization (Mathlib's `example_localization_eq_localizedModule`).
  This notation does not impose a domain or nontriviality assumption.
- The first conclusion is `∃ hregular : nonZeroDivisors A ≤
  (nonZeroDivisors B).comap (algebraMap A B), ...`, exactly f(T_A) ⊆ T_B.
- The isomorphism is an `AlgEquiv` over B with source `FractionRing A ⊗[A] B`
  and target `FractionRing B`. Its source algebra instance is explicitly
  `Algebra.TensorProduct.rightAlgebra`, whose structure map is b ↦ 1 ⊗ b;
  its target instance is the localization B-algebra structure. There are no
  additional algebra instances or compatibility assumptions supplied by the caller.
- The displayed canonical map is specified on every a, regular s, and b by
  `e (IsLocalization.mk' (FractionRing A) a s ⊗ₜ[A] b) =
  IsLocalization.mk' (FractionRing B) (algebraMap A B a * b)
  (⟨algebraMap A B s, hregular s.property⟩ : nonZeroDivisors B)`.
  This is exactly (a/s) ⊗ b ↦ f(a)b/f(s). Every localization element is a
  fraction and pure tensors generate the tensor product additively, so the
  formula uniquely determines the canonical map. The existential isomorphism
  therefore asserts invertibility of that specified map, not of an arbitrary map.
- Tensor multiplication is Mathlib's ring tensor multiplication, whose
  `Algebra.TensorProduct.tmul_mul_tmul` gives exactly
  (x ⊗ b)(x' ⊗ b') = xx' ⊗ bb'. This is the construction used, not an extra
  theorem conjunct duplicating an existing identity.
- Zero rings and maps to zero rings: no `Nontrivial`, `IsDomain`, faithfulness,
  injectivity, or field assumptions occur in the signature.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; also read `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`. Read its ULift definition and the underlying
  `Algebra.IndEtale` filtered-colimit definition in
  `WeilConjectures.RingTheory.ProEtale.IndEtale`.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`, `LocalizedModule.mk`, and the definitional identification of
  ring and module localization. Fraction notation and its ring structure are
  from `Mathlib.RingTheory.Localization.FractionRing`, `FractionRing`, and
  `Mathlib.RingTheory.Localization.Defs`, `IsLocalization.mk'`.
- `def-weil-pbc-module-tensor-product`: the Mathlib match `TensorProduct` and its
  bilinear map `TensorProduct.mk` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  publicly imported by `Mathlib.RingTheory.TensorProduct.Basic`. Read the quotient
  definition, multiplication, `tmul_mul_tmul`, and `rightAlgebra`.

All stated proof-dependency modules are imported privately unless already public for
statement use: `Sheaf.RingTheory.IndEtaleStability`,
`Mathlib.RingTheory.RingHom.Flat`, `Mathlib.RingTheory.Localization.BaseChange`,
`WeilConjectures.RingTheory.TotalFractionFiberDecomposition`,
`Sheaf.RingTheory.WeaklyEtaleField`, and `Mathlib.RingTheory.Etale.Field`.
The declaration docstring carries all five proof steps, their DAG citations, and the
zero-ring cases. There are no missing proof imports or import-cycle omissions.

Sources read: `literature/stacks-project/spaces-divisors.tex`,
`lemma-meromorphic-quasi-coherent` (Tag 0EN6), especially its displayed map and
flatness explanation. The source states the étale case; the node expressly records
its ind-étale extension, and the docstring does likewise. Also read the latest
blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof in
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`.
This item is a supporting algebra lemma, not the blueprint unit's own statement.

Edge cases checked mathematically:

- B = 0: both Q(B) and Q(A) ⊗ B are zero; regular denominators map to the unique
  element of the zero ring, which is a nonzerodivisor and a unit there.
- A = 0: a unital algebra forces B = 0, so the same case applies.
- A = k × k → B = k by projection: a component can be killed; injectivity must
  not be assumed. Both fraction rings and the tensor comparison have the stated form.
- A reduced reducible Noetherian ring: regular elements avoid every minimal prime;
  the proof works with a finite product of generic fibres rather than a fraction field.
- An ind-étale algebraic field extension (including an infinite one): Q(A) = A and
  Q(B) = B, and the comparison is the ordinary tensor unit isomorphism. No finite
  presentation of B over A was inadvertently added.
- The empty generic-point product for the zero base ring is permitted by the
  recorded total-fraction decomposition; no fixed positive number of factors is used.

Searches actually run (all through the prescribed msearch wrapper where applicable):

- LeanFinder: `For reduced Noetherian rings an ind etale map commutes with the total
  ring of fractions by tensor base change`. Eight hits, including
  `Algebra.Etale.baseChange`, `RingHom.Etale.isStableUnderBaseChange`, and
  `Algebra.FormallyEtale.localization_map`; none is this total-fraction comparison.
- Loogle: `"IsLocalization", "nonZeroDivisors", "TensorProduct"`. Zero hits.
- Mathlib grep: `(nonZeroDivisors|[Tt]otal[Ff]raction).*(tale|colimit)|(tale|colimit).*(nonZeroDivisors|[Tt]otal[Ff]raction)`.
  Zero hits.
- LeanSearch: `Total quotient ring tensor comparison for Noetherian ind etale
  algebras over reduced rings`. Eight hits on tensor products of module quotients;
  none concerns ind-étale total fractions.
- `rg` of the read-only `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-per-ind-etale-total-fraction-comparison|indEtale.*[Tt]otal|[Tt]otal.*indEtale`:
  only unrelated condensed totally-separated results. The item is not already stated.
- Broader `rg` for total-fraction and ind-étale names found and read
  `Sheaf.RingTheory.FlatIntegralTotalFractions` (integral intermediate subalgebras,
  different hypotheses and conclusion) and `Sheaf.RingTheory.IndEtaleDomainGenericField`
  (injective maps of domains, different hypotheses). Neither is an exact match.
- The proposed declaration name `indEtale_totalFraction_comparison` has no match in
  `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`, or `lean/Sheaf`.

No node faults or statement disputes found. No new nodes or dependency repairs needed.

Validation: `scompile.py N5 lem-per-ind-etale-total-fraction-comparison` compiled
both the sandbox module and its library-path version, each in under two seconds,
with no errors or warnings. The initial denominator inference error was repaired
by explicitly annotating the target denominator as `nonZeroDivisors B`.

## Second reading by N5

Author's separate self-check, as required by the direct-delivery brief; the maintainer
performs the independent review. Reopened the node and the final Lean signature.
Both commutative, reduced, Noetherian ring hypotheses appear, f is precisely the
chosen algebra structure map, and the recorded across-universes ind-étale predicate
is used without a new definition. The first dependent existential proves regular
image preservation rather than assuming it. The second existential is a B-algebra
isomorphism for the right-factor scalar action, and its formula on every a, s, b
matches numerator f(a)b and denominator f(s) exactly. Localizations and tensor
multiplication are Mathlib's constructions already named by the dependency nodes.
The formula on all fraction tensors determines the map uniquely, so no unspecified
comparison or arbitrary isomorphism remains. No nontriviality or injectivity
hypothesis excludes zero rings or projections killing components. No statement
mismatch was found; the only change during checking was the explicit denominator
type annotation needed for elaboration. All variables and universes are bound,
all proof dependencies with statements are imported, and the sole proof is `sorry`.
