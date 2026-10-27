## Worker report

Delivered module: `Sheaf.FieldTheory.OpenNormalInertiaFixedField`.
Declaration: `Ideal.fixedField_finite_galois_of_isOpen_normal_inertia_le`.
This is a statement only, with one `sorry` and the complete three-step natural-language
proof in its docstring. No definition is introduced and no theorem is proved.
The item's statement, dependencies and accepted split are unchanged; only `lean` is set.

The source was read in `literature/stacks-project/pione.tex`,
`lemma-normal-pione-quotient-inertia` (0BTD), especially the second proof paragraph,
and `literature/stacks-project/more-algebra.tex`,
`lemma-one-orbit-geometric-galois-compare` (0BSX), including its proof.
The current blueprint `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`
`sk-lem-wft-curve-heart/rem-dl-a1-conventions.md` supplies the ambient inertia convention.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The integrally closed domain is `A : Type u`, `[CommRing A]`, `[IsDomain A]`,
  `[IsIntegrallyClosed A]`. This is the normal-domain specialization of the
  recorded normal-ring definition, not a Noetherian normality assumption.
- Its fraction field is `K : Type v`, `[Field K]`, `[Algebra A K]`,
  `[IsFractionRing A K]`.
- The chosen separable closure is `Ω : Type w`, `[Field Ω]`, `[Algebra K Ω]`,
  `[IsSepClosure K Ω]`. The compatible `[Algebra A Ω]` and
  `[IsScalarTower A K Ω]` express the displayed inclusions through K.
  The three universes are independent and all variables are explicitly bound;
  `set_option autoImplicit false` enforces this.
- `G = Aut_K(Ω)` is `Ω ≃ₐ[K] Ω`; its topology is the Mathlib Krull topology
  imported through `Mathlib.FieldTheory.Galois.Infinite`. No arbitrary topology
  or extra continuity hypothesis is supplied.
- `C` is exactly `integralClosure A Ω` and the subgroup is
  `U : Subgroup (Ω ≃ₐ[K] Ω)`.
- Openness is `hUopen : IsOpen (U : Set (Ω ≃ₐ[K] Ω))` and normality is
  `hUnormal : U.Normal`.
- The hypothesis at every prime is `hUinertia : ∀ r : Ideal (integralClosure A Ω),
  r.IsPrime → r.inertia (Ω ≃ₐ[K] Ω) ≤ U`.
- `L` is the actual `IntermediateField.fixedField U`, not a chosen field or an
  arbitrary isomorphic object. `IntermediateField.mem_fixedField_iff` says
  exactly that every u in U fixes its elements.
- Finite Galoisness is the conjunction
  `FiniteDimensional K (IntermediateField.fixedField U)` and
  `IsGalois K (IntermediateField.fixedField U)`. Mathlib's `IsGalois` is separable
  and normal; its separability is algebraic. Neither is an extra hypothesis.
- `U = (IntermediateField.fixedField U).fixingSubgroup` says U consists exactly
  of the automorphisms fixing L pointwise. This subgroup is the image of
  `Aut_L(Ω)` inside `Aut_K(Ω)`; the existing
  `IntermediateField.fixingSubgroupEquiv` identifies the two groups. A literal
  equality between their differently typed groups would be inappropriate.
- `B` is exactly `integralClosure A (IntermediateField.fixedField U)`.
  For every ideal q of B with `q.IsPrime`, the existential supplies an ideal r
  of C with `r.IsPrime` and `r.comap f = q`.
  Here `f` is the canonical integral-closure inclusion
  `((IntermediateField.fixedField U).val.restrictScalars A).mapIntegralClosure.toRingHom`.
  The existing `.val` includes L in Ω; `.restrictScalars A` views that same map
  over A; `.mapIntegralClosure` restricts its domain and codomain to B and C.
  No arbitrary map, choice, additional integrality assumption or scalar-tower
  hypothesis about L was introduced.
- At the same arbitrary prime q the last clause is
  `q.inertia ((IntermediateField.fixedField U) ≃ₐ[K]
  (IntermediateField.fixedField U)) = ⊥`, precisely trivial finite-level inertia.
- No Noetherianity, finite generation or finiteness of an integral closure is assumed.

Inertia equivalence: `Ideal.inertia` (Mathlib/RingTheory/Ideal/Defs.lean) is the
subgroup satisfying `∀ b, g • b - b ∈ r`. By `Ideal.inertia_le_stabilizer`
(Mathlib/RingTheory/Ideal/Pointwise.lean), these elements stabilize r. The displayed
condition is identity on C/r. Since r is prime, C/r embeds in its fraction field;
identity on C/r extends to identity on all its fractions. Conversely identity on
the fraction field implies identity on C/r by injectivity. Thus this is exactly the
node's stabilizer acting trivially on Frac(C/r), at arbitrary primes, not only
maximal ideals. The identical explanation applies to B/q. This is also the exact
interface used by the recorded inertia-restriction theorem.

Recorded statement dependencies used:

- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` and `IsDomain` (normal-domain clause).
- `def-pd-separable-closure`: `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosure.exists_intermediateField_mem`; its full signature and docstring
  identify `IsSepClosure K Ω` as the separable-closure notion. The statement uses
  that existing class, while the union-of-finite-subextensions theorem is not
  an additional hypothesis needed here. Its module is publicly imported.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`;
  its carrier is `IsIntegral A b`.

Proof-dependency interfaces read and imported:

- `lem-weil-pbc-separable-closure-exists-galois`: Mathlib's `IsSepClosure.isGalois`
  through the separable-closure dependency module.
- `lem-exc-etale-open-subgroup-fixed-field-galois`:
  `InfiniteGalois.isOpen_iff_finite`, `InfiniteGalois.fixingSubgroup_fixedField`
  in `Mathlib.FieldTheory.Galois.Infinite`, and
  `IntermediateField.isSeparable_tower_bot` from its separability imports.
  The plain proof import `WeilConjectures.Mathlib.FieldTheory.KrullTopology`
  also gives `InfiniteGalois.fixingSubgroup_fixedField_of_isOpen` and
  `InfiniteGalois.finiteDimensional_fixedField_of_isOpen`.
- `lem-dl-a1-normal-fixing-subgroup-galois`:
  `InfiniteGalois.normal_iff_isGalois`, `Mathlib.FieldTheory.Galois.Infinite`.
- `lem-weil-pbc-integral-injective-lying-over`:
  `RingHom.IsIntegral.comap_surjective`,
  `Mathlib.RingTheory.Spectrum.Prime.Topology` (plain proof import).
- `lem-dl-a1-inertia-restriction-surjective`:
  `Ideal.inertia_map_restrictNormalHom`,
  `Sheaf.FieldTheory.InertiaRestrictionSurjective` (plain proof import).
  Its full tower signature and quotient-action explanation were read.

Edge cases checked mathematically before finalizing the statement:

- U = top: L is K, the finite extension has degree one, the lower automorphism
  group and its inertia are trivial; lying over is still an arbitrary-prime assertion.
- U = bottom, when open and satisfying the inertia hypothesis: the ambient
  separable closure is finite over K, and the assumption already kills upper inertia.
- Ω = K for separably closed K: no nontrivial extension or subgroup is required.
- The zero prime is allowed. For a domain the fraction field of the zero-prime
  quotient is the ambient field, so its inertia is trivial as required.
- Nonmaximal primes are included: the formulation uses `IsPrime`, not `IsMaximal`.
- Non-Noetherian normal domains and nonfinite integral closures are not excluded.
- Imperfect fields and positive characteristic are included: only separable
  closure is assumed, not algebraic closedness or characteristic zero.

Searches for an exact existing declaration:

1. `msearch.py ... leanfinder "The fixed field of an open normal absolute Galois
   subgroup containing inertia at every integral closure prime is finite Galois
   and has trivial inertia at every prime"`: 8 hits. The field-only result
   `InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois` supplies only the
   finite-Galois part. Other hits concern inertia degrees or invariant rings;
   none states the full arbitrary-prime assertion.
2. `msearch.py ... loogle "IntermediateField.fixedField, Subgroup.Normal"`:
   5 hits on `IsGalois.of_fixedField_normal_subgroup` and finite/infinite
   `normalAutEquivQuotient` (and their apply lemmas). No complete match.
3. `msearch.py ... grep "inertia.*(restrict|[Ss]urject)|fixedField.*[Ii]nertia"`:
   one hit in Mathlib/RingTheory/Polynomial/Morse.lean, unrelated to the assertion.
4. `msearch.py ... leansearch "An open normal subgroup of an absolute Galois
   group containing all integral closure inertia groups has a finite Galois
   fixed field with trivial inertia at every prime"`: 8 hits including the
   field-only open/normal criterion, `IsGaloisGroup.subgroup`, and Krull-basis
   results; no complete match.
5. `rg -n 'fixedField.*inertia|inertia.*fixedField|open_normal.*inertia|inertia.*open_normal'
   lean/WeilConjectures lean/Sheaf`: fixed fields of individual inertia groups in
   the strict-henselization and boundary-neighbourhood modules, not this theorem.
6. `grep -rn 'lem-dl-a1-open-normal-inertia-fixed-field' lean/WeilConjectures`:
   no hit. Exact proposed-name searches in Mathlib, WeilConjectures and Sheaf:
   no hit. The live project has the different theorem on surjective inertia
   restriction, which is reused as a proof dependency.

Validation: the final module was compiled through the prescribed `scompile.py`
against the live published library, in module mode, as both the sandbox module
and its intended library module. Both compiled cleanly with no diagnostics.
No statement dispute, missing notion, unusable dependency or source correction was found.

## Second reading by Q97

A second clause-by-clause pass in this worker session compared the node JSON,
source and finished module. This is a self-review; the dispatcher brief forbids
starting other agents and assigns independent review to the maintainer.
The pass checked the separable-closure binder, Krull openness, normality and
all-prime inertia containment, then each of the four conclusion components.
In particular, it checked that the comap uses the canonical inclusion of actual
integral closures and that the inertia groups use the full K-automorphism groups,
not just a selected stabilizer or a maximal-prime specialization. It checked the
quotient/fraction-field equivalence above and the fixing-subgroup representation
of Aut_L(Ω). No mathematical mismatch remained. Initial development probes were
replaced by the final direct fixed-field signature; all style warnings were fixed.
The accepted node statement and split did not change.
