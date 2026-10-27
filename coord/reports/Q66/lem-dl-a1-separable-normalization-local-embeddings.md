## Worker report

The module `Sheaf.RingTheory.SeparableNormalizationLocalEmbeddings` states
`Algebra.separableNormalization_local_embeddings`, with its sole proof `sorry`.
There are no new definitions and no proof claims. The seven-step accepted split,
source, and natural-language statement are unchanged.

The inherited BLOCKED ending concerned a stage-1 empty delivery. The current
`coord/brief-stage2.md` §0 explicitly distinguishes that situation from stage 2.
The live node has no `lean` or `reviewed_lean` and `coord/queue.tsv` lists stage 2.
Its stage-1 review of 2026-10-24 is the input to this work, not a prohibition on
recording its Lean statement. There is no released repair note for the item.

Hypotheses and objects, matched individually:

- The normal local domain A is `[CommRing A] [IsLocalRing A] [IsDomain A]
  [IsIntegrallyClosed A]`. No Noetherian, dimension, excellence or characteristic
  hypothesis is imposed.
- K is its fraction field: `[Field K] [Algebra A K] [IsFractionRing A K]`.
- Omega is the chosen separable closure: `[Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω]`. The A-algebra and `IsScalarTower A K Ω` identify the
  A-map used for integrality with this fraction-field embedding.
- B is exactly `integralClosure A Ω`, whose carrier is `{x | IsIntegral A x}`,
  not an arbitrary normal subring or an assumed normalization.
- The chosen maximal ideal is `q : Ideal (integralClosure A Ω)` with
  `[q.IsMaximal]`; `hq` is precisely contraction to `maximalIdeal A`.
- T is exactly `Localization.AtPrime q`; E is its `IsLocalRing.ResidueField`.
  The comparison with B/q is a conclusion, not an assumption.
- H has the recorded `IsHenselizationAtPrime' A (maximalIdeal A) H` predicate.
  Its HenselianLocalRing and algebra over A_m are the structures required by
  that definition. Its A-algebra and scalar tower merely express the same
  structural map A -> A_m -> H. Since A is local, A_m is canonically A.
- The chosen residue separable closure is `ks`, with the recorded
  `IsSepClosure (ResidueField A) ks`. The A-algebra scalar tower states that its
  A-map factors through the quotient to the residue field.
- R, with its A-algebra, is specified by
  `P : StrictHenselizationPresentationIn.{u,u} A ks R`, the existing universal
  pointed-etale-algebra cocone and identification, including its actual
  `P.residueMap`. No local, normal or ind-etale property of R is assumed.
  This is the existing ring formulation of the strict henselization; the
  source scheme construction is also publicly imported. All rings lie in a
  common arbitrary universe u, as in the ring definition, with no finite or
  countability restriction and no independently smaller test universe.

Conclusions, matched individually:

- B is a normal domain: `IsDomain B ∧ IsIntegrallyClosed B`.
- Frac(B) = Omega: `IsFractionRing B Ω` for its subalgebra inclusion.
- T is a normal domain: `IsDomain T ∧ IsIntegrallyClosed T`.
- Frac(T) = Omega: an `Algebra T Ω` with `IsScalarTower B T Ω` and
  `IsFractionRing T Ω`. The tower forces the map to extend the actual B
  inclusion. Thus its localization embedding is the specified one; it is
  not an unconstrained choice of map to Omega.
- T is strictly henselian: `IsStrictlyHenselianLocalRing T`.
- A -> T is local: `IsLocalHom (algebraMap A T)`, stated explicitly so the
  later residue extension is the structural one.
- E = B/q: `e : (B ⧸ q) ≃+* ResidueField T`, with the equation
  `e ∘ Quotient.mk q = residue T ∘ algebraMap B T`. This also specifies the
  canonical quotient-localization identification.
- H is a normal domain: `IsDomain H ∧ IsIntegrallyClosed H`.
- A -> H is local, injective and ind-etale: the three predicates
  `IsLocalHom`, `Function.Injective`, `RingHom.IndEtaleAcrossUniverses` on
  the actual `algebraMap A H`.
- H has unchanged residue field: `eH : ResidueField H ≃+* ResidueField A`,
  with `eH ∘ residue H ∘ algebraMap A H = residue A`.
- The compatible H-structure of R is concluded existentially, together with
  `IsLocalRing R` and `IsScalarTower A H R`. Thus the given A-map is retained.
  Its local H-map is canonical by the ordinary henselization universal property.
- R is a normal domain: `IsDomain R ∧ IsIntegrallyClosed R`.
- H -> R is local, injective and ind-etale: the same three predicates on
  `algebraMap H R`. Together with the A -> H clauses these state exactly the
  two maps in A -> H -> R; their composite has the corresponding properties.
- The specified residue of R is ks: `eR : ResidueField R ≃+* ks`, with
  `eR ∘ residue R = P.residueMap`. This retains the chosen residue pointing.
- E/kappa is algebraic: an `Algebra (ResidueField A) E`, with
  `IsScalarTower A (ResidueField A) E` and `Algebra.IsAlgebraic`.
  The A-action on E already comes from A -> B -> T -> E, so the tower forces
  precisely the structural residue inclusion (the quotient A -> kappa is
  surjective). No stronger algebraically-closed assertion about E is made.
- Existence of j: `Nonempty (ks →ₐ[ResidueField A] E)`. A unital homomorphism
  between fields is injective, so this is the required kappa-embedding.
- The local A-map h: `h : H →ₐ[A] T`, `IsLocalHom h.toRingHom`, and
  `Function.Injective h`. The clause `∀ h', IsLocalHom h'.toRingHom -> h' = h`
  gives uniqueness among ALL local A-maps, not just injective ones.
- For EVERY residue choice `j : ks →ₐ[ResidueField A] E`, there is an
  `i : R →ₐ[A] T` which is local and injective, with
  `i ∘ algebraMap H R = h` and `residue T ∘ i = j ∘ P.residueMap`.
  The first equation says exactly that i is an H-map with the h-induced
  H-structure on T. The second is the requested induced residue map.
- Final uniqueness quantifies over every local A-map i' with that residue
  equation and concludes i' = i. It therefore includes every compatible local
  embedding mentioned in the final sentence, without requiring injectivity or
  H-linearity as extra uniqueness hypotheses. The compatible injective maps
  and the canonical T -> Omega localization give A <= H <= R <= T <= Omega.

Dependency declarations read and used:

- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  `IsDomain`, together with `integralClosure` and `Localization.AtPrime`.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` and its Mathlib notion
  `IsSepClosure` (separably closed and separable algebraic).
- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'`, the full local-map universal property.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, its affine pointed-neighbourhood diagram
  and `strictHenselization_properties`, read with full signatures/docstrings.
  Its geometric-point parameter is algebraically closed; the ring specialization
  is expressed using the already landed ring-definition node below.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` and `.residueMap`. This is the
  current recorded interface of `def-sc-ring-strict-henselization`, added to
  the item's stmt_deps under the permission to gain an already landed node.
  Its cocone has real data, IsColimit and a specified algebra identification.
  No dependency is redefined or repaired in this packet.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `HenselianLocalRing` and `IsStrictlyHenselianLocalRing`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, the canonical ULift transport of the
  existing filtered-colimit ind-etale predicate.
- The existing stated proof-dependency modules are plain imports:
  `GabberQuotientLocalizations`, `PrimePairColimitIndEtaleModel`,
  `InitialHenselianColimitComparison`, `EtaleColimitNormalLocalDomain`,
  `StrictHenselizationFiniteLifts`, `IndEtaleStability`, and
  `MapIntoHenselianColimit` (their exact roots are in the module's import list).
  The two integral-closure/localization proof leaves and the separable-embedding
  leaf are Mathlib declarations exposed by the public imports. The two proof
  nodes without recorded Lean declarations, finite-local-lift-colimit-structure
  and ind-etale-domain-generic-field, have no module to import yet; their roles
  remain in the proof docstring. They are not needed to type this statement.

Sources and edge cases checked:

Read local Stacks `pione.tex`, section-ramification (0BSD), including the
henselization diagram and residue-prescribed uniqueness, and
lemma-normal-local-domain-separablly-closed-fraction-field (0BSQ), including
its field-case exception. Read the latest blueprint rem-dl-a1-conventions,
whose inertia-at-infinity equivalence is the ancestor served by this node.

If A is a field, B = T = Omega and E = Omega; the statement only says E is
separably closed through strict henselianity, not algebraically closed. This
preserves the imperfect separably-closed-field case. If A is already strictly
henselian, the identity henselizations and the prescribed residue embedding
are covered. Non-Noetherian normal local domains are covered. The zero ring
is correctly excluded by the normal-domain hypothesis. The specified maximal
ideal is a real input; no extra existence assumption on a chosen prime or
residue map is substituted. There is no empty-index or degree-zero clause.

Searches for an existing exact declaration (2026-10-24):

- msearch leanfinder: "Local compatible embeddings of the henselization and
  strict henselization into a separable normalization localized at a maximal
  ideal". Eight hits: HenselianLocalRing, its maximal-ideal henselian instance
  and projection, Field.henselian, HenselianLocalRing.TFAE, arithmetic Frobenius
  localization results and a quotient-localization existence lemma. None states
  the comparison of the two henselizations or residue-prescribed unique maps.
- msearch loogle: "IsSepClosure, IsIntegralClosure.isLocalization_of_isSeparable,
  HenselianLocalRing". Zero hits.
- msearch grep: "henseli.*(integralClosure|[Ee]mbed)|[Ss]eparable[Nn]ormalization".
  Zero Mathlib hits.
- msearch leansearch: "Compatible local embeddings of a henselization and strict
  henselization into the integral closure in a separable closure localized at
  a maximal ideal". Eight hits on integrally-closed localizations, henselian
  rings, galLift and localization of integral closure. No exact statement.
- rg on both project Lean trees with the same expression: a finite henselian
  DVR extension, a strict-henselization comparison, and tensor-component join
  models, all with different hypotheses/conclusions. Opened the relevant module
  signatures/docstrings; none is this statement. Exact node-id grep in upstream
  WeilConjectures returned no matches.
- DAG search found the existing ring strict-henselization definition; it is used
  rather than introducing another definition or copying the scheme construction.

Validation: the prescribed scompile wrapper compiled the sandbox and library-path
versions separately and cleanly (14.3 s and 9.3 s). The only postponed proof is
`Algebra.separableNormalization_local_embeddings`. No statement dispute or
mathematical node fault was found. The required deliver2.py dry run passed preflight and compilation
(commit 97c8ce15f48, nothing pushed).

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
