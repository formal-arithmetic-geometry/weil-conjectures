## Worker report

The module `Sheaf.RingTheory.HenselianGlobalInertiaComparison` states
`Algebra.henselianGlobalInertiaComparison`. The only theorem proof is `sorry`.
Five auxiliary declarations specify the actual closed geometric point, its recorded
strict-henselization ring, its canonical structural and evaluation maps, and the
compatibility conditions on the embeddings in the source diagram. They belong to this
node, are listed in `lean.declarations`, and introduce no independent mathematical notion.
There are no new nodes, dependency repairs, or changes to the natural-language statement.

Source read: `literature/stacks-project/pione.tex`, Section 0BSD
(`section-ramification`), its setup starting at line 2826, and Lemma 0BSW
(`lemma-identify-inertia`, lines 2883–2972), including its proof. The statement follows
the node's sixteen-step direct argument, including the purely inseparable residue
comparison that handles imperfect residue fields without using the setup footnote's
claim that the normalization residue is always an algebraic closure.

Hypothesis and clause correspondence:

- Normal local domain `(A,m,κ)`: `[CommRing A] [IsLocalRing A] [IsDomain A]
  [IsIntegrallyClosed A]`; `m = maximalIdeal A`, `κ = ResidueField A`. This uses the
  domain clause of the recorded normal-ring interface, not a new normality predicate.
- `K = Frac(A)`: `[Field K] [Algebra A K] [IsFractionRing A K]`, allowing any specified
  field of fractions. No valuation, dimension, excellence or Noetherian assumption.
- Chosen separable closure `Ω/K`: `[Field Ω] [Algebra K Ω] [IsSepClosure K Ω]`.
  `[Algebra A Ω] [IsScalarTower A K Ω]` names the composite base embedding.
- Integral closure `B`: exactly Mathlib `integralClosure A Ω`; its elements are the
  integral elements of Ω, hence the roots of monic polynomials over A. No substitute
  normalization algebra is supplied as an extra hypothesis.
- Chosen maximal `q` above `m`: `(q : Ideal (integralClosure A Ω)) [q.IsMaximal]`
  and `hq : Ideal.comap (algebraMap A (integralClosure A Ω)) q = maximalIdeal A`.
- `G = Aut_K(Ω)`: `Ω ≃ₐ[K] Ω`. The action on B is the existing integral-closure
  action; the pointwise ideal action is Mathlib's scoped `Pointwise` instance.
- `D = {g | gq=q}`: `MulAction.stabilizer (Ω ≃ₐ[K] Ω) q`, with its subtype topology.
- `I = {g in D | g acts trivially on κ(q)}`: `q.inertia (Ω ≃ₐ[K] Ω)`.
  Mathlib defines inertia by `∀ b : B, g • b - b ∈ q`, equivalently identity on B/q,
  and, since q is maximal, on its residue field. Its inclusion in D is the recorded
  `Ideal.inertia_le_stabilizer`, not another hypothesis.
- Ordinary henselization `H = A^h`: `[HenselianLocalRing H]`, its localized A-algebra,
  the compatible A-algebra/tower, and
  `hH : Algebra.IsHenselizationAtPrime' A (maximalIdeal A) H`.
- Chosen separable residue closure: `[Field κs] [Algebra (ResidueField A) κs]
  [IsSepClosure (ResidueField A) κs]`.
- Strict henselization `R = A^sh`: `henselianInertiaStrictRing A κs` is an abbreviation
  for the recorded `Scheme.strictHenselizationRing (henselianInertiaPoint A κs)`.
  Its geometric point is the composite A → κ → κs → AlgebraicClosure κs. Enlarging
  the separably closed point to this algebraic closure preserves the pointed étale
  neighbourhood construction and permits the recorded API's `IsAlgClosed` binder;
  κs itself is not required to be algebraically closed or perfect.
- The base map A → R is the canonical map of the base pointed chart, transported
  through `Scheme.smallStrictHenselizationColimitIso`. Evaluation is the canonical
  colimit evaluation transported by the same isomorphism in the opposite direction.
- Both henselizations are domains: existential conclusion witnesses `IsDomain H`
  and `IsDomain R`. Locality of R is also a conclusion, available for its residue
  expressions; it is not assumed on the input.
- Their residue fields are the specified κ and κs: the conclusion supplies `eH`
  with its base-residue formula, and a surjective `r : R →+* κs` with kernel
  `maximalIdeal R`. The equality
  `(algebraMap κs (AlgebraicClosure κs)).comp r = henselianInertiaStrictEval A κs`
  identifies this residue map with the chosen point's actual evaluation.
- Residue choice in `κ(q)`: the statement first asserts that a compatible
  `j : κs →+* ResidueField (Localization.AtPrime q)` exists, then quantifies over
  every such j. Its compatibility is written on every a in A. No extra embedding
  existence hypothesis is imposed. Field ring homomorphisms are injective.
- The compatible embeddings `A ⊆ H ⊆ R ⊆ B_q ⊆ Ω` are existence conclusions
  for `h : H →+* B_q`, `c : H →+* R`, `i : R →+* B_q`.
  `CompatibleHenselianInertiaEmbeddings` expands to the two base-map equations,
  `i.comp c = h`, locality and injectivity of all three maps, and
  `(residue B_q).comp i = j.comp r`.
  The final embedding B_q → Ω is the already defined `Ideal.atPrimeToField q`,
  whose injectivity is `Ideal.injective_atPrimeToField`.
- `K^h` and `K^sh` are `FractionRing H` and `FractionRing R`. The conclusion
  supplies their Ω-algebra structures, each specified on every ring element by
  its composite through B_q. These are fraction extensions of the actual embeddings,
  not unrelated choices of field embeddings.
- `D = Aut_(K^h)(Ω)` and `I = Aut_(K^sh)(Ω)` are given by `eD` and `eI` of type
  `≃ₜ*`, with the formulas `eD σ x = σ.val x` and `eI σ x = σ.val x` for every
  x in Ω. These formulas require both maps to be the identifications on the same
  field automorphisms, rather than arbitrary abstract group isomorphisms.
- Ω is a separable closure of `K^h`: explicit conclusion `IsSepClosure (FractionRing H) Ω`.
- Continuous surjective residue map: `res : D →* (κs ≃ₐ[ResidueField A] κs)` with
  `Continuous res ∧ Function.Surjective res`. Its defining element formula is
  `j (res σ (r x)) = residue B_q (Ideal.atPrimeMap q σ.val σ.property (i x))`
  for every σ in D and x in R. Surjectivity of r and injectivity of j uniquely
  specify res as restriction of the canonical localization residue action.
- Kernel exactly I as a subgroup of G: `res.ker.map D.subtype = q.inertia G`.
- The local henselian inertia kernel maps to precisely I: the last conjunct maps
  `(res.comp eD.symm.toMonoidHom).ker` along `D.subtype.comp eD.symm.toMonoidHom`
  and equates its image with `q.inertia G`. Thus local inertia is defined by the
  residue action on the absolute Galois group, not substituted by global inertia.
- All group identifications use the Krull topologies: `≃ₜ*` for eD and eI,
  `Continuous res`, and the existing Mathlib Krull topology instances on each
  algebra-automorphism group. D and I have their induced subgroup topologies.
- Any compatible embedding: after asserting existence, the theorem quantifies
  universally over h, c and i satisfying the exact same compatibility predicate,
  for every compatible j. The fraction-field algebra structures are determined by
  their displayed formulas, so this includes every compatible fraction embedding.

Dependency declarations read and used:

1. `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
   `IsIntegrallyClosed`, together with `IsDomain`, and `Localization.AtPrime`.
   Read the `IsIntegrallyClosed` documentation/signature and its chosen-fraction
   characterization, and the localization and inertia definitions in Mathlib.
2. `def-pd-separable-closure`: `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`,
   `IsSepClosure.exists_intermediateField_mem`, with the full docstring/signature;
   its documented underlying notion is Mathlib `IsSepClosure`. The class is used
   both for Ω/K and κs/κ.
3. `def-weil-pbc-henselization-at-prime`:
   `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`,
   `Algebra.IsHenselizationAtPrime'`, read in full along with its imported original
   universal-property definition. The theorem uses the current recorded interface.
4. `def-weil-pbc-strict-henselization-limit`:
   `WeilConjectures.AlgebraicGeometry.StrictHenselization`,
   `Scheme.strictHenselizationRing`, read with its small representative diagram,
   docstring and full signature. The canonical comparison is from
   `WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension`,
   `Scheme.smallStrictHenselizationColimitIso`. The base chart map and evaluation
   come from `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`,
   `Scheme.SpecPointedEtaleNeighborhood.ι` and `Scheme.strictHenselizationEval`.

The module also imports the modules of the recorded proof dependencies, including
`StrictHenselizationFiniteLifts`, `MapIntoHenselianColimit`, the integral-component
henselian permanence theorem, and the normal étale colimit theorem. Its proof docstring
records each of the node's sixteen steps and the facts used there. Every auxiliary
signature, universe and variable is explicitly bound; `autoImplicit` is false.

Edge cases checked before writing:

- A field A: q is zero in B = Ω, H is A up to its unique identification,
  R is the separable residue closure, D is all G and I is trivial. The formulas
  for eD, eI and res have exactly these specializations. No positive dimension
  or nonzero maximal ideal is required.
- Strictly henselian A: κ is separably closed, R and H agree with A up to the
  canonical identifications, the residue Galois group is trivial, and D = I.
- Henselian A with nontrivial separable residue extensions: H = A, D = G, and
  the residue quotient can be nontrivial, so no tautological trivial-action
  hypothesis was introduced.
- Imperfect κ in characteristic p: E can have a purely inseparable part over
  j(κs). The theorem never asserts E = κs or E algebraically closed. The chosen
  geometric point uses AlgebraicClosure κs only as a target of the pointings;
  the stated residue field of R remains κs. Characteristic zero and positive
  characteristic are both included without hypotheses on the characteristic.
- Normal non-Noetherian local domains are permitted; none of the inputs asks
  for finite generation, finite dimension, discreteness of a valuation or a DVR.
- All rings and fields are in an arbitrary common universe u, as required by
  the recorded scheme colimit. No separate smaller universe of test rings is
  introduced, and no equation of site object/morphism universes is imposed.

Searches actually run:

- `msearch.py ... leansearch`: "The decomposition group of a normal local domain
  is the Galois group over the fraction field of its henselization". Eight hits,
  including `IsGaloisGroup.to_isFractionRing`, `IsGaloisGroup.of_isFractionRing`,
  and `ValuationSubring.decompositionSubgroup`; no exact statement.
- `msearch.py ... leanfinder`: "For a normal local domain the decomposition and
  inertia subgroups identify with automorphisms fixing the fraction fields of its
  henselization and strict henselization". Eight hits, including valuation-subring
  inertia/decomposition definitions and integral restriction; no exact statement.
- `msearch.py ... loogle`: `Ideal.inertia, Ideal.decomposition`.
  Zero hits; Loogle reported unknown identifier `Ideal.decomposition`.
- `msearch.py ... grep`: `decomposition|inertia`, restricted to `RingTheory/Ramification`.
  Zero hits in that directory filter. A corrected search `inertia|stabilizer`
  in `RingTheory/Ideal` returned 22 hits, including `Ideal.inertia`,
  `Ideal.inertia_le_stabilizer`, `Ideal.Quotient.stabilizerHom` and its kernel lemma.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for henselian/inertia and
  decomposition/henselization: found the normalization localization maps in
  `StrictlyHenselianNormal`, the invariant construction in `InertiaStrictHenselization`,
  and the DVR-only `Sheaf.FieldTheory.StrictHenselianFractionInertia`. The latter
  takes A to be a DVR and its K to be Frac(H), so does not state this normal-domain
  comparison with both global D and I. The invariant constructions do not identify
  these groups with both given henselizations.
- Direct `rg` by the exact item id in `lean/WeilConjectures`: no match.
- Direct `rg` of `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`
  and `lean/Sheaf` for all introduced declaration names: no collisions.
- `python3 tools/blueprint_refs.py search 'decomposition inertia'`: zero blueprint
  nodes. No new definition node is needed: the canonical construction and subgroup
  notions already exist.

Validation: `scompile.py NH lem-dl-a1-henselian-global-inertia-comparison` compiled
both the renamed sandbox module and its actual library module cleanly. The initial
compile identified the need to activate the existing scoped ideal action; adding
`open scoped Pointwise` resolved it. No proofs were supplied, no warnings remained,
and every source line is at most 100 characters. The node copy differs from the
repository only in `lean`, with its signature copied verbatim from the module.

## Second reading by NH

A separate second pass by this dispatcher-started worker reopened the node, Section
0BSD/Lemma 0BSW and the completed file. No other agent was started; the maintainer's
independent delivery review remains separate from this worker pass.

The rereading checked the normal-domain and local hypotheses, the fraction-ring
and separable-closure choices, maximality and contraction of q, the two recorded
henselization interfaces, the residue identifications, and each arrow in the source
chain. The strict base map uses the inverse of the small-colimit comparison and
evaluation uses its forward map, so both maps refer to the same strict henselization.
The base point has kernel m, and evaluation is required to factor through exactly
κs, rather than imposing an algebraically closed residue hypothesis.

For the conclusions, existence of compatible local injections precedes universal
quantification over the same compatible injections; no source embedding is merely
assumed to exist. The two fraction embeddings extend those actual ring maps.
The eD/eI formulas quantify over every element of Ω, so they identify actual
subgroups of the global group. The residue formula determines res on all of κs
because r is onto; its kernel is compared with I after the canonical inclusion
in G. The final kernel uses the local group's transported residue action. The
continuous equivalences and `Continuous res` include the Krull topology clauses.
All choices j and all compatible embeddings are included, not only an arbitrary
single selected example. No mismatch with the node was found in this second pass;
there is no statement correction or disputed-statement flag.
