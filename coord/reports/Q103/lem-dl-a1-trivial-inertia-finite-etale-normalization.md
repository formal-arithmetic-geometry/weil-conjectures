## Worker report

The module `Sheaf.AlgebraicGeometry.TrivialInertiaFiniteEtaleNormalization` states
`AlgebraicGeometry.finiteEtale_normalizationIn_of_trivial_inertia`, with one `sorry` and
no definitions. The node changes only in `lean`. No statement correction, new node,
dependency repair, or mathematical dispute is needed.

Source read: Stacks `pione.tex`, Tag 0BTD, final normalization argument in
`lemma-normal-pione-quotient-inertia`, and Tag 0BST,
`lemma-inertia-invariants-etale`. The current blueprint was also read at
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`:
the boundary-unramifiedness equivalence is the purpose of this prerequisite.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Integral scheme X | `(X : Scheme.{u}) [IsIntegral X]`; nonemptiness is part of this class. |
| Local rings integrally closed domains | `hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`. |
| K is the generic local ring | `X.functionField`, Mathlib's stalk at `genericPoint X`, with its canonical field instance. |
| L/K finite, separable, normal; Γ = Aut_K(L) | `(L : Type u) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L] [IsGalois X.functionField L]`; automorphisms are `L ≃ₐ[X.functionField] L`. |
| Every nonempty affine V = Spec A | `(V : X.Opens) [Nonempty V]` and `IsAffineOpen V`, with `A = Γ(X, V)` and the canonical chart `hV.fromSpec`. |
| B is the integral closure of A in L | `integralClosure Γ(X, V) L`, using the recorded Mathlib definition. |
| The inclusion A → L | Quantification over `[Algebra Γ(X, V) L] [IsScalarTower Γ(X, V) X.functionField L]` specifies exactly the composite of the germ map and K → L. These structures are unique, and exist for every V: define the algebra by `((algebraMap X.functionField L).comp (X.germToFunctionField V).hom).toAlgebra`; the tower identity is reflexive. This is not an additional assumption or a different choice of inclusion. |
| Trivial inertia at every prime of B | `hinertia` quantifies over `q : PrimeSpectrum B` and `g : L ≃ₐ[K] L`. Its premise says that every b has a conjugate c in B with `c = g b` in L and `c-b ∈ q`. This is precisely identity on B/q. Conjugation preserves B because it preserves monic equations over A; identity on B/q preserves q and extends uniquely to its fraction field. Conversely identity on the fraction field implies this congruence condition. Its conclusion `g = 1` says that the subgroup is trivial. |
| B^Γ = A | For each b in B, `(∀ g, g (b : L) = b) ↔ ∃ a : A, algebraMap A L a = b`. Equality is inside the given field L; no auxiliary ring is chosen. |
| Spec B → V finite etale | `IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧ Etale (...)`. The target `Spec A` is canonically V, and the subsequent chart clause composes with `hV.fromSpec`. |
| Spec L → X through the generic point, quasi-compact and quasi-separated | The two explicit conjuncts `QuasiCompact (X.fromSpecOfAlgebraFunctionField L)` and `QuasiSeparated (...)`. The upstream abbreviation is exactly `Spec.map (algebraMap K L) ≫ X.fromSpecFunctionField`. |
| The relative normalization Y → X is finite etale | `X.normalizationIn L` and `X.fromNormalizationIn L` are upstream abbreviations for the recorded Mathlib relative normalization of that exact map. Both `IsFinite` and `Etale` are conclusions. The integral factorization and dominant map from Spec L are supplied by the existing normalization API. |
| Its inverse image over V is Spec B | The next conjunct gives `e : (ν ⁻¹ᵁ V).toScheme ≅ Spec B` with `e.inv ≫ (ν ⁻¹ᵁ V).ι ≫ ν = Spec.map (algebraMap A B) ≫ hV.fromSpec`. Thus this is an isomorphism over the actual affine chart, not an unrelated abstract ring. |
| Canonical generic fibre Spec L | `e : Spec L ≅ pullback ν X.fromSpecFunctionField`, with first projection equal to the canonical `toNormalization`, and second projection equal to `Spec.map (algebraMap K L)`. These two equations determine e uniquely by the pullback universal property. |
| Any separable closure Ω/K containing L | The final conjunct quantifies over Ω with `IsSepClosure K Ω`, `Algebra L Ω`, and the compatible scalar tower. Field algebra maps are embeddings. |
| Any algebraic closure Ωa of Ω | `IsAlgClosure Ω Ωa`, with `Algebra K Ωa` and its tower compatibility fixing the structural map used in the fibre product. All objects live in a common arbitrary ambient universe u. |
| Evaluation identifies the geometric generic fibre with Hom_K(L, Ω) | `E : ↥(pullback ν (X.fromSpecOfAlgebraFunctionField Ωa) : Scheme.{u}) ≃ (L →ₐ[K] Ω)`. For each φ an Ωa-valued lift z has second projection the identity, first projection `Spec.map ((algebraMap Ω Ωa).comp φ.toRingHom) ≫ toNormalization`, and `E (z (IsLocalRing.closedPoint Ωa)) = φ`. These conditions characterize the equivalence by evaluation rather than merely asserting an arbitrary bijection. |
| Points have unique Ωa-valued lifts | `∀ y, ∃! z, z ≫ pullback.snd _ _ = 𝟙 _ ∧ z (closedPoint Ωa) = y`. This also makes the action-on-lifts convention an unambiguous action on the underlying points. |
| Unique extension of σ to Ωa | `∀ σ, ∃! τ : Ωa ≃ₐ[K] Ωa, ∀ a : Ω, τ (algebraMap Ω Ωa a) = algebraMap Ω Ωa (σ a)`. |
| G-action by t ↦ t ∘ Spec(τ) | `ρ : (Ω ≃ₐ[K] Ω) →* Equiv.Perm ↥(...)` records the action law. For every extending τ and based lift z, the next conjunct gives a based lift z' with `z' ≫ fst = Spec.map τ.toRingHom ≫ z ≫ fst` and `ρ σ (z (closedPoint Ωa)) = z' (closedPoint Ωa)`. This is exactly the stated precomposition of the lift to Y. |
| Equivariance, φ ↦ σ ∘ φ | `∀ σ y, E (ρ σ y) = σ.toAlgHom.comp (E y)`. |
| Stabilizer at L ⊆ Ω is Aut_L(Ω) | The final iff says `ρ σ (E.symm (IsScalarTower.toAlgHom K L Ω)) = E.symm (...) ↔ ∀ a : L, σ (algebraMap L Ω a) = algebraMap L Ω a`. The right-hand side is exactly fixing L pointwise, so identifies the stabilizer subgroup with Aut_L(Ω). |
| No Noetherian, excellence, or prior normalization-finiteness hypothesis | None occurs among the binders. In particular finite-dimensionality applies to L/K, never to B/A. |

Dependency declarations read and used (statement imports public, proof-only imports plain):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` for the normal-domain conjunction recorded by def-weil-pbc-normal-ring.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`; compatible inclusions use `IsScalarTower`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `.Integral`: `IsIntegralHom` (the normalization's integral morphism).
- `Mathlib.AlgebraicGeometry.Normalization`: `Scheme.Hom.normalization`,
  `toNormalization`, `fromNormalization`, `normalizationObjIso`,
  `toNormalization_fromNormalization`, `fromNormalization_app`,
  `normalizationObjIso_hom_val` and the integral/dominance instances.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`; these reuse
  exactly the preceding recorded relative-normalization construction.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: the module of the recorded
  `IsSepClosure.exists_intermediateField_mem`; its docstring identifies the notion
  itself as Mathlib's `IsSepClosure`, which is the class used here.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, with
  `IsAlgClosure` and `IsAlgClosure.equiv` from its `.Basic` import. The node permits
  any algebraic closure, not only the named canonical construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, used for the recorded geometric-fibre construction.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; its
  quasi-compact component is the recorded `QuasiCompact` in `.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.

Proof-plan dependencies are imported: `functionField_isFractionRing_of_isAffineOpen`
(from the public upstream normalization import),
`Scheme.fromSpecStalk_local_properties` in
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`,
`integral_totalFraction_mem_range_of_normal` in
`WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`,
`IsGalois.mem_range_algebraMap_iff_fixed` in `Mathlib.FieldTheory.Galois.Basic`,
`exists_etale_neighborhood_inertia_invariants` in
`Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale`,
`LocallyOfFinitePresentation.finitePresentation_appLE`,
`RingHom.Finite.of_isIntegral_of_finiteType`, `pullbackSpecIso`,
`LocalizedModule`, `separableClosure.isPurelyInseparable`,
`IsSepClosed.algebraMap_bijective`, `IsAlgClosure.equiv`,
`Algebra.separable_tensor_algebraicallyClosed_equiv_pi` in
`Sheaf.FieldTheory.SeparableTensorAlgebraicClosure`, and
`spec_finite_product_fields` in `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`.
Every stated proof dependency is available through a direct or public import; no import
cycle was introduced. The nine-step natural-language proof is in the theorem docstring.

Edge cases checked before writing:

- X is nonempty by integrality; the empty scheme is correctly excluded.
- Empty affine opens are excluded exactly where the statement excludes them, so their
  zero section ring never needs a map into L. No affine-cover index is assumed finite.
- For L = K, the Galois group is trivial, B = A by normality, and the normalization is X;
  the generic and geometric identifications reduce to their canonical one-point cases.
- X = Spec K reduces to a finite separable field spectrum, whose inertia at the zero
  prime is trivial and whose geometric points are exactly the K-embeddings.
- For imperfect fields in positive characteristic, Ωa need not equal Ω. The explicit
  extension τ and its uniqueness retain this case; no perfectness is assumed.
- Ramified examples such as Kummer extensions over a normal trait fail the inertia
  hypothesis at the ramified prime, as required. Wild inertia is not discarded.
- X can be non-Noetherian and nonseparated. Quasi-compactness and quasi-separatedness
  are conclusions about Spec L → X, not assumptions about X.
- Γ-triviality is expressed on the original automorphism group of L/K, not on a
  potentially nonfaithful quotient action on B. The fixed-ring equality retains the
  specified embedding of A, not merely an abstract isomorphism.
- All rings, schemes and closures use a common arbitrary universe u. The point types
  explicitly coerce a `Scheme.{u}` pullback, preventing accidental Type-category limits.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder "finite Galois normalization of a normal integral scheme with trivial inertia is finite etale"`:
  eight hits include Mathlib normalization, integral normalization morphisms and a proper
  finiteness result; none states this theorem or its geometric equivariance clauses.
- `msearch.py ... loogle "integralClosure, Algebra.Etale"`: one hit,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux`, assumes finite type
  and quasi-finiteness and constructs etale localization data, not this assertion.
- `msearch.py ... grep "normalization.*[Ee]tale|[Ii]nertia.*[Ee]tale"`: zero Mathlib hits.
- `msearch.py ... leansearch "normal integral scheme finite Galois normalization trivial inertia finite etale"`:
  eight normalization-construction hits; no finite-etale trivial-inertia theorem.
- `rg` for those normalization/etale and inertia/etale patterns in `lean/WeilConjectures`
  and `lean/Sheaf` found the existing inertia-invariants theorem and unrelated normalization
  results. Reading `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean` found
  the canonical constructions reused here; its finiteness theorem assumes locally finite
  type over a field and is not this general result.
- Searching the item id in `lean/WeilConjectures` returned no declaration.
- Searching `finiteEtale_normalizationIn_of_trivial_inertia` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no hit.

Validation: the required `scompile.py` compiled both the sandbox and library-context
module cleanly (11.1 s and 9.8 s). A preliminary probe also confirmed that the generic-point
map has the existing quasi-compact and quasi-separated instances, so the normalization
is usable without adding those conclusions as hypotheses. No local/global build was run.

## Second reading by Q103

A separate reading pass by the same dispatcher worker checked the node and final module;
no additional agent was started, in accordance with the brief. The maintainer's independent
review remains the independent reading, not a claimed review by a fictitious second worker.

This pass checked every row above against the final signature. In particular, the closure
algebra is not arbitrary: `IsScalarTower` forces the germ-composite inclusion. The inertia
condition includes existence of each conjugate in B, so the congruence is not a vacuous
implication. The affine finite-etale assertion retains every nonempty affine open and prime.
The relative normalization is the actual canonical upstream construction. Both projections
characterize the generic-fibre isomorphism. Evaluation is tied to Spec of φ, and the action
is a genuine group homomorphism, characterized by precomposition on lifts; it uses σ rather
than σ inverse. The stabilizer is tested at the actual inclusion, not an unspecified point.
Positive-characteristic purely inseparable algebraic closures remain covered. No mathematical
mismatch or node fault was found. The compile-driven corrections only made scheme-to-point
coercions explicit and removed a mismatched parenthesis; the mathematical statement did not
change. No new definitions or dependency modules require a separate audit.
