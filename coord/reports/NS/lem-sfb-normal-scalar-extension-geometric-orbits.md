## Worker report

The module `Sheaf.AlgebraicGeometry.NormalScalarExtensionGeometricOrbits` states
`AlgebraicGeometry.NormalScalarExtension.geometric_orbits`, with its proof `sorry`.
Its four auxiliary declarations are actual pullback objects, projections, and induced
maps belonging to this statement, rather than new independent notions. There are no
new DAG nodes, dependency repairs, or statement corrections. The original node fields
are preserved except for `lean`.

The source was read in the local ILO PDF, X 2.3, Step 2, printed p.150: diagram
(2.b), its equivariant scalar diagram, and the assertion that it retains conditions
(i)--(iv). The node explicitly elaborates its geometric-orbit argument using the
listed Stacks facts; its eight proof steps are reproduced in the theorem docstring.
The current blueprint unit `_section.md` was also read; the item is an auxiliary
lemma, not that unit's six-functor statement.

Hypotheses, individually:

| Node | Lean rendering |
| --- | --- |
| Fields e ⊆ F ⊆ K | `e F K : Type u`, three `Field` instances, `Algebra e F`, `Algebra F K`, `Algebra e K`, and `IsScalarTower e F K` |
| Finite degree K/e | `Module.Finite e K`; this is the finite-extension notion documented in `FieldExtension.degree`'s owning module, not finite type as an algebra |
| Normality, without separability | `Normal e K`, whose source definition is algebraicity and splitting of all minimal polynomials |
| Finite groups J and Γ | Independent group universes `v w`, `Group` and `Finite` for each |
| ρ, r, α homomorphisms | `ρ : J →* (F ≃ₐ[e] F)`, `r : Γ →* J`, `α : Γ →* (K ≃ₐ[e] K)` |
| r surjective | `hr : Function.Surjective r` |
| α restricts on F to ρ ∘ r | `hc`, the corresponding commuting square on spectra using inverse automorphisms; full faithfulness and contravariance of Spec make this exactly the stated restriction, also for inverses |
| α(ker r) = Aut_F(K) | `hk`: for every e-algebra automorphism τ, membership in the image of the kernel is equivalent to fixing every image of F. Since the tower commutes, this is precisely Aut_F(K), and includes both set inclusions |
| Finite-type F-scheme V | `V`, `p : V ⟶ Spec (.of F)`, `LocallyOfFiniteType p`, `QuasiCompact p` |
| Left semilinear J-action | `a : J →* Aut V`; `hs` says `(a j).hom ≫ p = p ≫ Spec.map (ρ j).symm.toRingHom`, with the node's inverse convention |
| An e-scheme B | `B`, `s : B ⟶ Spec (.of e)` |
| v an e-morphism | `v : V ⟶ B` and `he`, its commuting structural square |
| v J-invariant | `hv : ∀ j, (a j).hom ≫ v = v` |
| Every algebraically closed geometric point b | `Ω : Type u`, `Field Ω`, `IsAlgClosed Ω`, and `b : Spec (.of Ω) ⟶ B` |
| Nonempty single J-orbit in V_b | `hn : Nonempty ↥(pullback v b)` and `ht`, which uses the actual induced map `fibreMap` |

Objects and conclusions, individually:

* `V_b` is exactly `pullback v b`, with the recorded Mathlib projections.
* `fibreScalar p v b` is its map to Spec F.
* `scalarFibre K p v b` is `(V ×_B Spec Ω) ×_F Spec K`. This is a chosen
  presentation of W_b: pullback associativity gives the unique isomorphism to
  `(V ×_F Spec K) ×_B Spec Ω` commuting with the V, K, and Ω projections.
  Thus W is not replaced by an arbitrary scheme or a supplied comparison map.
* `fibreMap` is `pullback.map` of `(a j).hom` and identity on Ω over identity on B.
  `diagonalMap` is `pullback.map` of `fibreMap (r γ)` and Spec(α(γ) inverse),
  over Spec(ρ(r γ) inverse). The commuting-square proofs are checked structural
  proofs, not postponed construction data. No arbitrary lifted action is assumed.
* Rationality is the first conclusion: for every x there is an isomorphism
  `i : .of Ω ≅ (pullback v b).residueField x`, whose `hom` is explicitly the
  structural residue map. That map is `Spec.preimage` of
  `fromSpecResidueField x ≫ pullback.snd v b`; this avoids introducing a second
  definition of a structural residue map. In particular the isomorphism is not
  an unconstrained abstract field isomorphism.
* The scalar map F → Ω at x is `Spec.preimage (fromSpecResidueField x ≫
  fibreScalar p v b) ≫ i.inv`. The subtype of ring homomorphisms `β : K →+* Ω`
  imposes exactly agreement with this map on F. Field ring homomorphisms are
  automatically embeddings; no additional injectivity hypothesis is needed.
* `E` is an equivalence from this embedding subtype to the actual point fibre
  `{y : scalarFibre ... // pullback.fst ... y = x}`. `Nonempty` of the embedding
  subtype states the separate nonemptiness clause.
* The evaluation characterization is explicit. For each β, the morphism `t`
  has first projection `Spec.map i.inv ≫ fromSpecResidueField x`, second
  projection `Spec.map β`, and Ω projection identity; `E β` is its image point.
  The pullback property uniquely determines t. Pulling back to the rational
  point x and using `pullbackSpecIso F Ω K` identifies this with the map from
  Spec Ω induced by the tensor evaluation. Its restrictions to Ω and K are
  respectively identity and β, so the tensor universal property forces exactly
  `z ⊗ k ↦ z * β(k)`. This is the complete evaluation characterization, expressed
  using projections so that no artificial F-algebra structure on Ω is assumed.
* The kernel-action clause quantifies every γ with `r γ = 1` and every β₁,
  asserts existence of an extending embedding β₂ with
  `β₂.val = β₁.val.comp (α γ).symm.toRingHom`, and identifies `E β₂` with
  `diagonalMap ... γ (E β₁)`. Thus closure under that formula is stated, not
  merely a conditional equivariance if the composite happens to exist.
* The final two conjuncts give `Nonempty (scalarFibre ...)` and, for every pair
  of its points, a γ carrying the first to the second under the constructed
  diagonal map. These express the nonempty single Γ-orbit.
* No separability, reducedness, faithful action, normality of F/e, finite type
  of B, or quasi-compactness of v is present. In particular the finite-type
  hypothesis is on p, exactly as in the node.

Dependency declarations read and used:

* `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
* `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`, with its documentation
  that finite extensions use `Module.Finite` (the degree function itself is not
  needed as a term of this statement).
* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`; scheme pullbacks are provided by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`, and
  `Scheme.SpecToEquivOfField`. The latter two supply the precise description
  of a rational point used here, rather than a new point notion.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the source signatures
  for `IsAlgClosure` and `AlgebraicClosure` were also checked. Only the
  algebraically closed field notion is required by the geometric-point clause.
* `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage`, whose
  inverse is `Spec.map` (`Spec.homEquiv`), for canonical structural residue maps.
* `Mathlib.FieldTheory.Normal.Defs`: `Normal`, `Normal.tower_top_of_normal`,
  `Normal.algHomEquivAut`; this also supplies the two field-theoretic proof leaves.
* The remaining recorded proof leaves are imported via
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (`IsAlgClosed.lift`,
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`),
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic` (`residueFieldIsoBase` and
  `SpecMap_residueFieldIsoBase_inv`),
  `Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`),
  `Mathlib.AlgebraicGeometry.PullbackCarrier` (`Scheme.Pullback.carrierEquiv`
  and its projection lemmas), and `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  (`locallyOfFiniteType_iff`, `locallyOfFiniteType_isStableUnderBaseChange`).
  All these recorded signatures and their docstrings were opened locally.

Edge cases checked before writing and on the second pass:

* Empty V or an empty geometric fibre is excluded only by the node's `hn`.
  Empty B admits no b, as required; there is no nonempty-base hypothesis.
* Trivial J or Γ, and identity field extensions, are included.
* A purely inseparable K/F can yield a nonreduced tensor algebra; primes,
  residue fields and evaluation points still give a singleton fibre. No
  reduced or separable tensor decomposition appears anywhere in the statement.
* F/e may be nonnormal, and either action may have kernel.
* B can be arbitrary and v need not be quasi-compact. The proof docstring first
  derives local finite type, rather than quietly assuming finite type of v.
* All schemes and fields share an arbitrary ambient scheme universe `u`, with
  independent group universes `v w`. Every binder is explicit and autoImplicit
  is disabled. Point types of the categorical pullback use explicit coercions.

Searches (2026-10-24):

* `msearch.py ... leanfinder "Finite normal scalar extension of a scheme preserves
  transitivity of geometric fibres and identifies fibres with field embeddings"`:
  eight hits, including finite fibres and the pullback-carrier tensor maps; none
  states the orbit result or its residue/evaluation/action package.
* `msearch.py ... loogle "Normal, Scheme, MulAction"`: zero hits, unknown identifier
  `Scheme` in the service's unqualified context.
* `msearch.py ... leansearch "scheme finite normal field extension geometric points
  transitive group action"`: eight hits on Galois groups, fixed fields, Sylow
  actions and transitivity of primes over a Galois extension. These assume
  different data and do not state the scheme lemma (in particular they do not
  replace normality by a separable Galois hypothesis here).
* `msearch.py ... grep "semilinear|[Nn]ormal.*[Oo]rbit|[Ss]calar.*[Oo]rbit"
  AlgebraicGeometry`: four unrelated structure-sheaf semilinear localization hits.
* Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for semilinearity,
  diagonal actions, scalar-extension orbits, and actions `→* Aut` found related
  action statements but no matching theorem. The requested node-id search in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json` found no declaration.
* The source of `SurfacePointBlowup.fieldMap` was read after the scalar-map search.
  A provisional duplicate helper was removed: the final statement directly uses
  the existing `Spec.preimage` construction. The four remaining helpers are only
  the concrete iterated pullback and its maps, with all data written in full.
* Full-name searches for the new namespace and `geometric_orbits` in Mathlib,
  WeilConjectures and Sheaf found no collision (the unrelated
  `affine_action_stack_geometric_orbits` has different hypotheses and conclusion).

No `STATEMENT-DISPUTED` issue was found. Validation uses only the prescribed
`scompile.py` and `deliver2.py` wrappers. The final compilation and delivery
preflight results are recorded below after they finish.

## Second reading by NS

A separate second pass in this worker session re-read the node's whole statement,
its eight proof steps and the completed module. No other agent was started, as
instructed; the maintainer's independent review remains separate.

The re-reading checked the inverse in both semilinear base maps, both directions
of the kernel-image equality, the structural (not arbitrary) residue isomorphism,
the scalar map in the embedding subtype, the two evaluation projections and Ω
normalization, the action on embeddings, and nonemptiness of both the embedding
sets and W_b. It found that an initial implication comparing two already-given
embeddings would not explicitly state closure under the kernel formula. This was
changed to existence of the composed embedding together with its formula and
point action. A duplicate structural-residue-map helper was also removed in favour
of `Spec.preimage` of the canonical residue-field point. Explicit point coercions
resolved elaboration of the chosen categorical pullbacks. Two long lines were
wrapped after compiler warnings. The node's mathematical statement needed no change.

Validation: final `scompile.py` passed for both the sandbox and actual library module,
2.1 seconds each, with no errors or warnings. `deliver2.py --no-push` then printed
`OK (dry run): commit 2395a0c8514 passes the preflight and compiles; nothing pushed`.
