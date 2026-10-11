## Worker report

The module `Sheaf.AlgebraicGeometry.ProjTildeFunctorial` states
`AlgebraicGeometry.Proj.tilde_functorial`, with one `sorry` and no definitions.
The statement is unchanged. No missing notion, unusable dependency, or statement
correction was needed.

The three modules M, N, L are written as `M : Fin 3 → Type u`, with indices 0, 1,
2 respectively. This packages three independently chosen graded modules, rather
than restricting their objects. The conclusion quantifies maps between these
three modules, so its composition clause specializes to indices 0, 1, 2. Taking
any universal triple, this is equivalent to the node's universally quantified
assertion, including identity and composition. A common universe can be chosen
large enough for the ring and all three modules, as in the dependency interface.

Hypotheses and identifications, clause by clause:

- N-graded commutative ring S: `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, `[GradedRing 𝒜]`.
- X = Proj(S): `Proj 𝒜`. Its points already encode homogeneous primes not
  containing the irrelevant ideal; S_+ needs no extra parameter or hypothesis.
- Z-graded S-modules M, N, L: `M`, the pointwise `AddCommGroup` and `Module S`
  instances, `𝓜 : ∀ i, ℤ → AddSubgroup (M i)`, the direct-sum decomposition
  `h𝓜`, and the homogeneous scalar compatibility `hsmul`.
- Their associated sheaves: `F : Fin 3 → (Proj 𝒜).Modules`. These are any of the
  associated sheaves supplied by `gradedModuleSheaf_exists`, not arbitrary
  sheaves: `alpha`, `halpha`, `hscalar`, and `hres` specify exactly the canonical
  chart identifications and restrictions in clauses (a) and (b) of that lemma.
  The maps are its additive equivalences followed by inclusions into ordinary
  localized modules. `Function.Injective` and prescribed `Set.range` are the
  equivalent presentation of an additive equivalence onto those fractions.
- Sections on D_+(f) for homogeneous positive-degree f: all `f,d,hd,hf` are
  quantified; the image in `halpha` is the shared `degreeZeroFractions` in
  `LocalizedModule.Away f (M i)`. Numerator degree is the integer coercion of
  the nonnegative degree of the denominator, as required for degree zero.
- Module identification over S_(f): `hscalar` uses `awayToSection 𝒜 f` on
  structure-sheaf scalars and the canonical `algebraMap` into `Localization.Away f`
  on ordinary localized-module scalars. No additional module structure is chosen.
- Canonical restrictions, part of the meaning of “associated”: `hres` is the
  fraction formula `a^m • y / g^(e*m)` whenever `g^e = a*f` and D_+(g) ≤ D_+(f).
  It is exactly the dependency's `rho` formula transported by its `alpha`.
- Stalk identifications of dependency clause (c): `mu`, `hmu` give injective
  additive maps with image exactly the degree-zero fractions at
  `x.asHomogeneousIdeal.toIdeal.primeCompl`. `hgerm` is the dependency's germ
  formula, making these the canonical identifications, not arbitrary ones.
  The dependency's scalar law on these stalks is implied by the chart scalar
  law and this germ formula; it need not be separately assumed here.

Conclusions, clause by clause:

- Every degree-preserving S-linear phi: `phi : M i →ₗ[S] M j` and the argument
  `hphi : ∀ z y, y ∈ 𝓜 i z → phi y ∈ 𝓜 j z` of `lift`.
- Existence and uniqueness of tilde(phi) with its chart formula: the first
  conjunct says for every sheaf morphism `chi`, its chart fraction formula is
  equivalent to `chi = lift i j phi hphi`. This gives existence by taking chi
  equal to lift, and uniqueness among precisely the maps with that formula.
  Every denominator f^m and every representative y are quantified, without
  an extra hypothesis on y: equality to the image of a section already puts
  its fraction in M_(f), and linear localization acts on every representative.
- Composition: the second conjunct is
  `lift i k (psi.comp phi) ... = lift i j phi hphi ≫ lift j k psi hpsi`.
  The explicit proof argument is the composition of the two degree-preservation
  hypotheses. Categorical composition is written in Lean's order.
- Identity: the third conjunct is `lift i i LinearMap.id ... = 𝟙 (F i)`.
- Stalk fraction formula: the last conjunct uses the same sheaf map and
  `RingedSpace.moduleStalkFunctor ... .map`. For `h` in the complement of the
  prime, homogeneous of degree d, and y of the same degree, if `mu i x s = mk y h`,
  then the stalk image is sent by `mu j x` to `mk (phi y) h`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`,
  `AlgebraicGeometry.Proj`: the scheme of the N-graded ring. The additional
  source-recorded `Proj.projectiveSpaceOverAffine` is a polynomial specialization
  and is not needed for this general statement.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist`,
  `AlgebraicGeometry.Proj.twist`: read its full definition and section variables.
  The dependency record explicitly delegates general M~ (clause (1)) to
  `gradedModuleSheaf_exists`. This item involves no twisting sheaf O(d), so this
  specialized module is not imported unnecessarily and no new twist is defined.
- `Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists`,
  `AlgebraicGeometry.Proj.gradedModuleSheaf_exists`: imported; its chart, scalar,
  restriction, stalk, and germ interfaces are the data used in the hypotheses.
  Its local abbreviations/instances are not reused outside its file. All types
  here are explicit Mathlib and shared project types, without local notation.
- The transitive shared declarations `LocalizedModule.degreeZeroFractions`
  (`Sheaf.Algebra.Module.DegreeZeroFractions`) and
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`
  (`Sheaf.Algebra.Homology.ModuleStalkFunctor`) provide fraction carriers and
  actual module-stalk objects and maps.

Edge cases checked: the zero ring and empty Proj have no points; chart and stalk
conditions remain meaningful, and morphisms on the empty space are unique.
The irrelevant ideal can vanish (again Proj is empty). Zero modules, zero maps,
all characteristics, and zero fractions are included. There is no positive
numerator condition. The stalk formula allows d=0 and any homogeneous denominator
outside the prime; only standard-chart denominators require positive degree.
Repeated modules, identity maps, and all indices i=j or i=j=k are included.
Nilpotent homogeneous chart denominators give empty opens and zero localizations,
which are included. All universes and variables are explicitly bound.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch`: “degree preserving map of graded modules induces
  a unique morphism of associated module sheaves on Proj”: service unavailable
  (Internal Server Error), no results; no verdict assigned for this service.
- `msearch.py ... leanfinder`: “degree preserving linear map of graded modules
  induces a functorial morphism of associated sheaves on Proj”: 8 hits, including
  Proj.res_apply, awayMap_awayToSection, awayToΓ, toOpen_toSpec_val_c_app, and
  fromOfGlobalSections; these are structure-sheaf/ring maps, not general module
  sheaf maps. No match.
- `msearch.py ... loogle`: `AlgebraicGeometry.Proj, LinearMap, SheafOfModules`:
  zero hits.
- `msearch.py ... grep`: `gradedModuleSheaf|tilde.*[Ff]unctor|[Ff]unctor.*tilde`
  in Mathlib/AlgebraicGeometry: 5 hits, all in Modules/Tilde.lean, the affine Spec
  tilde functor; not the Proj construction.
- `rg` for the same pattern and the item id in source `WeilConjectures` and
  project `lean/Sheaf`: affine tilde uses and the associated-sheaf existence
  theorem, no Proj module-sheaf functoriality theorem. Source grep for the item
  id returned no hit.
- `rg` for `tilde_functorial` in Mathlib, source WeilConjectures and
  `dag/lean_names_upstream.json`: no collision with the proposed declaration.

The Stacks source was not present in this clone. Read the official source at
https://stacks.math.columbia.edu/tag/01M7: clauses (2), (3), (5), and its final
functoriality paragraph agree with the node. No node fault or mathematical
statement dispute was found.

Validation: server compilation initially succeeded with a whitespace warning;
removed the extra space, then reran the required dry-run compilation/preflight.
No second-reading section is supplied by the author: that belongs to the second reader.

## Second reading by Q1

I read the node statement and the complete declaration `AlgebraicGeometry.Proj.tilde_functorial` in `lean/Sheaf/AlgebraicGeometry/ProjTildeFunctorial.lean`.

- The graded ring object is rendered by `{S : Type u} [CommRing S]`, `𝒜 : ℕ → AddSubgroup S`, and `[GradedRing 𝒜]`; `Proj 𝒜` is the scheme X. No separate irrelevant ideal is needed because the Proj type carries the homogeneous-prime condition.
- The three graded modules are `M : Fin 3 → Type u` with additive-group and S-module instances, `𝓜 : ∀ i, ℤ → AddSubgroup (M i)`, internal direct-sum hypotheses `h𝓜`, and the homogeneous scalar law `hsmul`. The Fin 3 packaging supplies arbitrary M, N, L and all index choices in the node.
- The associated sheaves are `F : Fin 3 → (Proj 𝒜).Modules`; `alpha`, `halpha`, `hscalar`, and `hres` give the standard-open section identifications, degree-zero fraction ranges, scalar compatibility, and restriction formula required by the associated-sheaf construction.
- The stalk identifications are `mu`, `hmu`, and `hgerm`, with the exact degree-zero fraction image at each homogeneous prime complement and the germ formula.
- The first conclusion conjunct quantifies every degree-preserving linear map `phi` (the component-preservation hypothesis `hphi`) and characterizes exactly the unique sheaf morphism `lift` by the fraction formula on every positive-degree standard open. The second conjunct is the composition law, the third is the identity law, and the fourth is the stalk fraction formula for `h` and `y` of the same homogeneous degree.

The quantifier order and all clauses agree with the node. The `Fin 3` indexing is equivalent to naming M, N, L and includes repeated modules and all identity/composition cases. No mismatch was found and no source or Lean change was required.

Edge cases checked: zero ring, zero modules and maps, empty Proj, vanishing irrelevant ideal, nilpotent or empty standard opens, degree zero stalk denominators, arbitrary characteristics, and indices with repetitions are all admitted. Universes are explicitly bound by one `u`, and no independent index or test-object universe is introduced.

Searches were reviewed against Mathlib, `WeilConjectures`, and `lean/Sheaf` using `msearch.py` LeanSearch/LeanFinder/Loogle queries and `rg` searches for `gradedModuleSheaf`, `tilde_functorial`, and related Proj/sheaf-map names. Only affine tilde and structure-sheaf declarations were found; no existing declaration states this Proj functoriality theorem. The dependency declaration `AlgebraicGeometry.Proj.gradedModuleSheaf_exists` was opened and its chart, scalar, restriction, stalk, and germ interfaces are exactly those used here. No missing notion, unusable dependency, hollow definition, or statement correction was found.
