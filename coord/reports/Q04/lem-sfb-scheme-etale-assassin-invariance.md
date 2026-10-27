## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAssociatedPoints` states
`AlgebraicGeometry.Scheme.Modules.associatedPoints_tensorPullback_iff_of_etale`.
Its only theorem has proof `by sorry`, as required for stage 2. No definitions,
new nodes, dependency repairs, or statement corrections are introduced.

Hypothesis and conclusion correspondence:

- Schemes V and U: `{V U : Scheme.{u}}`; the universe `u` is explicitly declared.
- The morphism h: V → U: `(h : V ⟶ U)`.
- Etaleness of h: `[Etale h]`, the recorded Mathlib predicate.
- U locally Noetherian: `[IsLocallyNoetherian U]`.
- V locally Noetherian: `[IsLocallyNoetherian V]`.
- Any O_U-module G: `(G : U.Modules)`.
- Quasi-coherence of G alone: `(hG : G.IsQuasicoherent)`. In particular the
  dependency's conjunction `IsQuasiCoherentFiniteType` is not assumed.
- Zariski tensor pullback h*G: `((tensorPullback h).obj G)`, the existing explicit
  inverse-image/change-of-rings construction, imported through the recorded
  section-normalized adjunction module. No new pullback is defined.
- Every point v: `(v : V)`; its image u is the term `h v`, so no separate point
  or equality hypothesis is needed.
- The associated-point condition on V:
  `v ∈ associatedPoints ((tensorPullback h).obj G)`.
- If and only if the associated-point condition on U:
  `↔ h v ∈ associatedPoints G`.
- Both sets use `Scheme.Modules.associatedPoints`, defined by membership of the
  stalk-ring maximal ideal in the element-annihilator associated primes of the
  actual module stalk. This is not Mathlib's radical-annihilator associated-prime
  convention and not the structure-sheaf-only associated-point predicate.
- There is no `IsFiniteType`, coherence, finite-generation, surjectivity,
  quasi-compactness, separatedness or affineness binder.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes
  `SheafOfModules.IsQuasicoherent`; its separate finite-type conjunction is unused.
  The defining Mathlib quasi-coherence declaration and docstring were read.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly imports
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, supplying
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. Its object is the explicit
  inverse-image sheaf followed by extension of scalars and sheafification.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `AlgebraicGeometry.Scheme.Modules.associatedPoints`.

Proof dependencies are imported without `public`; those already publicly imported
for the statement are not imported a second time. The proof docstring gives all
four DAG steps, including the affine neighbourhood reduction and prime contraction,
restriction/pullback comparisons and affine section tensor equivalence, etale
weak-association invariance with the tensor flip, and Noetherian conversion to
annihilator association followed by the affine associated-point dictionary.
Relevant declarations read include `Etale.instResLE`,
`IsLocallyNoetherian.component_noetherian`, `Spec`, `Spec.map`,
`Scheme.Modules.restrictFunctor`, `restrictAdjunction`,
`nonempty_tensorPullbackId`, `nonempty_tensorPullbackComp`,
`exists_locallyQuasicoherent_affine_pullback_sections`,
`Scheme.Modules.isQuasicoherent_pullback`,
`Module.weakly_associated_tensor_iff_of_etale`,
`Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`,
`Scheme.Modules.affine_associated_points_primes`, and `IsNoetherianRing`.
The recorded quasi-coherence preservation theorem uses abstract pullback; its
application to tensor pullback is transported along the left-adjoint-uniqueness
isomorphism. This is part of the proof plan and does not require a second predicate
or an extra hypothesis in this statement.

Sources checked directly in the local Stacks text: `flat.tex`,
`lemma-etale-weak-assassin-up-down` (05FP), states the weak-assassin equivalence for
any quasi-coherent module. `divisors.tex`, `lemma-ass-weakly-ass` (05AR), says that
Ass and WeakAss coincide on a locally Noetherian scheme. These give exactly the
node's statement without a finite-generation restriction.

Edge cases checked mathematically before writing:

- Empty V: the universally quantified point condition is vacuous. No nonemptiness
  hypothesis is present. A map to empty U also has empty source.
- G = 0: the maximal ideal of a stalk is proper, whereas the annihilator of the
  sole element of the zero module is the whole ring, so both associated sets are
  empty; tensor pullback is again zero.
- Identity and arbitrary open immersions: the equivalence is the expected local
  associated-point condition. Non-surjective maps and non-quasi-compact open
  immersions remain in scope.
- Infinite quasi-coherent direct sums and non-finite modules: the signature only
  asks for quasi-coherence, and the affine weak-association and finitely-generated
  prime inputs impose no finite generation on the module.
- Zero rings and empty affine charts cause no extra point case; a chosen point
  automatically excludes the zero ring on its neighbourhood.

Searches run for this item using the prescribed msearch.py wrapper:

- LeanFinder: `For an etale morphism of locally Noetherian schemes a point is associated to the tensor pullback of a quasi coherent module if and only if its image is associated`.
  Eight hits concerned the etale locus, base change, and etale algebras; no
  associated-point statement matched.
- Loogle: `"associatedPrimes", "Etale"`. Successful service response, zero hits.
- Mathlib grep: `associatedPoints|[Ee]tale.*associatedPrimes|associatedPrimes.*[Ee]tale`.
  Successful search, zero hits.
- LeanSearch: `Etale pullback preserves and reflects associated points of arbitrary quasi coherent modules on locally Noetherian schemes`.
  Eight hits concerned abstract pullback and etale morphisms; none matched.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `associatedPoints|[Ee]tale.*associatedPrimes|associatedPrimes.*[Ee]tale` found
  the existing module-associated-points definition, the affine dictionary, and
  `FlatPullbackAssociatedPoints`. The latter states the general flat-fibre union
  formula, not this pointwise etale equivalence; no duplicate was written.
- Direct `rg` for `lem-sfb-scheme-etale-assassin-invariance` in
  `lean/WeilConjectures` found nothing. Searches for the proposed full declaration's
  final component in both source roots, Mathlib and `dag/lean_names_upstream.json`
  also found no existing declaration.

Validation: the prescribed `scompile.py Q04 lem-sfb-scheme-etale-assassin-invariance`
compiled both the sandbox form (2.7 s) and the actual module form (3.4 s) cleanly,
with no compiler errors or warnings. The delivery dry run and final delivery use
`deliver2.py`, which repeats per-file compilation and server preflight.

No statement dispute or node fault found. The shared repository and its library
were read only; all authored files are in the assigned sandbox.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
