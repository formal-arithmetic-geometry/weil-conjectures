## Worker report

The module `lean/Sheaf/RingTheory/FiniteProjectiveCokernelLocalization.lean` states
`Module.finiteProjectiveCokernel_residue_localization` for a commutative ring `R`,
finite projective modules `P₁` and `P₂`, a linear map `φ`, and a prime ideal `p`.
Finite projectivity is rendered by the explicit typeclass hypotheses
`[Module.Finite R Pᵢ]` and `[Module.Projective R Pᵢ]`. The residue-field map is
`φ.baseChange p.ResidueField`.

The first implication exactly renders the injective-fibre clause: it gives `f : R`
with `f ∉ p`, injectivity of `φ.baseChange (Localization.Away f)`, and finite
projectivity of its cokernel. The cokernel is represented by
`TensorProduct R (Localization.Away f) P₂ ⧸ LinearMap.range
(φ.baseChange (Localization.Away f))`, with `Module.Finite` and
`Module.Projective` instances over `Localization.Away f`. The second implication
renders the isomorphism-fibre clause as bijectivity of the base-changed map and
produces `f ∉ p` with bijectivity after localization.

No statement dependencies are listed by the node, so no project-specific
 dependency declarations are imported. The proof is `sorry`, as required for stage 2;
the docstring records the node proof: localize both finite projectives to finite free
modules near `p`, apply the finite-free residue-localization lemma, and compose the
principal localizations.

Edge cases checked: `P₁` or `P₂` may be zero (the typeclasses permit zero modules),
`p` is any prime ideal including primes in a zero ring when present, and no positive
rank or nonempty index is imposed. Independent universes `u`, `v`, `w` allow modules
of different sizes; `Fin 0`-type behavior is not excluded by the formulation.

Searches for an existing declaration:

- `msearch.py ... leanfinder "finite projective linear map injective residue field localization cokernel projective"` returned only general projectivity/localization lemmas (`Module.projective_of_localization_maximal`, `Module.Finite.exists_comp_eq_id_of_projective`, residue-field local-ring lemmas), with no matching theorem.
- `msearch.py ... loogle "Module.Projective LinearMap.baseChange ResidueField"` returned zero hits (and an application-type diagnostic for `LinearMap.baseChange`).
- `msearch.py ... grep "finiteProjectiveCokernel|cokernel-flat" Mathlib/RingTheory` returned zero hits.
- `rg` over `WeilConjectures/` found no declaration for this theorem; `rg` over `lean/Sheaf` found only the distinct finite-free specialization and a scheme-level residue-isomorphism theorem.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

The second reader should compare the node and file clause by clause. The binders
for the ring, two finite projective modules, map, and prime ideal are explicit. The
first implication has exactly the two required residue/localization maps, the
outside-prime condition, injectivity, and finite-projective cokernel; the second has
exactly the outside-prime condition and localized isomorphism. The quotient by the
linear-map range is the standard cokernel representation used by the finite-free
sibling. No additional hypotheses or conclusions occur.

## Second reading by S1

I read the node as the following ordered list. First, introduce a commutative ring `R`,
finite projective `R`-modules `P₁` and `P₂`, a homomorphism `φ : P₁ → P₂`, and a prime
ideal `p`. The first conclusion clause assumes that the residue-field map
`φ ⊗ κ(p)` is injective and requires an element `f ∉ p` for which the localized map is
injective and its cokernel is finite projective over `R_f`. The second clause assumes
that the residue-field map is an isomorphism and requires `f ∉ p` for which the localized
map is an isomorphism.

The Lean renders these items as `{R : Type u} [CommRing R]`, modules `P₁ : Type v` and
`P₂ : Type w` with `[AddCommGroup]`, `[Module R]`, `[Module.Finite R]`, and
`[Module.Projective R]`, followed by `(φ : P₁ →ₗ[R] P₂)` and `(p : Ideal R) [p.IsPrime]`.
The residue-field map is `φ.baseChange p.ResidueField`; localization is represented by
`φ.baseChange (Localization.Away f)`. The first implication gives
`f : R`, `f ∉ p`, injectivity, and `Module.Finite` plus `Module.Projective` for
`TensorProduct R (Localization.Away f) P₂ ⧸ LinearMap.range
(φ.baseChange (Localization.Away f))`, the standard cokernel of the localized map.
The second implication gives exactly `f ∉ p` and bijectivity of the localized map.
Thus every object, hypothesis, quantifier order, and conclusion clause agrees with the
node; no extra assumptions or omitted clauses were found. The node's `lean.statement`
is verbatim the theorem signature.

The Stacks source (Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3)) assumes
only a ring and finite projective modules. Its local-open formulation implies the two
pointwise existential clauses in the node by choosing a principal neighborhood of `p`.
The source also permits zero modules and empty-rank free summands, which the Lean
class hypotheses preserve. No positivity, nonempty index, characteristic, or universe
restriction is introduced; the independent universes `u`, `v`, and `w` preserve the
source's generality. A zero ring/prime and zero `P₁` or `P₂` remain admissible whenever
Lean supplies the stated instances.

I repeated the existing-declaration searches. `msearch.py` LeanFinder for finite
projective residue-fibre localization, Loogle for
`Module.Projective LinearMap.baseChange ResidueField`, and grep searches through
Mathlib/RingTheory, `WeilConjectures/`, and `lean/Sheaf` found no declaration with this
statement. The finite-free sibling and unrelated projectivity/localization lemmas are
not matches, so this module is needed.

No mismatch was found and no repair was necessary. The module compiles cleanly with
`scompile.py`; its only proof is the required `sorry`, and the docstring identifies
Stacks Tag 00O0 and the blueprint and records the two localization steps.
