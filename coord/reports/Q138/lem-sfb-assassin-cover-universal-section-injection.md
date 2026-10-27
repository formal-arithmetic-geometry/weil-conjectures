## Worker report

The module `Sheaf.RingTheory.AssassinCoverUniversalSectionInjection` states Stacks
Project, More on Flatness, Tag 05DH (`flat.tex`,
`lemma-base-change-universally-flat`), with a single sorry theorem and no new definitions.
I read the complete source statement and proof, the current node's four proof steps,
all seven statement dependency records, and the signatures and docstrings used below.

Hypothesis and conclusion correspondence:

- Commutative rings R -> C -> D: the three `CommRing` binders and `Algebra R C`,
  `Algebra C D`. An algebra structure over a commutative ring records precisely a
  ring map; no R-algebra structure on D is separately required.
- P is a C-module: `AddCommGroup P`, `Module C P`. `Module R P` together with
  `IsScalarTower R C P` records restriction along R -> C, rather than an extra
  mathematical hypothesis. Taking the C scalar to be 1 gives the prescribed R-action.
- C finitely presented over R: `Algebra.FinitePresentation R C`.
- P finitely presented over C: `Module.FinitePresentation C P`.
- P flat over R: `Module.Flat R P`.
- D flat over C: `Module.Flat C D`, equivalent to `RingHom.Flat (algebraMap C D)`
  by `RingHom.flat_algebraMap_iff` in the recorded flat-ring-map module.
- For each q with contraction p: `hcover` quantifies over `PrimeSpectrum R` and
  `PrimeSpectrum C` and requires `q.asIdeal.comap (algebraMap R C) = p.asIdeal`.
  Quantifying p separately with this equality gives exactly the unique contraction.
- Element-annihilator associated-prime condition in the specified fibre:
  `q.asIdeal ∈ annihilatorAssociatedPrimes C (P ⊗[R] p.asIdeal.ResidueField)`.
  The C-action is the canonical action through P, so this is the C-module in the
  node, without a Noetherian assumption or a weakly-associated-prime replacement.
- Image containment: `q ∈ Set.range (PrimeSpectrum.comap (algebraMap C D))`.
  This is exactly the underlying-point image of the recorded `Spec.map`.
- Canonical section u: `((TensorProduct.mk C P D).flip (1 : D)).restrictScalars R`.
  The bilinear tensor constructor evaluated in its second variable at 1 gives
  `p ↦ p ⊗ 1`; scalar restriction supplies its R-linear type.
- Universal injectivity: quantify over every additive commutative R-module L and
  take `Function.Injective` of the right tensor of that exact section map.
  The formula is `(p ⊗ l) ↦ ((p ⊗ 1) ⊗ l)`, with the exact source and target
  tensor order in the node. The explicit universe `max u v w x y` permits every
  larger test universe and every smaller test via the canonical universe lift.
- No faithful-flatness hypothesis occurs, and neither ring map is assumed injective.

Dependency declarations and sources read:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`, recorded
  by the already landed node `def-sc-finitely-presented-module`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`; `Module.Flat` comes from its public imports.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  through `Mathlib.AlgebraicGeometry.ResidueField`; the underlying prime map is
  `PrimeSpectrum.comap`.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`, whose definition is primality and equality
  to `(⊥ : Submodule C M).colon {z}` for some z.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, which is the
  residue field of the stalk. For a ring prime I use the canonical algebraic carrier
  `Ideal.ResidueField` already exposed there, the residue field of its prime
  localization, as used in the existing `FlatCompletionUniversallyInjective` module.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`: `TensorProduct`,
  `TensorProduct.mk`, `LinearMap.rTensor` and its pure-tensor formula.

Proof dependencies with recorded declarations are imported privately:
`Sheaf.RingTheory.UniversalInjectiveCheckStalks`;
`WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness`;
`Mathlib.RingTheory.Flat.Localization`; `Mathlib.RingTheory.FiniteType`;
`Mathlib.RingTheory.Spectrum.Prime.Topology`. Their public imports also supply the
recorded localization and Noetherian-ring definitions. The local Tag 05DG node
`lem-sfb-assassin-cover-universal-section-injection-local` has no recorded Lean
module yet: it is a proof-only prerequisite, no interface is needed to state this
item, and its future import is left to the maintainer. The proof docstring gives
all four steps, including the denominator-clearing argument in the Noetherian fibre.

Node citation issue: `def-weil-pbc-module-finite-type-presentation` defines finite
presentation of sheaves on a ringed space, not ordinary modules. I read its recorded
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation` declarations.
The existing node `def-sc-finitely-presented-module` records exactly the ordinary
module notion needed here. Its id is added to stmt_deps under the permission to
add already landed definition nodes; the original citation and every other field
are preserved. No dependency definition is copied, and no statement correction is
needed: the node and its source unambiguously require ordinary C-modules.

Edge cases checked mathematically before writing:
P = 0 makes the associated-prime condition empty and every tensor map injective;
L = 0 is immediate; C -> D the identity makes the section the unit tensor
isomorphism; R or C the zero ring forces P = 0. If D is the zero ring, the image
condition must still hold, and the stated theorem is not made vacuous by assuming
D nontrivial. A nonfaithful example is R a field, C = R × R, P = R supported on
the first factor, D = R with the first projection: the omitted component has zero
P-fibre and the section remains an isomorphism. No Nontrivial, Noetherian, domain,
or faithful-flatness binder is imposed. Ring, module and test universes are explicit.

Searches for an existing statement (2026-10-24):

- msearch LeanFinder: “A flat algebra map covering every relative associated prime
  makes the section map from a finitely presented flat module to its scalar extension
  universally injective”. Eight hits, including faithful-flatness from surjective
  spectrum and flat-toAlgebra injectivity; none is the relative-assassin theorem.
- msearch Loogle: `Module.FinitePresentation, LinearMap.rTensor, TensorProduct.mk`.
  One hit, `Module.exists_basis_of_basis_baseChange`; it does not state this result.
- msearch LeanSearch: “Finitely presented flat module and a flat algebra map covering
  all associated primes of its residue field fibres give a universally injective
  section map”. Eight hits on faithful-flat descent, projectivity, tensor preservation
  of injectivity, and the flatness criterion; none gives the required theorem.
- msearch grep: `universally.*injective|assassin|annihilatorAssociatedPrimes` under
  Mathlib `RingTheory/Flat`: no matches.
- rg across `lean/WeilConjectures` and `lean/Sheaf` for the item tag, proposed
  declaration name, assassin-cover names and `base.change.universally.flat`: no
  matching declaration. Broader RingTheory searches found related completion and
  stalk-criterion statements; their hypotheses and conclusions differ.
- DAG search for the exact `Module.FinitePresentation` binding found
  `def-sc-finitely-presented-module`, so no definition node was created.

The inherited BLOCKED ending concerned the already reviewed stage-1 split under
Q27. The current node has no lean record, is on the stage-2 queue, and has no
released repair note. The stage-handoff paragraph of brief-stage2 §0 explicitly
permits recording its Lean statement while preserving its accepted split.

Validation: scompile.py compiled both the isolated sandbox module and the module
under its delivery name cleanly, each in 1.4 seconds. No errors or warnings.
No statement dispute or mathematical correction was found.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
