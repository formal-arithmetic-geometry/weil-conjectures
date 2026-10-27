## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RestrictedInducedInfinitesimalInvariants`
states `AlgebraicGeometry.restricted_induced_infinitesimal_invariants`, with its whole
proof `sorry`. No definitions, other postponed theorems, new nodes, dependency repairs,
or changes to the mathematical node statement are introduced. Only its `lean` field changes.

The source was opened online at https://www.imsc.res.in/~knr/vdk/mathieu.pdf:
Mathieu, Lemma 2.1, printed pp.153--154, and Lemma 2.3, printed p.155.
The latter asserts the infinitesimal invariant line for restricted dominant weights.
The node uses the equivalent positive-Borel convention and includes semisimple products
and the trivial group. The module docstring records all three accepted DAG proof steps.

Hypotheses, in their order in the node:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Prime characteristic p > 0 | `(p : ℕ) [Fact p.Prime] [CharP F p]`; prime implies positive |
| S is a group scheme | `S : Grp (Over (Spec (.of F)))` |
| Smooth, connected, affine, finite type, no nontrivial smooth connected solvable normal subgroup | `hS : IsSemisimpleGroupScheme S.X`, whose full definition was read in `Semisimple.lean`; solvability is termination of the scheme-theoretic commutator series |
| Simply connected | `hsc`, over every semisimple `S'` and monoid homomorphism `f`, with `Surjective f.left`, finite scheme-theoretic kernel and commutation with every `S'(A)` after every F-algebra extension, concluding `IsIso f` |
| Split maximal torus T and Borel B containing it | `iT`, `iB`, `j`, `hj`, `hT`, `hsplit`, `hB`, exactly the recorded Borel-pair interface |
| Unipotent radical U | `iU`, `hU`: closed, normal, smooth, connected, unipotent, and maximal among such subgroups by factorization; not just a chosen unipotent subgroup |
| Projection πT with kernel U and B = U ⋊ T | `πT`, `hπT`, `hker`, `hsd`, copied in meaning from the Borel-pair conclusion |
| Character/cocharacter lattices, roots, coroot pairing, positive roots, simple base | Actual additive group-scheme Hom groups in `Φ`, `P`, `b`; `hroot` identifies roots with characters; `hpair` pins the integer pairing to composition/powers; `aS`, `aB`, `hconjS`, `hconjB` pin the tangent actions to conjugation; `hweights` gives exactly the nonzero tangent weights and `hpos` the Borel positives |
| Q = S/B and its torsor map | `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hπf`, `hπs`, `hπi`, `hπt` specify precisely the proper finite-type faithfully flat right B-torsor from the recorded quotient theorem |
| Longest Weyl element w₀ | `act`, `hact` give the canonical normalizer-quotient action of `RankOneRoots.Weyl iT`; `w₀`, `hw₀` say it takes the positive roots onto their negatives. This characterization, rather than an independently chosen involution, identifies the longest element of `rho_regular_weyl_orbit` |
| λ p-restricted and dominant | `lam` in the actual additive character group; `hlam` is `0 ≤ P.toLinearMap lam (P.coroot α)` and `< (p : ℤ)` for every `α ∈ b.support` |
| M_μ = L_{-μ ∘ πT}, and V(λ) = Γ(Q,M_{-w₀λ}) | `hχ : χ = πT ≫ (act w₀).inv ≫ lam.toMul` makes `χ = w₀λ ∘ πT`. Thus `L : AssociatedCharacterLineBundle.Presentation S B iB Q π χ` has sheaf `L.L = L_χ = M_{-w₀λ}`. The theorem concerns its actual `AssociatedCharacterLineBundle.sections Q L.L`, not an abstract vector space |
| Semi-invariant section realization | `ψ`, `hψ`, and the concluded linear equivalence `e` identify sections with `RhoSection.sectionModule S B iB ψ 1`. Since ψ = χ⁻¹ and sectionModule uses positive right semi-invariance, this is exactly E(χ). The equation for every σ pins `e` to the existing `pullbackCoordinate` |
| Left translation (g f)(s) = f(g⁻¹s) | Concluded finite basis `d` and rational `r`, with `IsMonHom r`; the equation for every algebra A, points s,g, and basis column k is precisely `HasRationalLeftTranslation`'s coordinate identity, transported along `e` and `d`. It determines the algebraic action, including on nonreduced A |
| Differentiated action of Lie(U) | `r.differential (GrpObj.differential (iU ≫ iB).hom.hom x)`, acting by `mulVec` on the coordinates `d.symm w`. Both differentials are existing canonical constructions |

Conclusions, clause by clause:

* Finite-dimensional V: `Module.Finite F (AssociatedCharacterLineBundle.sections Q L.L)`.
  The basis in the action description is a coordinate witness of this finite module,
  not an additional hypothesis or substitute for the actual sections.
* A nonzero highest vector: `∃ v : AssociatedCharacterLineBundle.sections Q L.L, v ≠ 0 ∧ ...`.
* Equality of infinitesimal invariants with Fv: for every section `w`, annihilation by
  the displayed differential for **every** `x : GrpObj.Lie U.X` is equivalent to
  `w ∈ Submodule.span F {v}`. A singleton span is precisely Fv; `v ≠ 0` makes it a line.
* U fixes v: the matrix action on the scalar-extended coordinates of v equals those
  coordinates for every F-algebra A and every `a : Spec A → U`.
* T has character λ on the line: for every F-algebra A and every `t : Spec A → T`,
  the same matrix action equals `RhoSection.characterValue (t ≫ lam.toMul.hom.hom)`
  times the coordinates. This is a character identity, not its differential.
* N = number of positive roots is an explanatory quantity not used in the assertion;
  the finite root set is already retained in Φ and no condition involving N is added.

Dependency declarations used, with sources read:

* Mathlib `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`); the algebraic-closure dependency's
  `AlgebraicClosure`/`IsAlgClosure` record supplies this same algebraically closed notion.
* `CategoryTheory.GrpObj`, `Grp`, `IsMonHom` in `Mathlib.CategoryTheory.Monoidal.Grp`,
  with the recorded scheme specialization in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: kernels, closed/normal subgroups,
  finiteness and scheme homomorphisms. The group-scheme definition is reused.
* `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive` in
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`: the exact
  Borel-pair, quotient, radical, complement and root-data interfaces.
* `AlgebraicGeometry.exists_homogeneousLineBundle_sections` in
  `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`, including its
  recorded definitions `AssociatedCharacterLineBundle.Presentation`, `sections`,
  `pullbackCoordinate`, and `RhoSection.sectionModule`, `evaluate`, `characterValue`.
  Their full signatures, normalization and all-algebra conventions were read.
* `AlgebraicGeometry.rho_regular_weyl_orbit` in
  `Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit`, with its actual
  `RankOneRoots.Weyl` quotient and character action. All root signs match its hpos/hw₀.
* `GeneralLinearGroup.RationalHom`, `.points` and `.differential` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`, and
  `GrpObj.differential`: the existing finite-dimensional rational-action and Lie APIs.
* The currently recorded proof dependency
  `AlgebraicGeometry.BorelDistributions.borel_simple_root_distribution_calculus`
  (`Sheaf.AlgebraicGeometry.GroupScheme.BorelSimpleRootDistributionCalculus`) is
  imported without `public`. The other two proof-only inputs
  `lem-sfb-induced-dual-lowest-distribution-generator` and
  `lem-sfb-induced-module-primitive-line` have no recorded modules, so none is invented
  or imported for them. Their argument is retained in the proof docstring.

Edge cases checked: S = 1 has Φ empty, empty simple support, Weyl group trivial,
λ = 0 and V = F. There is no positive-rank, nonempty-root or nonzero-weight premise.
The vector conclusion excludes V = 0 by asserting nonvanishing, rather than assuming it.
Weights with simple pairing 0 and p−1 are included; pairing p is excluded as in the node.
Characteristic 2 is included, with no division by 2 or factorial in the statement.
Semisimple products have no irreducibility/simple-root-system hypothesis. All test
algebras, groups and the base field use the same universe u; the actual finite section
module is handled by a basis indexed in u. Nonreduced test algebras are included.

Searches actually run through `msearch.py NX <item>` (also in `searches.jsonl`):

* LeanFinder: “A restricted dominant induced representation of a semisimple group
  has one dimensional invariants under the Lie algebra of the unipotent radical”:
  8 hits, including `RootPairing.GeckConstruction.instIsIrreducible`,
  `FDRep.simple_iff_end_is_rank_one`, and ordinary Lie nilpotent/solvable weight lemmas;
  none concerns the actual restricted induced group-scheme module or this assertion.
* Loogle: `"LieModule", "invariant"`: only `LieModule.traceForm_lieInvariant`;
  its displayed type is about trace forms, so not a match.
* LeanSearch: “Infinitesimal unipotent invariants of restricted dominant induced
  algebraic group modules form a highest weight line”: 8 hits: ordinary
  `Representation.toInvariants`, `Representation.invariants`,
  `Representation.le_comap_invariants`, `Rep.toInvariants`,
  `LieModule.zero_genWeightSpace_eq_top_of_nilpotent'`, `LieModule.genWeightSpace`,
  `LieModule.coe_genWeightSpace_of_top`, `Representation.invtSubmodule.coe_top`.
  The returned types describe abstract group invariants/generalized Lie weights,
  not restricted dual Weyl modules; no exact statement.
* Grep via msearch: `restrictedEnvelop|restricted.envelop|DualWeyl|WeylModule|infinitesimal.*invariant`:
  no Mathlib hits.
* Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the item id, theorem name, restricted induced
  modules, and infinitesimal invariants found no existing declaration of this result.
  Searches for the component notions located the reused RhoSection,
  AssociatedCharacterLineBundle, root-data and RationalHom APIs; no notion was copied.

Validation: `scompile.py` compiled the file both under its sandbox module name and
its actual library module name, each in 2.7 seconds, with no errors or warnings.
The first compile exposed Lean's reserved `λ` token as a binder; it was renamed `lam`.
No mathematical node fault or disputed assertion was found.

## Second reading by NX

Author's second reading, with the node JSON and completed Lean signature open;
the dispatcher prohibits additional agents, so independent review belongs to the
maintainer. I rechecked each row and conclusion above against both files.
The actual sections are retained throughout the finite-dimensional, nonzero-vector
and span conclusions. The homogeneous character is χ = w₀λ, whereas the
positive-right-semi-invariance character is ψ = χ⁻¹; these opposite conventions
are explicitly tied by hχ/hψ, avoiding the wrong induced module. The Weyl action
uses `(act w₀).inv` exactly as the recorded character action does.
The Lie expression differentiates the U inclusion and the same rational action
specified by left translation. Group fixity and torus weight are separate
all-algebra assertions, so no unjustified equivalence between group invariance
and Lie invariance is assumed. hU includes radical maximality, hsc includes the
full finite central-kernel condition, and hlam includes both inequalities.
No hypothesis excludes the trivial-group or characteristic-2 cases. No additional
mathematical mismatch was found; only the reserved binder spelling needed repair.
