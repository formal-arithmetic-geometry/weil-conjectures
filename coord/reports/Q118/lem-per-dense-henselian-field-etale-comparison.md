## Worker report

The module `Sheaf.FieldTheory.DenseHenselianEtaleComparison` states
`AlgebraicGeometry.Etale.denseHenselianField_etaleComparison`. Its only theorem
proof is `sorry`. There are no new definitions, dependency repairs, or statement
changes. The current accepted seven-step split is preserved verbatim in the node,
and its argument is recorded step by step in the theorem docstring.

The former worker's ending concerned stage 1. The current assignment is stage 2,
the queue lists stage 2, and the node has no Lean record. The repair note is
resolved, stage 1, and Q53's reconstructed split has passed independent review.
This follows the stage-handoff rule at the start of `coord/brief-stage2.md`;
it neither re-splits the accepted argument nor rebinds a withdrawn theorem.
The Lean statement was freshly written against the current node and APIs.
The `lean_removed` history is preserved as required.

Hypotheses and clauses, in order:

- Fields and inclusion: `(K L : Type u) [Field K] [Field L] [Algebra K L]`.
  `algebraMap K L` is injective because its domain is a field. Writing an
  inclusion as a field algebra allows arbitrary specified embeddings, rather
  than requiring literal subtype inclusions.
- Nontrivial valuations: independent ordered value types `Γ : Type v` and
  `Δ : Type w`, with `LinearOrderedCommGroupWithZero` instances, and
  `[vK : Valued K Γ] [vL : Valued L Δ]`, with
  `[vK.v.IsNontrivial] [vL.v.IsNontrivial]`. `Valued` includes the uniform
  structure and the assertion that its topology is the valuation topology.
  Multiplicative valuations use balls defined by strict upper bounds;
  these are the additive-valuation strict lower-bound balls in the node.
- Henselian valuation rings: `[HenselianLocalRing vK.v.valuationSubring]`
  and `[HenselianLocalRing vL.v.valuationSubring]`. The actual valuation
  subrings are used; henselianity is not imposed on the fields themselves,
  where it would be automatic and would lose the intended hypothesis.
- The topology on K is induced from L: `h_induced : Topology.IsInducing
  (algebraMap K L)`. This means equality with the induced topology, rather
  than merely continuity.
- Density: `h_dense : DenseRange (algebraMap K L)`. Valuation balls form
  a neighbourhood basis, so this is precisely the nonempty-ball condition.
- Arbitrary compatible separable closures: `Ks : Type s`, `Ls : Type t`,
  their field structures, `[Algebra K Ks] [IsSepClosure K Ks]` and
  `[Algebra L Ls] [IsSepClosure L Ls]`. The inclusion of closures is
  `[Algebra Ks Ls]`, with `[Algebra K Ls]` and both
  `[IsScalarTower K Ks Ls] [IsScalarTower K L Ls]` expressing compatibility.
  These are exactly the commutative-square data, with independent closure
  universes. There is no algebraic or separability restriction on L/K.
- Topological Galois restriction isomorphism: the first conjunct supplies
  `e : Gal(Ls/L) ≃ₜ* Gal(Ks/K)` using Mathlib's Krull topologies.
  Its formula `algebraMap Ks Ls (e σ x) = σ (algebraMap Ks Ls x)` for
  every `σ` and `x` specifies restriction, rather than an arbitrary group
  isomorphism. Injectivity of the closure embedding uniquely determines
  the image of every automorphism. The homeomorphism and multiplicative
  equivalence components give both directions of the required topological
  group isomorphism. This direct characterization avoids introducing a
  second definition of a restriction map or choosing uncharacterized data.
- Every torsion abelian small-etale sheaf: the second conjunct quantifies
  `F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}`
  and assumes the recorded predicate `F.IsTorsion`. This predicate is local
  finite additive order, not a uniform exponent or torsion of every entire
  section group.
- Every degree q >= 0: `∀ q : ℕ`. Its conclusion is `Function.Bijective
  (cohomologyMap (Spec.map (CommRingCat.ofHom (algebraMap K L))) F q)`.
  `cohomologyMap` is the existing additive homomorphism from `Sheaf.H F q`
  to the cohomology of `(upperStar ...).obj F` over Spec L. Bijectivity of
  this homomorphism says exactly that the canonical pullback is an
  isomorphism. `def-weil-pbc-etale-cohomology`'s Lean note explicitly
  permits the library's `Sheaf.H` encoding; its comparison with cohomology
  of derived global sections is the shared stage-3 bridge. Both that
  recorded module and the actual canonical-map module are public imports.
- Naturality: the final conjunct quantifies torsion `F`, `G`, an arbitrary
  `φ : F ⟶ G`, `q : ℕ` and `x : Sheaf.H F q`. It equates pullback after
  `Sheaf.H.map φ q` with `Sheaf.H.map ((upperStar ...).map φ) q` after
  pullback. This is the canonical commuting square, with the source and
  target sheaf maps in the right order. It renders the node's last clause
  explicitly; it does not replace pullback with the existence of an
  unrelated isomorphism.
- No extra completeness, discrete valuation, rank, residue characteristic,
  perfectness, or finite-generation assumption occurs anywhere in the
  signature. No independent topology is supplied for the Galois groups.

Recorded statement dependencies used, after opening their source and reading
the relevant signatures and docstrings:

- `def-trf-valuation-ring`: Mathlib's `ValuationRing` and its fraction-field
  characterization `ValuationRing.TFAE`, in
  `Mathlib.RingTheory.Valuation.ValuationRing`. The concrete valuation
  rings in the signature are the existing `Valuation.valuationSubring`,
  in `Mathlib.RingTheory.Valuation.ValuationSubring`; they have the
  valuation-ring instances without any additional assumption.
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`, exposing Mathlib's
  `HenselianLocalRing` (and `HenselianRing`). The node's alternative
  idempotent formulation is exactly the equivalence explained by its
  existing Lean record. No replacement notion was defined.
- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosure` (separably closed top field and separable algebraic
  extension), not merely `IsSepClosed`.
- `def-weil-pbc-etale-sheaves`:
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; its mixed Lean record
  names `CategoryTheory.Sheaf.IsTorsion`, defined in the publicly imported
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, obtained through
  the public small-etale imports; the field embedding is passed through
  `CommRingCat.ofHom`.
- `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, left Kan extension followed by
  sheafification, exposed by the canonical-map module.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.cohomology` and
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`. As explained above,
  the canonical pullback API is
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`,
  `AlgebraicGeometry.Etale.cohomologyMap`, with the existing naturality
  theorem `cohomologyMap_map`.

Proof-only imports expose the recorded finite-Galois envelope, Krull
finite-limit, profinite-group, compact-Hausdorff, algebraic closure,
abelian-sheaf/Galois-module and K-injective tools:
`Mathlib.FieldTheory.Galois.Profinite`,
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`Mathlib.Topology.Homeomorph.Lemmas`,
`Sheaf.AlgebraicGeometry.AbelianSheavesGModules`,
`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`, and
`Sheaf.AlgebraicGeometry.KInjectiveResolutions`.
The derivative/separability Mathlib leaf is exposed by `IsSepClosed`.
The remaining proof-only nodes have no usable recorded modules yet
(`lem-per-henselian-finite-extension-topology`,
`lem-per-henselian-krasner-neighbourhood`,
`lem-per-galois-restriction-image`,
`lem-per-henselian-simple-root-stability`,
`lem-per-field-pullback-galois-action`). They are not required to type the
statement and were not silently replaced by new hypotheses or local lemmas.
Their later proof imports are for the maintainer when they are stated.

Edge cases checked before writing:
identity inclusion and compatible identity closures; arbitrary closure
embeddings with the two towers; q = 0; zero sheaf; zero morphisms; torsion
sheaves with no uniform exponent; purely inseparable parts of L/K;
non-discrete and arbitrary-rank valuations; equal and mixed characteristic.
The statement does not exclude any of these. Trivial valuations are excluded
because the node explicitly excludes them. The two value groups and the two
closure universes are independent, and the site/coefficient convention is
exactly Scheme.{u} with AddCommGrpCat.{u+1} from the recorded interfaces.

Searches, performed before writing:

- `msearch.py ... leanfinder "Dense extensions of henselian valued fields
  induce isomorphisms of absolute Galois groups and etale cohomology"`:
  eight hits, including `galLiftEquiv`, `galRestrict`,
  `Field.absoluteGaloisGroup`, and `InfiniteGalois.algEquivToLimit`.
  Reading `IntegralRestrict.lean` shows the first two restrict/lift
  automorphisms between integral closures and fraction fields, not dense
  henselian field comparison. `absoluteGaloisGroup` is just a group
  definition, and the finite-limit theorem is infrastructure, not this
  comparison.
- `msearch.py ... loogle '"absoluteGaloisGroup", "Valued"'`: no hits.
- `msearch.py ... grep 'dense.*henselian|henselian.*dense|galRestrict'
  FieldTheory`: no hits.
- `msearch.py ... leansearch "A dense inclusion of henselian valued fields
  preserves absolute Galois groups and all torsion etale cohomology"`:
  eight hits on absolute Galois groups, finite-limit projections,
  dense embeddings and valuation-subring inclusions; no comparison.
- `rg` of all Mathlib for dense/henselian combinations: no hits.
  Searches of `lean/WeilConjectures` and `lean/Sheaf` for
  dense-henselian combinations, the intended declaration and the item id
  found no matching statement. Broad dense/henselian searches found only
  unrelated condensed rigidity and section-density modules.
  The upstream declaration-name inventory has no attachment for this item.

Source check: read the local ILO PDF, PDF p.380 = printed p.374, XX 4.4.
It states exactly the dense-henselian-field comparison using compatible
separable closures and Krasner's lemma. No complete/discrete/rank-one
specialization was introduced. No `STATEMENT-DISPUTED` fault was found.

Validation: `scompile.py Q118 lem-per-dense-henselian-field-etale-comparison
<module>` compiled both sandbox and library module successfully (23.2 s and
5.8 s), with no errors or non-sorry warnings. The module begins with
`module`, uses public statement imports and private proof imports, and sets
`autoImplicit false`; all types and universes are explicit.

## Second reading by Q118

A separate self-review pass reopened the current node and the completed module,
since the dispatcher explicitly forbids starting another agent and the
maintainer supplies the independent delivery review. Checked the actual
signature, not only the name: the two valuations and both henselian valuation
rings occur explicitly; induced topology and density are separate hypotheses;
closure compatibility has both towers; the Galois equivalence is pinned down
by its value on every element of Ks; canonical pullback is used in every
nonnegative degree; torsion has its local meaning; the last conjunct spells
out the correct naturality square. There is no assumption on L/K other than
the dense embedding. The proof matches all seven steps of the accepted split.
No mismatch or correction was found. No new or dependency nodes are delivered.
