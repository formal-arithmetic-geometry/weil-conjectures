## Worker report

The module `Sheaf.RingTheory.PowerQuotientGradedComparison` states
`Ideal.powerQuotient_graded_comparison`, with one `sorry` and no new definitions.
It uses the existing canonical maps rather than constructing competing maps.
Source read: `literature/stacks-project/algebra.tex`, lines 41256–41291,
Stacks Tag 0H1D, `lemma-formally-etale-lift-infinitesimal`. The node extracts the
associated-graded implication from its quotient-isomorphism premise; its elementary
representative proof explains why this implication itself needs no formal étaleness.
No statement correction and no disputed assertion.

Clause-by-clause correspondence:

- Commutative rings A and C: independent `Type u`, `Type v`, `[CommRing A]`,
  `[CommRing C]`. The map φ is `φ : A →+* C`; the ideals are `I : Ideal A`
  and `J : Ideal C`; ideal preservation is `hI : I ≤ J.comap φ`.
- For positive n, the first conjunct gives a ring map Q equal to the existing
  `powerQuotientMap φ I J hI n`, with the explicit formula
  `Q (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (J ^ n) (φ a)`.
  `1 ≤ n` occurs precisely where the node specifies a positive quotient index.
- The second conjunct gives `G : associatedGraded I →+* associatedGraded J`;
  its type includes additivity, multiplicativity and preservation of 1. Equality
  `G.toAddMonoidHom = associatedGradedMap φ I J hI` specifies the existing
  canonical direct sum map, not an arbitrary ring homomorphism.
- For every `n : ℕ` and every `x : associatedGradedPiece I n`, the equality
  on `DirectSum.of ... n x` says that G takes the degree-n inclusion to the
  degree-n inclusion of `associatedGradedPieceMap φ I J hI n x`. This is the
  degree-preserving property. The existing piece map is the semilinear quotient
  map induced by the restriction of φ to I^n, so its definitional representative
  formula is exactly `[a]_n ↦ [φ a]_n`. Its definition, not a new choice, supplies
  the homogeneous maps mentioned by the node.
- The separate universal quantification over `a : A` and
  `x : associatedGraded I` gives
  `G ((Ideal.Quotient.mk I a) • x) = (Ideal.Quotient.mk J (φ a)) • G x`.
  These are the already published quotient-algebra scalar actions.
- Only the third conjunct assumes `∀ n, 1 ≤ n → Function.Bijective
  (powerQuotientMap φ I J hI n)`. It concludes bijectivity of every
  `associatedGradedPieceMap`, including n=0, and a ring equivalence e equal as
  an additive map to the same canonical graded map. Thus G itself is an
  isomorphism, rather than merely the existence of an unrelated ring isomorphism.
  The equivalence's scalar equality is precisely A/I-linearity after transporting
  the C/J-action along Q_1: every A/I scalar has a representative a, and Q_1
  sends that representative's class to the class of φ a. Together with equality
  to the degree-preserving map this states the graded algebra isomorphism.
- The fourth conjunct quantifies independent rings A', C', their ideals, φ', α,
  γ, the three ideal-preservation hypotheses and `γ.comp φ = φ'.comp α`.
  Its two equalities are the Q_n and G commuting-square laws. Every map uses
  exactly the same `powerQuotientMap`/`associatedGradedMap` constructors with
  its specified source and target ideals. This conjunct has no bijectivity premise.
- The fifth conjunct gives composition for arbitrary `u : A →+* C`,
  `v : C →+* D`, arbitrary ideals K in C and L in D, with `hu`, `hv`.
  The composite's ideal-preservation proof is `hu.trans (Ideal.comap_mono hv)`.
  Since A, C and I are arbitrary outer parameters, this covers every triple
  (R,K) → (S,L) → (T,M) of the node, independently of φ or J.
- The final two conjuncts are Q_n(id)=id and G(id)=id. The graded equality is
  between additive maps, hence equality of the underlying functions of the
  canonical ring maps specified earlier. There is no quotient-isomorphism
  premise on these laws and no formal-étaleness hypothesis anywhere.

Dependency declarations read and used:

- `def-weil-pbc-algebra-hom-quotient`: its Mathlib match is used directly.
  `Mathlib.RingTheory.Ideal.Quotient.Operations` supplies quotient rings and
  `Ideal.quotientMap`, with `Ideal.quotientMap_mk` giving the representative
  formula, and `Ideal.Quotient.algebra` supplies quotient algebra structures.
  `Mathlib.RingTheory.Ideal.Operations` supplies multiplication/powers of ideals.
  `AlgHom` in `Mathlib.Algebra.Algebra.Hom` was read; no extra base algebra is
  imposed on φ, since this node starts with a plain ring homomorphism.
- `def-weil-pbc-associated-graded-ring`: recorded module
  `WeilConjectures.RingTheory.AssociatedGradedRing`, read in full.
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedCommRing`, and `Ideal.associatedGradedAlgebra` supply
  exactly the piece quotients, direct sum, ring, and quotient-scalar action.
- Proof dependency `lem-weil-pbc-associated-graded-ring-structure` has the same
  upstream module, already publicly imported transitively. Its published
  `Ideal.associatedGraded_mul`, `Ideal.associatedGraded_one`,
  `Ideal.associatedGraded_smul`, and
  `Ideal.algebraMap_associatedGraded_injective` give the ring/scalar formulas.
- Proof dependencies `def-weil-pbc-quotient-module` and
  `def-weil-pbc-direct-sum-modules` are Mathlib matches, read at their source:
  `Submodule.Quotient`, `Submodule.mkQ`, `Submodule.mapQ`, `DirectSum`,
  `DirectSum.of`/`DirectSum.lof`, and `DirectSum.map`. Their modules are already
  exposed by the associated-graded module and the following public import.
- Existing canonical helpers in
  `Sheaf.RingTheory.FormallyEtaleAssociatedGraded` are reused by public import:
  `Ideal.powerQuotientMap`, `Ideal.associatedGradedPieceMap`,
  `Ideal.associatedGradedMap`. All three have actual data and are general in φ,
  I, J, and hI, with no formal-étaleness assumption. The same module already
  states `powerQuotientMap_naturality`, `associatedGradedMap_naturality`,
  `powerQuotientMap_comp`, `associatedGradedMap_comp`, `powerQuotientMap_id`,
  and `associatedGradedMap_id`. The new theorem collects the node's full
  statement, including its previously absent general isomorphism criterion;
  it does not replace any existing helper. The module's main formal-étale
  theorem is not used to assert the criterion. Its owning downstream node,
  `lem-sfb-augmented-etale-associated-graded`, already has this item as a proof
  dependency; do not add that node as a DAG dependency of this item. The
  maintainer must skip the reverse proof import into that existing module,
  since this module imports its canonical helpers. No wait or circular proof
  premise is introduced by the present statement.

Edge cases checked before finalization:

- Degree 0 is included in the piece bijectivity and homogeneous formula;
  its surjectivity uses Q_1, never the undefined positive-index assumption Q_0.
  For r>0 the proof uses Q_r and Q_(r+1), both positive.
- I=0 and J=0 leave only degree 0; the criterion specializes to the given ring
  map being bijective. I=top and J=top give zero quotient and graded rings,
  which are allowed by `[CommRing]` without `[Nontrivial]`.
- Mixed unit/zero ideals and zero rings are allowed; no properness, finite
  generation, Noetherianity, injectivity/surjectivity of φ, or J=IC is assumed.
- Finite support comes from the existing DirectSum; zero elements cause no
  need to choose infinitely many nonzero lifts. All universe variables and all
  theorem variables are explicitly bound; `set_option autoImplicit false` is on.
- Identity maps and arbitrary ideal-preserving composable maps occur without
  quotient-isomorphism assumptions. Naturality allows four independent ring
  universes, and composition an independent third ring universe.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`, query “An ideal preserving ring map inducing
  isomorphisms modulo every positive ideal power induces an isomorphism of
  associated graded rings”: eight hits, principally
  `Ideal.powQuotPowSuccEquivMapMkPowSuccPow` and completion equivalences.
  These identify one subquotient or an adic completion, not this comparison.
- `msearch.py ... loogle`, query `"associatedGraded", "map"`: zero hits.
- `msearch.py ... leansearch`, query “Ring homomorphism on associated graded
  rings induced by a map preserving ideals”: eight hits including
  `Ideal.quotientMap`, `DirectSum.liftRingHom`, and graded projections. The
  quotient map is reused through the published helper; no full criterion.
- `msearch.py ... grep`, query
  `associatedGraded|AssociatedGraded|powQuotPowSucc`, subdirectory RingTheory:
  eight hits on ideal-power subquotient equivalences and principal ideals.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` found the existing upstream
  associated-graded ring and the canonical helpers in
  `Sheaf/RingTheory/FormallyEtaleAssociatedGraded.lean`; all were read.
  `grep -rn lem-sfb-power-quotient-graded-comparison lean/WeilConjectures`
  found no attached statement. Name searches in Mathlib, project source, and
  `dag/lean_names_upstream.json` found no declaration named
  `Ideal.powerQuotient_graded_comparison`.
- The example `Sheaf/CategoryTheory/CompactObject.lean` is withdrawn. Its node
  points to `WeilConjectures/CategoryTheory/CompactObject.lean`; that live
  replacement was read for the module conventions.

Validation: the prescribed `scompile.py` compiled the delivered module in module
mode against the live published build. No diagnostics or warnings were printed.

## Second reading by NV

Author's second reading, not an independent reviewer (the dispatcher brief assigns
independent review to the maintainer and prohibits starting other agents).
I reopened the node, the complete theorem, and the existing canonical helper
constructors. The map types and representative definitions match the two rings,
ideals and preserving condition. Q_n is asserted only for positive n; pieces
range over all natural degrees. The ring-map existential is pinned to the
DirectSum.map constructor, its degree formula uses the actual semilinear piece
map, and its scalar equation uses the published quotient algebra instances.
The isomorphism premise is local to its implication, not shared with the square,
composition or identity conjuncts. The ring equivalence has the same canonical
additive map and the transported scalar equation, so there is no arbitrary
isomorphism in place of the canonical comparison. The square retains every
ideal-preservation assumption and exactly the given commutation equality.
Composition and identity use the same helpers, without formal étaleness.
During this reading I parenthesized the degree formula so the scalar clause is
an independent conjunct, and expanded the proof docstring to explain separately
degree zero and positive-degree surjectivity. No mathematical statement changed.
