## Worker report

Item: `lem-sfb-lattice-cubical-multiplication-roof`, group Q36, stage 2.
Module: `Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof`.
The sole theorem proof is `sorry`; every definition has actual data. The theorem
returns the three maps together with their complete coordinate characterizations;
no definition chooses data from an unproved mere-existence assertion.

The current blueprint direct-images proof, paragraph (3), was read in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
As the node explicitly says, its structural lattice calculation is the agent-written
expansion, rather than a formula asserted in that blueprint paragraph. The full six-step
DAG proof is rendered in the main theorem's docstring.

Hypotheses and objects, clause by clause:

- A commutative condensed ring is `R : CategoryTheory.CondensedBar.Ring.{u}`.
  This is the existing bundled `CommMon` of abelian sheaves on the coherent profinite
  site. Its underlying `R.toMon : Profinite.CondensedRing` is the ring used by the
  recorded Koszul and pairing interfaces. Bundling commutativity adds no restriction.
  All universes are explicitly declared; localization is in universe `u + 2`.
- `r : ℕ` includes zero. Modules and discrete lattice actions are the recorded
  `DiscreteLattice.Modules R.toMon` and `DiscreteLattice.Equivariant R.toMon r`.
  `CubicalEvaluation.DiscreteComparison R r` is the recorded normalized equivalence
  from generalized continuous-section actions to discrete lattice actions.
  `J.underlying` and `J.action` retain the underlying modules and constant actions;
  no abstract replacement of the coefficient action is assumed.
- `K : KoszulModel R.toMon r` is the dependency's finite ordered-subset Koszul complex.
  `B : DerivedCup.Algebra R.toMon r`, `[IsCommMonObj B.X]` and `hflat : exactFunctor
  ... (tensorLeft B.X.V)` express exactly the commutative equivariant algebra and
  flatness hypothesis. `P : FlatTwisted.Pairing K B` is the specified star and unit,
  with its complete coefficient matrix and homogeneous unit laws.
- `C : CubicalEvaluation.CubicalModel R r` supplies the actual cubical coproduct,
  boundary, translation, augmentation and integral contraction. `lattice` is its
  image under the recorded normalized equivalence, and `cell` transports its actual
  inclusions by `J.underlying.inv`, including zero in the wrong cardinality.
- The existential `F : Roof (koszul ...) (lattice ...) (algebra ...)` supplies the
  three chain maps simultaneously with every defining coordinate formula and claimed
  identity. `Roof` itself is only a bundle of three maps, with no identity assumption.
  The first conjunct fixes its augmentation on every vertex. The second is exactly
  the integral diagonal extended R-linearly: `partitionSign`, `directionSum`, `I.powerset`
  and second part `I \ A`. `cellTensor` uses the signed total inclusion.
- The third conjunct fixes the B[0] specialization of E_B on every Koszul/cell
  coordinate: `cSign p` times `T^v` when A=I, zero otherwise. The output is concentrated
  in zero, so all other total-degree components vanish. The construction described in
  the proof transports the recorded augmentation/evaluation theorem through J and
  identifies its single-input total with K_B. The formulas determine every component,
  so this is the same E_B; an arbitrary scalar normalization cannot satisfy them.
- `star` and `unit` apply the existing trivial-action cochain functor to `P.star`
  and `P.unit`, with its canonical strong tensor comparisons. `algebra`,
  `DerivedCup.singleMultiplication`, and `eta` use B's original multiplication
  and unit.
- `Roof.comparison` is `1 tensor diagonal` followed by Mathlib's `tensorμ`, which is the
  signed middle interchange with its canonical associators. Thus its middle-degree
  sign is `(-1)^(q*(-p)) = (-1)^(pq)` as required.
- `F.Identities` is a transparent predicate on the ambient monoidal category. Its
  first three clauses give the left, right and double counit equations. The fourth is
  exactly `F.f star = F.comparison ≫ F.g mul`, the required chain-map equality.
  `Roof.f` is E_B(t star tensor 1); `Roof.g` is m_B(E_B tensor E_B).
  The fifth is the actual common denominator `F.comparison ≫ F.b = F.a`.
  The sixth is the unit equality with eta_B and epsilon, using the canonical unitor.
  These generic definitions are specialized to the actual signed cochain tensor;
  they are abbreviations of the displayed compositions, not extra hypotheses.
- The next conclusion is the sign identity for all `p q : ℕ`. `supported` and `value`
  render the two numerator coefficient equations as internal-module morphisms:
  zero unless A and C partition I, otherwise c_(p+q) epsilon(A,C) times multiplication
  after T^v and T^(v+u_A). Naturality in profinite restriction is built into these
  internal maps; no global-section generation assumption is used.
- `QuasiIso F.a` and `QuasiIso F.b` are the actual denominators. `F.Localized Q star mul`
  supplies isomorphisms whose forward maps are exactly Q of those denominators and
  equates their inverse-denominator/numerator composites in the ordinary derived
  category. Localization uses the explicit `u + 2` size convention.
- The next quantified clauses state K-flatness of X,Z,Y via total tensor with every
  acyclic complex and invertibility of the canonical Q tensor comparisons on these
  representatives, so the tensors are ordinary K-flat derived tensor representatives.
- The rank-zero clause explicitly gives ordinary multiplication and B's original unit
  on the unique empty-subset coordinate. The general diagonal formula at r=0 has only
  the empty partition and gives 1 tensor 1. The final two clauses state both rank-one
  mixed products and the two rank-one diagonal terms with translation by u_i.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module morphisms.
- `Sheaf.CategoryTheory.CondensedActionModule`: the original internal module/action
  category, forgetful and trivial functors (through recorded dependencies).
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: ordinary derived
  restriction/invariants and exactness detection (through public dependencies).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `Modules`, `Group`,
  `Equivariant`, `Subsets`, `KoszulModel`, `generator`.
- `Sheaf.CategoryTheory.LatticeFlatTwistedChainPairing`: `FlatTwisted.Pairing`,
  `FlatTwisted.trivialKoszul`, `lattice_flat_twisted_chain_pairing`.
- `Sheaf.CategoryTheory.LatticeCubicalAugmentationEvaluation`: `CubicalModel`,
  `DiscreteComparison`, `cell`, `cSign`, `Evaluation`, and
  `lattice_cubical_augmentation_evaluation` (all under `CubicalEvaluation`).
- `Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal`:
  `IntegralLatticeCubical.directionSum`, `partitionSign`, `diagonal`.
- The pairing dependency publicly supplies `DerivedCup.Algebra`, `trivial`,
  `singleMultiplication`, and the ordinary cochain/derived tensor instances.

Searches made before writing:

- msearch LeanFinder, query "Cubical lattice diagonal signed Koszul product evaluation
  multiplication roofs": eight generic complex-sign lemmas, no matching theorem.
- msearch Loogle, query `"HomologicalComplex.tensorHom", "DerivedCategory.Q"`:
  zero hits.
- msearch grep, query `cubical.*diagonal|koszul.*evaluation|multiplication.*roof`:
  two unrelated Mathlib hits (ZetaValues and Finset.SMulAntidiagonal).
- msearch LeanSearch, query "The cubical lattice diagonal compares twisted Koszul
  multiplication evaluation roofs in the derived category": eight generic diagonal
  constructions, no cubical/Koszul evaluation identity.
- Direct rg of the same concepts in `lean/WeilConjectures`, `lean/Sheaf`, and the node
  id in upstream Lean/name records: no existing theorem of this statement. Existing
  cubical diagonal, augmentation/evaluation and Koszul pairing were found and reused.
  The triangulated cup-comparison consumer describes using this item in its proof;
  it does not supply the chain-map/common-denominator theorem needed here.

Edge cases checked before writing: r=0 has the empty direction set, r=1 has exactly
the two partitions displayed in the node; empty/nonpartitioning subsets give zero;
the evaluation signs are c_0=1, c_1=-1, c_2=-1, so the (1,1) identity has the required
minus sign. Degrees outside the finite Koszul/cubical support are zero. No Nontrivial,
characteristic, invertibility or division assumption occurs; the zero ring and zero
algebra are retained. A separate normalization checks the actual algebra unit, rather
than an arbitrary map out of the tensor unit.

No statement correction, new node, or dependency-node repair is needed.

## Second reading by Q36

The dispatcher explicitly prohibits starting other agents. This section records a
separate self-reading of the node and module, not an independent worker review;
the maintainer supplies the independent review of the delivery.

The rereading checked the actual common denominator a=b delta and the order of
composition in Q(a)^(-1)Q(f), and ensured the unit is B's original unit. It found that
the first draft only mentioned low-rank behavior in proof prose, so explicit rank-zero
and rank-one clauses were added. It also added the canonical Q tensor comparison and
both internal numerator coefficient formulas. The generic `Roof.Identities` and
`Roof.Localized` were unfolded against the node, giving exactly its compositions.
Their abstraction avoids repeated elaboration of concrete tensor objects and adds
no hypothesis. All three returned maps are simultaneously fixed by complete coordinate
formulas. The final theorem has one `sorry`, and every other declaration has real data.
