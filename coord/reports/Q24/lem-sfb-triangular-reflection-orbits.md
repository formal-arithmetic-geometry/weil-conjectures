## Worker report

The delivery states `AlgebraicGeometry.TriangularReflection.triangular_reflection_orbits`
in `Sheaf.AlgebraicGeometry.GroupScheme.TriangularReflectionOrbits`. Its only proof is `sorry`.
The accompanying definition node packages the exact hypotheses as `TriangularReflection.Data`.
Every datum and canonical set/subgroup construction has real data. No existing node statement,
proof, proof dependency, status, or source is changed. The item's statement dependencies gain
only the new definition node.

Read: AGENTS.md, SETUP.md, GOAL.md, coord/STATE.md, roles/worker.md,
coord/brief-stage2.md in full, stages/2-statements.md, tools/README.md,
coord/delivery-errors.md H, and the compact-object example and its node. The example
Sheaf module is now withdrawn; its node points to the upstream definition. Read the item's
complete statement and ten proof steps, all original statement dependencies and their Lean
records/mathlib matches. There is no released repair note for this item.

Source checked directly: Milne, Algebraic Groups (2017), PDF page 506, printed page 494,
Theorem 23.31 and Remark 23.33. Milne's theorem assumes rank-one reductive subgroups;
this item is the explicit intermediate assertion proved from the stronger triangular-coordinate
hypotheses, not a restatement of Milne's reductivity conclusion. The node's ten-step agent proof
is reproduced in the theorem docstring. Read the current blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The long supporting
alteration/moduli/PGL/Steinberg chain is the inherited `blueprint.from.place`; the ancestor
command returns None. This supporting lemma is not the blueprint unit's own statement.

Hypotheses, matched against the original node:

| Node hypothesis | Lean rendering |
| --- | --- |
| F algebraically closed field, unrestricted characteristic | `{F : Type u} [Field F] [IsAlgClosed F]` in the theorem |
| Affine finite-type group scheme G | `d.G : Grp (Over (Spec (.of F)))`, `Data.algebraic : SolvableGroupStructure.IsAlgebraic G` |
| G smooth and connected | `Data.smooth`, `Data.connected` |
| T a closed split maximal torus | `iT`, `maximal : ReductiveTorusCentralizer.IsMaximalTorus iT`, `split : ∃ r, Nonempty (T ≅ MultiplicativeType.splitTorus F r)` |
| X actual character group and Y actual cocharacters | Existing `TrivialTorusCoherent.Character T` and `RankOneRoots.Cocharacter T`; these are additive group-scheme Hom into Gm and group-scheme Hom from Gm |
| Pairing fixed by chi composed with eta | `pairing` and `composition`: equality to the actual integer power of the identity Gm morphism |
| D finite, nonempty, nonzero and Z-linearly independent | `D : Finset (Character T)`, `nonempty`, `nonzero`, `independent` |
| U,V closed smooth connected unipotent, normalized by T | `iU`, `iV`, `closedU`, `closedV`, `smoothU`, `smoothV`, `connectedU`, `connectedV`, `unipotentU`, `unipotentV`, `normalizedU`, `normalizedV` |
| Normalization is conjugation, not an unspecified action | `adjointAction`, `adjointFormula` pin its morphism to `RankOneRoots.adjointMap iT`; stability is the existing `TorusCharacterTangent.IsStable` |
| Multiplication V x T x U open immersion | `bigCell` is `IsOpenImmersion` of the displayed product of the three projection/inclusion morphisms |
| lambda of common positive height n | `lam`, `n : ℤ`, `positive`, `height` |
| Z_G(lambda)=T and contraction groups U,V | `centralizer`, `contraction`, `oppositeContraction` equate existing functors with image subgroups on every `CommAlgCat F` |
| Negative lambda | Precompose lambda with the actual inversion homomorphism of Gm in `oppositeContraction`; no commutativity assumption on G is added |
| Ua subset U, Va subset V, Ga parametrizations | `Ua`, `Va`, `u`, `v`, `closedUa`, `closedVa`, `parameterU`, `parameterV` |
| T-normalization and alpha/-alpha parameter scaling | `normalizedUa`, `normalizedVa`, `scalingU`, `scalingV`; the latter use actual polynomial parameter points and evaluated Laurent coordinates over every algebra |
| These groups generate U,V as closed subgroups | `generateU`, `generateV`, with the smallest-closed-subgroup universal property `generates` |
| n_alpha in the scalar-extension normalizer | `representative`, `normalizes : representative alpha ∈ RankOneRoots.normalizer iT` |
| n_alpha maps Ua onto Va | `conjugationSimple`, equality of subgroup functors on every algebra |
| Its actual action on X | `torusAction` and `conjugationT` specify conjugation on T; `reflectionAction` identifies the character action with precomposition by its inverse |
| Reflection formula and coroot pairing 2 | `reflection`, `coroot`, `reflectionFormula`, `corootTwo` |
| Every nonnegative eta extends to multiplicative A1 action on U | `monoidExtensions`; `monoidExtension` gives a scheme morphism, its restriction to conjugation, its unit law at scalar 1 and its multiplication law on every algebra |
| eta_alpha zero on alpha, common positive m_alpha on all other beta | `eta`, `m`, `positiveM`, `zeroHeight`, `otherHeight` |
| Evaluation at zero is a homomorphism p_alpha | `action`, `extendsEta`, `projection : U ⟶ Ua alpha` in group schemes, `evaluationZero`; the `1` in the additive group is its zero section |
| p_alpha restricts to identity | `retract` |
| Smooth connected kernel K_alpha | `K`, `kernelInclusion`, `closedK`, `smoothK`, `connectedK`, `kernel : IsPullback ...` |
| U = Ua semidirect K | `semidirect`, isomorphism of underlying schemes by the specified multiplication; `kernel` ensures the kernel is normal, so this is precisely the split semidirect decomposition |
| C_U(eta_alpha)=Ua | `fixedSubgroup`, pulling the existing G-centralizer condition back along the U inclusion, on all algebras |
| n_alpha K_alpha n_alpha^-1=K_alpha | `kernelNormalized`, equality of subgroup functors |

All auxiliary choices are specified: the pairing by composition, the torus automorphism by
its inclusion into G, the character automorphism by precomposition, and each A1 action by its
restriction on Gm. These are unique canonical data, not new substantive hypotheses.
Closed subgroup schemes of the affine finite-type G are themselves affine finite type; this
also applies successively to Ua, Va and K. Thus no separate finiteness assumptions are needed
for these subgroups. The definition node explicitly documents every component and construction.

Conclusions, matched clause by clause:

| Node conclusion | Lean rendering |
| --- | --- |
| W generated by the simple reflections, R=WD | `Data.weyl` is `Subgroup.closure (Set.range reflection)`; `Data.roots` is the orbit set of actual simple characters |
| W finite and R finite | `Finite d.weyl ∧ d.roots.Finite` |
| Reduced crystallographic root system on its rational span | Existential `P : RootPairing d.roots ℚ d.rootSpace (Module.Dual ℚ d.rootSpace)` with `IsRootSystem`, `IsReduced`, `IsCrystallographic`; its perfect pairing is explicitly ordinary dual evaluation and its roots are exactly `1 ⊗ rho` |
| D simple base | `b : P.Base` and `rho ∈ b.support ↔ rho.val ∈ d.D` |
| Integral D expansions of a single sign | Explicit `∃ c : d.D → ℤ`, finite sum equal to rho in the actual character group, and all coefficients nonnegative or all nonpositive |
| No full-span assumption on X tensor Q | `rootSpace` is only `Submodule.span ℚ (1 ⊗ R)` inside `ℚ ⊗[ℤ] X`; no equality to the ambient module is asserted |
| Every word in n_beta and their inverses is covered | `Data.words` is the subgroup generated by paired `(representative,reflection)` in `G(F) × Aut_Z(X)` |
| Conjugate depends only on rho, including choice of alpha | For every `h k : d.words` and `alpha beta : d.D` with identical resulting character, equality of the two `conjugatePoints` functors on every algebra |
| Root subgroup lies in U/V according to sign | Nonzero lambda height for each word-conjugated simple root and the two sign-conditioned subset assertions into `pointImage iU`/`pointImage iV` |
| Existence of a word with w0 D=-D | Existential `h : d.words` with equality of the two image sets |
| That same word exchanges U and V in both directions | Both final `conjugatePoints` equalities, on every algebra, using the same `h.val.1` |

The notation U_rho in the prose denotes the well-defined conjugate subgroup, not an
additional choice. The Lean statement expresses exactly its word/simple-root independence
and sign location using the concrete conjugate of the given additive subgroup. Equality of
these represented subgroup functors on all affine test schemes is equality as subgroup
schemes, including infinitesimal information. Projection of the paired generated subgroup
to its second factor is W, so the word formulation covers every w in W. No relation is
asserted with all adjoint weights, and no reductivity condition occurs.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled `Grp`, group homs.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`; its actual signatures and docstrings were read.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; algebraic-closure dependency's match explicitly includes this predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `...QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`, as exposed by `IsAlgebraic`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `additive`, `affine`,
  `map`, the actual group structures and polynomial/Laurent coordinate constructions.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `Cocharacter`, `normalizer`, `pointImage`, `adjointMap`, `multiplicativeValue`.
- `Sheaf.AlgebraicGeometry.TrivialTorusCoherentData`: `Character` and the public
  `multiplicativeCommMonObj` instance giving its genuine commutative pointwise group law.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `splitTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `IsStable`.
- `Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`: `unipotentPoints`,
  `centralizerPoints`; read their morphism-based extension and scalar-extension conditions.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `additiveParameterPoint`; uses `Polynomial.aeval`, not an arbitrary map.
- `Mathlib.LinearAlgebra.RootSystem.Defs`, `...Base`, `...Reduced`, `...IsValuedIn`:
  `RootPairing`, `IsRootSystem`, `Base`, `IsReduced`, `IsCrystallographic`.
- Proof import `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`:
  `MultiplicativeType.multiplicative_character_antiduality`. The other two theorem
  proof dependencies, `lem-sfb-torus-normalizer-components` and
  `lem-sfb-root-chamber-simple-transitivity`, have no recorded module yet, so no import
  can be added for them. They are not needed to state this theorem. No waiting or new
  proof claim is introduced.

Edge cases checked by reading the actual formulas before writing:

- Rank one: `otherHeight` is vacuous, but `positiveM` still permits m=1;
  eta_alpha can be zero, its monoid action is identity, and its kernel is trivial.
- D empty is excluded exactly by the source's `nonempty`. Rank-zero T cannot supply a
  nonzero independent nonempty D. Neither case is silently discarded by a type restriction.
- Additional central torus directions remain in X, while P uses only `rootSpace`.
- Nonprimitive alpha in X is allowed: independence does not assert primitive/saturated D.
  Integer coefficients and reducedness concern the D-lattice and its rational span.
- Characteristic 2 and other positive characteristics are retained. Scaling uses actual
  characters, not their differentials. The integer pairing 2 is in ℤ, not in F.
- Zero/nonreduced test algebras are included by `CommAlgCat F`; centralizers, normalizers,
  and subgroup equalities are not tested only on geometric points.
- Multiple word lifts and different simple-root presentations are explicitly quantified.
  The empty word and inverse words are included by subgroup closure.
- Scalar 0 in A1 means the additive group's identity section; scalar 1 is separately
  used for the monoid unit law. These two are distinguished in `evaluationZero` and
  `monoidExtension`.

Searches (recorded raw in the new node):

- LeanFinder, “Triangular group scheme coordinates yield signed reflection orbits,
  a reduced crystallographic root system and longest conjugation”: eight root-system
  results, no group-scheme coordinate theorem.
- Loogle, `RootPairing, GrpObj, LinearIndependent`: zero hits, unknown short `GrpObj`.
- Mathlib grep, `triangular|[Cc]ocharacter|[Uu]nipotent` in AlgebraicGeometry: zero hits.
- LeanSearch, “group scheme torus characters cocharacters contracting subgroup root system”:
  root datum/root-system construction results, no exact theorem.
- LeanFinder and LeanSearch on the triangular coordinate datum: eight results each;
  existing root pairings and Lie triangularizability, no datum of these hypotheses.
- Mathlib grep `TriangularReflection|triangular.*(datum|coordinates)|MonoidExtension|SignedReflection`:
  zero hits. Upstream WeilConjectures grep for the item id and triangular/reflection terms:
  no exact statement. Sheaf searches found the reusable component modules listed above,
  but no triangular coordinate datum or complete theorem.
- DAG grep and `tools/blueprint_refs.py search 'triangular reflection'`: no existing
  definition node for the datum; zero blueprint-node matches. Existing roots and Borel
  theorems assume reductivity or a root pairing and cannot replace this statement.

Validation: both files compile individually in dependency order through `scompile.py`.
The local wrapper encountered ENOSPC in its temporary compiler area and automatically
confirmed successfully on the server; server times were 5.7 s and 2.0 s, under the
unchanged 60 s limits. No Lean errors or unexpected warnings remain.

No statement dispute or correction was needed. No dependency module was replaced.

## New nodes

`def-sfb-triangular-reflection-data` defines exactly the triangular-coordinate hypotheses,
the pinned pairing/reflections, the additive root subgroup parametrizations, monoid extensions,
zero-evaluation retractions and kernels, and the canonical W, paired words, R and rational
root span. Its module is `Sheaf.AlgebraicGeometry.GroupScheme.TriangularReflectionData`.
Its statement spells out the full source hypotheses rather than assuming an unexplained
predicate or citing the consuming item, so no dependency cycle is introduced. It reuses the
existing character, cocharacter, torus, subgroup, stability, unipotence, limit-functor and
parameter constructions. The searches above and their raw JSON records establish that the
assembled datum is missing; this node supplies it under rule (A). Source: the supporting
triangular assertion for Milne 23.31/23.33, p.494, with the inherited explicit agent argument.
No theorem or root-system conclusion is hidden in the datum. All eight added component
nodes were checked by graph traversal not to depend on the item.

## Second reading by Q24

I reread the finished node, both modules and the source in a separate pass; no additional
agent was started, as the dispatcher explicitly prohibits it. The maintainer provides the
independent delivery review. The clause tables above record this reading's full comparison.

The second pass found that a preliminary external normalization predicate duplicated the
existing action-stability interface. It was removed. `Data.adjointAction` is now pinned to
actual conjugation by `adjointFormula`, and all four normalization fields use the existing
`TorusCharacterTangent.IsStable`. Both files were recompiled after this change. Also checked:
`reflectionAction` uses the inverse torus automorphism (the correct left action on characters),
paired word multiplication respects conjugation order, the negative lambda is obtained by
inversion of Gm, and opposite root scaling uses `-alpha` in the actual character group.

The root system lives in `span_Q(1 tensor R)`, its root embedding is pinned to the given
characters and its pairing to evaluation. The simple-root support equality and integral
signed expansions refer to the same D as in the hypotheses. Thus the root-system witness
neither assumes that roots span the full torus character space nor asserts reductivity.
The final witness is one paired word and both U/V equalities use that same representative.
The root subgroup independence quantifies over two arbitrary words and two arbitrary simple
roots. All source hypotheses, including those unused in the ten-step proof, remain in Data.
The new node is a definition with no postponed data or proofs; the consuming theorem alone
has the expected `sorry`. No further mismatch was found.
