## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.OppositeRootSL2Parametrizations`
states `AlgebraicGeometry.opposite_root_sl2_parametrizations`, with one postponed
proof and no new definitions or dependency modules. The item theorem is unchanged
from returned head acd3c07979e6; only its Borel-pair public import is restored. The
already landed `def-sfb-rank-one-root-interfaces` is added to `stmt_deps` because
it provides the natural functor-of-points SL₂ morphism and normalizer interfaces.

Source read: Milne, *Algebraic Groups* (2017), Theorem 21.11 and its proof,
printed pp.428–430, and paragraph 21.24, printed p.432, in
`literature/milne-algebraic-groups_iAG2017.pdf`. In particular 21.11(e), equation
(134), defines the canonical coroot by the actual normalizer reflection, and
21.24 gives the diagonal restriction and isomorphisms on both unipotent groups.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- Group schemes and their homomorphisms are `Grp (Over (Spec (.of F)))` and its
  morphisms, using the recorded group-scheme notion. The field and algebra
  universes are the same, as required for affine test algebras of these schemes.
- The smooth connected affine finite-type reductive group is `G` with
  `hG : ReductiveTorusCentralizer.IsReductive G`. Its definition includes affine
  finite type, smoothness, geometric connectedness, and exclusion of nontrivial
  smooth connected normal unipotent groups after algebraic closure. The reused
  `SolvableGroupStructure.IsUnipotent` itself includes smoothness and faithful
  geometric matrix unipotence. Over the algebraically closed base these are
  precisely the hypotheses in the item; no additional restriction on G is used.
- The split maximal torus is `T`, its inclusion `i`, `hT`, and `hsplit`. The latter
  says it is isomorphic to a finite product of the recorded multiplicative group.
- The lattices X and Y are the actual additive Hom groups in the two arguments
  of `P : RootDatum Φ ... ...`. Thus Y consists of scheme cocharacters, not Lie
  algebra elements. `hroot` identifies roots with the characters in Φ. `hpair`
  identifies the integer pairing with composition and the integer power map.
  `hconj` identifies the action `aG` with conjugation, and `hweights` says Φ is
  exactly the nontrivial character tangent weights. The explicit commutativity
  instances are structures inherent in the torus and Gm, as in the Borel-pair
  dependency, needed to put additive group structures on these Hom groups.
- A root is the arbitrary `α : Φ`. The data of the canonical coroot is
  `(P.coroot α).toMul`. The binder `hcanonical` states the reflection identity
  as equality of morphisms T → G: for an actual normalizer element n,
  `t / α∨(α(t)) = n⁻¹ t n`. This is the dual form of equation (134) in Milne,
  since the pairing is composition by `hpair`. The root-datum axiom already
  gives pairing 2, so the reflection is nontrivial. This spells out the node's
  word "canonical", rather than adding a further geometric hypothesis.
  An arbitrary abstract root datum with these character roots need not specify
  the geometric coroot (central cocharacter twists can preserve pairing 2);
  the actual-normalizer condition is therefore deliberately retained. A finite
  Weyl reflection with image line Qα is the α reflection, so this condition
  identifies exactly the canonical coroot, including on central torus directions.
- The given subgroups Uα and U−α are `Uplus`, `Uminus`, with inclusions
  `jplus`, `jminus`. The five conjuncts of `hplus` and `hminus` are respectively
  closed subgroup, smooth, connected, T-normalized, and having tangent space
  equal to the corresponding character weight space. These are exactly the
  defining properties of the unique root subgroup in the recorded dependency.
  The negative root is the inverse character `(-α.val).toMul`.
- The required group-scheme homomorphism is `v : RankOneRoots.SL2Hom G`. Its
  fields are homomorphisms on the actual determinant-one matrices over every
  `A : CommAlgCat.{u} F`, natural with respect to every F-algebra homomorphism.
  This is the affine functor-of-points meaning of a scheme homomorphism; there
  is no arbitrary point map and no field-only test condition.
- The two restrictions are the group-scheme isomorphisms `eplus` and `eminus`
  from the recorded additive group to the two given root subgroups. The first
  and second conclusion conjuncts identify `v.app A` on `!![1,a;0,1]` and
  `!![1,0;a,1]` with the specified isomorphism followed by its subgroup inclusion.
  `additiveParameterPoint F a` is the recorded polynomial-coordinate point.
- The last conjunct sends `diag(s,s⁻¹)` to
  `s ≫ (P.coroot α).toMul.hom.hom ≫ i.hom.hom`. Here s is a point of the
  actual Laurent-spectrum multiplicative group and `multiplicativeValue`
  evaluates its Laurent coordinate. Such points are exactly A×, including
  nilpotent test algebras. Coordinate evaluation of `s⁻¹` gives the inverse unit.
- In each formula the determinant-one matrix is universally quantified with
  its matrix entries specified by an implication. This avoids inserting a
  proof of determinant one in a statement. The three displayed matrices always
  have determinant one and hence always supply such an element; the implications
  do not discard any parameter or impose an additional condition.
- There is no `CharZero`, inverted prime, reducedness, or field condition on A.
  In particular the theorem includes characteristic two and arbitrary rings A.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group-object morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive`,
  `multiplicative`, their recorded group instances.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`, the unchanged landed Q131
  Borel-pair declaration, supplies the character/cocharacter and pairing interface.
  Its record also retains `AlgebraicGeometry.semisimpleGroupScheme_isReductive`.
  The item takes `hcanonical` explicitly as a hypothesis: it does not require a
  stronger Borel-pair conclusion to state the desired rank-one parametrization.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `TorusCharacterTangent.reductive_root_subgroup_parametrizations` and
  `TorusCharacterTangent.additiveParameterPoint`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`;
  `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `TorusCharacterTangent.weightSpace`, `IsStable`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.adjointMap`, `normalizer`, `SL2Hom`, `multiplicativeValue`.
- Proof-only import `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`:
  `RankOneRoots.reductive_rankOne_reflections`. The other proof nodes
  `lem-sfb-split-rank-one-classification` and `lem-sfb-projective-frames-pgl`
  have no recorded Lean declarations at this reading, so have no modules to import.

Edge cases checked before writing: if Φ is empty there is no α, so the statement
is vacuous, including for a torus or the trivial reductive group. Positive
characteristic, especially characteristic two, does not identify opposite
characters in their integral lattice. In characteristic two the sign change on
Ga remains an isomorphism. Nonreduced A and the zero F-algebra are included.
The SL₂ map need not be an isomorphism or an immersion: in the PGL₂ case its
central kernel μ₂ can be nonreduced. Only the two root restrictions must be
isomorphisms. The diagonal is an actual cocharacter identity, not an identity of
differentials. The two chosen root subgroups may be any representatives of their
unique closed subgroup schemes; the returned isomorphisms respect their inclusions.

Searches executed:

- `msearch.py ... leanfinder` with query "A reductive group has compatible opposite
  root subgroup parametrizations by SL2 with diagonal equal to the coroot": eight
  results, including `IsSl2Triple.h_eq_coroot` and abstract root-pairing results;
  none states the algebraic group-scheme result in arbitrary characteristic.
- `msearch.py ... loogle` with query `"SpecialLinearGroup", "root"`: twelve
  results concerning matrix centers and projective special linear groups, none
  the required root-subgroup theorem.
- `msearch.py ... grep` with query `SL2Hom|opposite.*root|root.*parametr`: no hits
  in Mathlib. Direct `rg` in `lean/WeilConjectures` gives no matching interface
  or theorem, and the exact blueprint-id grep there has no hits.
- Direct `rg` in `lean/Sheaf` finds the recorded root-subgroup and rank-one
  interfaces and many uses in proof docstrings, but no theorem asserting both
  root restrictions and the prescribed diagonal. Reused the existing SL₂
  interface instead of constructing another SL₂ notion. Checked the proposed
  declaration name against Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`; no collision.

No statement correction, new node, or dependency module is needed. The source
statement is consistent and no STATEMENT-DISPUTED flag is raised.

Validation: the repaired single module compiled cleanly through `scompile.py`
(28.2 seconds sandbox, 4.0 seconds library). The repaired delivery is also
checked through `deliver2.py --no-push` before `deliver2.py`. All variables and the
universe remain explicitly bound, and `autoImplicit` is disabled. The only
postponed theorem delivered is `AlgebraicGeometry.opposite_root_sl2_parametrizations`.

## Second reading by Q36

This is a single-worker consistency reading after the maintainer's independent
review of immutable head acd3c07979e6. The reviewer accepted the item clause by
clause, including `hcanonical`, both isomorphisms Ga ≅ U±, the diagonal identity,
and the empty-root, characteristic-two, nonreduced-algebra and universe cases.

Compared the final signature and proof body against the retained returned
version: they are byte-identical. The only source change to the item module is
its public import of the original `ReductiveBorelPairStructure`. Rechecked the
three conclusions: one `v` appears in all of them; the two restrictions go
through isomorphisms to the given root subgroups; and the last uses the actual
cocharacter `(P.coroot α).toMul` over every test algebra. `hcanonical` remains
an explicit hypothesis specifying the geometric coroot. The accepted item needs
no strengthened conclusion from the Borel-pair dependency.

## Repair of return H13 (+H4)

Return reviewed: L's independent stage-2 review of immutable head acd3c07979e6,
recorded in `coord/returns/Q36.md`, 2026-10-24 11:23 UTC.

1. Restored the sandbox copy of
   `lem-sfb-reductive-borel-pair-structure.json` byte-for-byte from the live
   read clone. Its Q131 Lean record remains unchanged, including both
   `AlgebraicGeometry.reductive_borel_pair_structure` and
   `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. No dependency record
   change is part of this delivery.
2. Removed `CanonicalReductiveBorelPairStructure.lean` from the sandbox.
   Its repeated Borel-pair statement and extra normalizer conjunct are no
   longer delivered. The earlier claim that the landed interface was unusable
   was incorrect: it faithfully states its node, and the accepted item already
   takes `hcanonical` as a hypothesis.
3. Restored the item's public import to
   `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`.
   The item theorem, its hypotheses, three conclusions, and sorry proof are
   unchanged. Its node's `lean.statement` is still the exact source signature.
4. Removed the rejected dependency-repair discussion and declaration from this
   report. No geometric-coroot theorem is attached to the Borel-pair node, and
   no statement correction or new statement node is introduced by this repair.
