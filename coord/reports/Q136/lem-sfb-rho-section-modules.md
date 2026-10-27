## Worker report

The delivery states `AlgebraicGeometry.exists_rho_section_modules` in
`Sheaf.AlgebraicGeometry.RhoSectionModules`. Its only theorem has proof `by sorry`.
The new module `Sheaf.AlgebraicGeometry.RhoSectionModuleData` constructs the actual
semi-invariant subspace and specifies its rational left action. All definitions have
real data, and all variables and universes are explicit (`autoImplicit false`).
No statement correction or disputed mathematical claim was needed.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The group is `S : Grp (Over (Spec (.of F)))`, the bundled version of the
  recorded `GrpObj` group scheme. No characteristic hypothesis is imposed.
- Semisimplicity is `hS : IsSemisimpleGroupScheme S.X`. The existing predicate
  spells out smoothness, connectedness, affineness, finite type, and triviality
  of every smooth connected solvable normal closed subgroup. Its solvability
  uses termination of the scheme-theoretic commutator series.
- Simple connectedness is `hsc`, quantified over every semisimple `S'` and every
  group-scheme homomorphism `f : S' ⟶ S.X`. Its antecedents are `Surjective f.left`,
  `IsFinite (GrpObj.ker f).hom`, and the explicit commuting equation between
  every algebra-valued kernel point and every algebra-valued source point.
  Its conclusion is `IsIso f`. For this affine finite-type kernel, scheme
  finiteness is exactly finite dimension of its coordinate algebra.
- `IsRhoBorelPair i j k` uses the existing maximal-torus predicate, an isomorphism
  to `MultiplicativeType.splitTorus F r` for some natural `r`, the existing
  `IsBorelGroupScheme`, and `k ≫ j = i`. Rank zero is included. The first
  conjunct of the theorem asserts existence of this pair; the second quantifies
  over every such pair, with all three inclusion maps retained.
- The existential `a : ModObj T.X B.X` has its morphism characterized by
  `lift t b ≫ a.smul = (t ≫ k.hom.hom) * b * (t ≫ k.hom.hom)⁻¹` on every test
  scheme. Thus its induced tangent action is the actual conjugation action.
  It is not an arbitrary action or an added hypothesis.
- The positive roots are the duplicate-free list `Φ` with membership exactly
  `α.hom.hom ≠ 1 ∧ TorusCharacterTangent.weightSpace T B α ≠ ⊥`, using that
  conjugation action. The recorded weight-space definition evaluates the actual
  character at constant points of the torus on actual dual-number tangent
  vectors of `GrpObj.Lie B.X`. Since the split torus is smooth over an
  algebraically closed field, its F-points are dense, so this character-space
  condition is equivalent to the scheme-theoretic weight condition. It does
  not differentiate characters, which would lose information in characteristic p.
- Both `ρ` and `ρB` are homomorphisms to the recorded multiplicative group.
  The equation `ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod` is exactly
  twice rho equals the sum of all positive roots, in multiplicative notation.
  Characters of a split torus form a torsion-free lattice; this specifies the
  integral half-sum uniquely. Listing the finite set introduces no ordering
  dependence because G_m is commutative. A list product avoids requiring a
  separately synthesized commutative-group instance on this definitional G_m.
- `k ≫ ρB = ρ` is the extension condition. The following universal clause says
  every smooth connected normal closed unipotent subgroup of B is killed by
  `ρB`. This is equivalent to killing the largest one, its unipotent radical:
  all such subgroups lie in the radical, and the radical itself is among them.
  `SolvableGroupStructure.IsUnipotent` uses a faithful matrix representation
  with unipotent points over every algebraically closed extension field and
  includes smoothness. No extra assumption on a radical has been introduced.
- Positive integers are quantified by `(m : ℕ), 0 < m`, equivalently the
  integers m >= 1 in the node. `RhoSection.sectionModule S B j ρB m` is the
  intersection of kernels of the exact linear equations
  `evaluate (g * (b ≫ j.hom.hom)) f = characterValue (b ≫ ρB.hom.hom)^m * evaluate g f`
  for every commutative F-algebra A, every g, and every b. Thus it is the
  actual specified subspace of F[S], not a merely isomorphic representation.
- The final three conclusions are `W ≠ ⊥`, `Module.Finite F W`, and
  `HasRationalLeftTranslation S W`. The last gives a linear basis isomorphism
  from F^I onto this W and a group-scheme homomorphism to GL_I; its matrix
  columns, tested on every algebra A and s,g in S(A), evaluate to f_j(s⁻¹g).
  This is precisely the finite-dimensional rational action on the actual W.
  A group-scheme map to GL is equivalent to the coaction in the node: its
  regular coordinate matrix entries define W → W tensor F[S], and the
  multiplication and identity diagrams give coassociativity and the counit.
  Its all-algebra normalization determines the action, including on scalar
  extensions of every linear combination of basis elements. Invariants and
  diagonal tensor actions in the node are conventions for downstream use,
  not an additional assertion in this lemma.

Dependency declarations read and used:

- Mathlib `Field` (Algebra.Field.Defs), `IsAlgClosed` (FieldTheory.IsAlgClosed.Basic),
  `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`, `GrpObj.ker`, `GrpObj.kerι`.
  The source module `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents
  the specialization to `Over (Spec F)` and finite kernels.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `IsSemisimpleGroupScheme`, `IsSolvableGroupScheme`, and their derived-series data.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus` and `MultiplicativeType.IsTorus`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsUnipotent`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `TorusCharacterTangent.weightSpace`, using `GrpObj.Lie` and `tangentPoint`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine` and `multiplicative`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`:
  `GeneralLinearGroup.RationalHom` and `GeneralLinearGroup.homMulEquiv`.
  These are genuine group-scheme representations in every characteristic.
- Mathlib AlgebraicGeometry.Group.Affine: `algΓ`, `algSpec.fullyFaithful`,
  `algΓAlgSpecAdjunction`. Evaluation is obtained from its canonical unit and
  inverse on morphisms; it is pullback of global functions at the given point.
  The resulting `Coordinate G` has carrier Γ(G, O_G) and its structural F-algebra.
- The stated proof dependency `lem-pc-coherent-hi` is imported, without public
  exposure, through its recorded module
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
  Its `finite_sections_higherDirectImage` gives exactly the proper-over-affine
  finite-module input. The four representation-theoretic proof dependencies
  have no recorded Lean modules and therefore cannot yet contribute imports.
  Their proof steps are all preserved in the theorem docstring.

Existing landed definition nodes were added to stmt_deps to cite their actual
interfaces: semisimple-group-scheme, borel-subgroup-scheme, tori-multiplicative-type,
solvable-group-structure, reductive-torus-centralizer-terminology, and
 torus-character-tangent-weights (all with prefix `def-sfb-`). The item's prose,
proof, proof_deps and other fields are unchanged. `IsRhoBorelPair` is the local
owning-node helper packaging precisely the pair already introduced in the item;
it is public and included in lean.declarations.

Edge cases checked mathematically: S=1 permits rank zero, the empty root list,
rho=1 multiplicatively, and W_m=F with trivial action. For SL2 with upper triangular
B and rho=diag(t,t⁻¹)↦t, W_1 contains the first-column entries g11,g21;
this checks the positive exponent and left inverse convention. In characteristic 2,
the equality of character squares still determines rho; it is not multiplication
by zero in F. No nonreduced test algebra is excluded. The auxiliary section-module
definition also covers m=0 and the rational-action predicate covers W=0 via the
empty basis. The main theorem correctly only claims nonzero W for positive m.
All test algebras have the field/scheme universe u, the standard nonvacuous
scheme-points convention, sufficient to test their functorial equalities.

Searches: msearch LeanFinder queried the Borel-pair/rho theorem (8 unrelated Lie
weight and finite-group character hits). Loogle queried IsSemisimpleGroupScheme,
GrpObj, Borel, Comodule (no match / unknown project identifier), and LinearMap.ker,
GeneralLinearGroup.RationalHom, GrpObj (no match). LeanSearch queried semi-invariant
regular functions on an affine algebraic group (8 abstract representation/invariant
hits, none this notion). LeanFinder queried the defining semi-invariant subspace
(8 finite abstract-group regular-representation and unrelated hits).
msearch grep `Borel|rhoSection|IsSplitTorus|Comodule` under AlgebraicGeometry and
`semi.?invariant|sectionModule|rational.*translation` globally both gave zero hits.
Direct rg in the upstream group-scheme files and Sheaf files found the existing
notions listed above but no actual section-module interface. The item id does not
occur in upstream WeilConjectures. The upstream name index has no RhoSection
match. DAG text search and `blueprint_refs.py search "rho section"` found no
existing definition node for the new subspace/action interface.

Validation: scompile.py compiled both delivered modules separately, including the
private dependency overlay and their real library paths, with no warnings or
errors. Only the main theorem is postponed. No global/local lake build was run.

## New nodes

`def-sfb-rho-section-module-data` supplies `Coordinate`, its canonical evaluation,
`characterValue`, `sectionModule`, and `HasRationalLeftTranslation` in its own
module. Source: Milne Definition 12.1, Section 18c and Definition 22.21, with
Alper Section 9.7 for the sign convention. It reuses Mathlib's algebraic Gamma/Spec
adjunction and upstream RationalHom, rather than defining another rational
representation notion. Its genuinely missing definitions are the actual
semi-invariant subspace and the predicate normalizing that representation to
left translation on this exact subspace. Searches and their raw outputs are
recorded in mathlib_searches. The existing homogeneous-line-bundle theorem and
rho-section node describe these in prose but have no Lean definitions to reuse.

The source and blueprint lineage are inherited from the item, whose ancestor is
null as confirmed by blueprint_refs.py ancestor; the via chain starts with the item.
No theorem, choice of representation, or unspecified coordinate data is hidden
in these definitions.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
