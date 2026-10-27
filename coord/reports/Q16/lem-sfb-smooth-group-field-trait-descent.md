## Worker report

The sole module, `Sheaf.AlgebraicGeometry.SmoothGroupFieldTraitDescent`, states
`AlgebraicGeometry.exists_smooth_group_field_trait_descent`. Its sole theorem proof is
`sorry`. There are no definitions, auxiliary postponed theorems, new nodes, dependency
repairs or statement changes. The item JSON changes only `lean`.

Source checked: Bosch--Lütkebohmert--Raynaud, Néron Models, 6.5 Theorem 1,
printed p.157 (PDF page index 163), at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The online text at lines 5486--5493 states effective descent of both the group and its
torsor over faithfully flat field/DVR extensions, and all three descended properties.
Taking the torsor to be the group itself gives exactly this node. The module docstring
includes all five steps and all proof inputs of the accepted node.

Hypotheses and clauses, matched individually:

- The commutative rings are `B C : Type u` with `[CommRing B] [CommRing C]`.
  Both fields and DVRs are integral domains; `[IsDomain B] [IsDomain C]` expose this
  common consequence so that the DVR propositions are well typed. They restrict neither case.
- The given map is `φ : B →+* C`; faithful flatness is `hφ : φ.FaithfullyFlat`.
  This uses the existing ring-map definition, with the algebra structure induced by φ.
- The two permitted cases are exactly `hbase : (IsField B ∧ IsField C) ∨
  (IsDiscreteValuationRing B ∧ IsDiscreteValuationRing C)`. `IsField` avoids adding field
  operations to the commutative-ring structure: `IsField.toField` supplies the equivalent
  `Field` when needed. Neither finite extension nor separability is required.
- S and S' are `Spec (.of B)` and `Spec (.of C)`; p is
  `Spec.map (CommRingCat.ofHom φ)`. Their common universe is the standard scheme-library
  universe; rings and schemes of different initial sizes can be lifted into their maximum.
- The S'-group scheme is `G' : Grp (Over (Spec (.of C)))`. Its existing `GrpObj G'.X`
  includes multiplication, identity, inverse and their diagrams. It need not be commutative.
- Smoothness is `[Smooth G'.X.hom]`.
- Separatedness is `[IsSeparated G'.X.hom]`, whose defining clause is
  `IsClosedImmersion (pullback.diagonal G'.X.hom)`, exactly the node's diagonal condition.
- Finite type is `[LocallyOfFiniteType G'.X.hom] [QuasiCompact G'.X.hom]`, as the recorded
  finite-type dependency requires.
- The datum is `D : Over.DescentDatum p G'.X`, the dependency's actual transport interface.
  It includes naturality, transport along the diagonal, and the cocycle law; reversing a
  transport is its inverse. Its module explains its Yoneda equivalence with an overlap iso.
- The overlap iso being a group iso is `hmul`: for every test scheme T and pair of maps
  f₁,f₂ with the same composite to S, transport preserves multiplication on group-valued
  T-points. The scoped operations are the existing `Hom.group` from `GrpObj`.
  This condition also preserves identity and inverse: the image of identity is idempotent
  in a group, hence identity, and multiplicativity then preserves inverses. Transport is
  already bijective by the datum axioms. Thus no group-compatibility clause is dropped.
- The descended group is `∃ G : Grp (Over (Spec (.of B)))`.
- Its smoothness, separatedness and finite type are the four conjuncts
  `Smooth G.X.hom ∧ IsSeparated G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`.
- The S'-group iso is
  `e : (Over.pullback p).mapGrp.obj G ≅ G'`. The existing pullback functor preserves finite
  products; `mapGrp` is the existing induced functor on group objects. The iso therefore
  preserves the entire group structure, not just underlying schemes.
- Realizing the given datum is the final universally quantified equation. Writing
  q for `e.inv.hom.hom.left ≫ pullback.fst G.X.hom p`, it reads
  `(D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q`.
  This is exactly the invariance clause of `Over.DescentDatum.IsEffective`; e also supplies
  its pullback square. By the pullback universal property, the transported point is the
  unique point over f₂ having the same q-image. Hence this equation identifies D with the
  canonical datum and does not merely assert unrelated effectivity.
- There is no hypothesis imposing affineness, projectivity, properness, connectedness,
  geometric connectedness, completeness, henselianity, characteristic, finite field
  extension degree or a ramification condition.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and `RingHom.FaithfullyFlat` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` (the latter is used in the signature).
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`; equivalent propositional
  interface `IsField`, `Mathlib.Algebra.Field.IsField`, including `IsField.toField`.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, a local PID domain with nonzero
  maximal ideal, so the field and DVR alternatives are genuinely distinguished.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sc-group-scheme`: `CategoryTheory.Grp` and `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; the Hom groups are in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`. The general existing group-object API
  applies to Over S for both kinds of S; no private generalization is needed.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, used through `IsSeparated`.
- `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum` and `.IsEffective`,
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`.
- `def-pc-base-change`: imported its recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; that record explicitly
  directs scheme base change to `CategoryTheory.Over.pullback` and `Limits.pullback`,
  used here. Its module-base-change declaration is not applicable to this statement.

The statement-dependency modules are public imports. The already stated proof-dependency
modules are plain imports: affine morphisms, local flat descent, fpqc covers, DVR dimension,
faithfully-flat spectrum surjectivity, valuation-ring normality, fpqc morphism descent,
and fpqc descent of separatedness, local finite type, quasi-compactness. The proof inputs
`lem-sfb-finite-type-group-ample-line`, `lem-sfb-field-ample-scheme-datum-effectivity`,
`lem-sfb-trait-generic-effective-dense-affine`, `lem-sfb-trait-horizontal-boundary-datum`,
`lem-sfb-smooth-group-relative-neutral-open`, `lem-sfb-dedekind-action-boundary-ampleness`,
and `lem-sfb-polarized-affine-fpqc-effectivity` have no recorded Lean or Mathlib statement
in the read repository, so no imports can yet name them. Their precise roles are retained
in the theorem's proof docstring.

Edge cases checked before writing:

- Identity ring map and canonical datum: take G=G' with the canonical base-change iso.
- Trivial group schemes and dimension-zero groups are allowed.
- Nonconnected and noncommutative smooth groups are allowed.
- Positive characteristic and purely inseparable field extensions are allowed.
- Infinite field extensions, ramified DVR extensions and noncomplete DVRs are allowed.
- Abelian varieties give nonaffine examples; G_m gives nonproper examples. Both are covered.
- The zero ring is excluded by the field/DVR alternatives, as the source requires.
- An empty group scheme over either nonempty base cannot have an identity section; its
  exclusion follows from `GrpObj`, not an extra nonemptiness assumption.
- Test schemes T include the empty scheme; both Hom groups then have their usual unique point.
- Merely being an effective underlying scheme would be insufficient: the actual group iso
  and the original transport invariance are both included in the conclusion.

Searches for an exact existing statement (all prescribed msearch calls use group Q16 and
this item, and are recorded by the wrapper in searches.jsonl):

- LeanFinder: "Effective descent of smooth separated finite type group schemes over
  faithfully flat extensions of fields or discrete valuation rings". Eight hits, mainly
  `Algebra.Smooth.exists_finiteType`, smooth morphism properties and flatness; no effective
  descent theorem for possibly nonaffine group schemes.
- Loogle: `"GrpObj", "DescentDatum"`. Zero hits.
- Mathlib grep via msearch: `group.*scheme.*descent|descent.*group.*scheme`. Zero hits.
- LeanSearch: "Effective descent of smooth separated finite type group schemes over fields
  or discrete valuation rings". Eight hits: smooth algebra approximation and morphism
  property descent, with no matching effective group descent.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: searched group/descent combinations,
  transport/multiplication, and this node id. Inspected the existing
  `EffectiveDescent/Group.lean`, `EffectiveDescent/Basic.lean`, and the retired companion
  `Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/EffectiveDescent.lean`.
  These concern group operations on an already descended underlying scheme or other,
  restricted effectivity inputs. They do not supply field/DVR group-scheme effectivity.
- rg in both source trees and `dag/lean_names_upstream.json` for the proposed declaration
  and smooth-group field/trait descent names found no exact declaration or collision.

Validation: scompile.py compiled this single file separately in sandbox and library modes
against the published server library, with no error or warning (17.7 s and 2.0 s).

## Second reading by Q16

I reopened the item and module for a second pass, checking the field/DVR disjunction,
all four geometric-property predicates, both group-object structures, and the variance
of e and its projection. In particular e goes from the base change to G', so e.inv is
used before pullback.fst in the datum-invariance equation. The universal T-points make
both the group compatibility and the datum identification scheme-theoretic. No mismatch
or statement correction was found. This is a worker self-audit: the dispatch instructions
prohibit starting other agents, and independent review is performed by the maintainer.
